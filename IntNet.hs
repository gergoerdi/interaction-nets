{-# LANGUAGE RecordWildCards, Rank2Types #-}
module IntNet where

import Lam
import Data.STRef
import Control.Monad.ST
import Data.Array.ST
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Monad ((<=<), unless)
import Data.IntMap.Strict ((!))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.List
import Data.Ord
import Data.Function (fix)

data NodeType = IRot
              | ILam
              | IApp
              | IDup Int
              | IEra
             deriving (Show)

data PortNum = P0
             | P1
             | P2
             deriving (Show, Eq, Enum, Bounded)

type NodeID = Int -- TODO

data Node s = Node{ nodeType :: !NodeType
                  , nodeID :: !NodeID
                  , nodePort0, nodePort1, nodePort2 :: !(Port s)
                  }

data NodeTag = TEra
             | TLamApp
             | TDup Int
             deriving (Show, Eq)

nodeTag :: Node s -> Maybe NodeTag
nodeTag Node{..} = case nodeType of
    IRot -> Nothing
    ILam -> Just TLamApp
    IApp -> Just TLamApp
    IDup tag -> Just $ TDup tag
    IEra -> Just TEra

type Port s = STRef s (NodeAddr, PortNum)
type NodeAddr = Int

type Heap s = STArray s NodeAddr (Node s)
data R s = R{ heap :: Heap s
            , garbage :: STRef s [NodeAddr]
            , nextAddr :: STRef s NodeAddr
            , nextID :: STRef s NodeID
            }

type OptLam s = ReaderT (R s) (ST s)

alloc :: OptLam s NodeAddr
alloc = do
    gref <- asks garbage
    garbage <- lift $ readSTRef gref
    case garbage of
        addr:garbage -> do
            lift $ writeSTRef gref garbage
            return addr
        [] -> do
            aref <- asks nextAddr
            addr <- lift $ readSTRef aref
            lift $ writeSTRef aref (succ addr)
            return addr

free :: [NodeAddr] -> OptLam s ()
free addrs = do
    gref <- asks garbage
    lift $ modifySTRef gref (addrs ++)

freshID :: OptLam s NodeID
freshID = do
    ref <- asks nextID
    id <- lift $ readSTRef ref
    lift $ writeSTRef ref (succ id)
    return id

mkPort :: OptLam s (Port s)
mkPort = lift $ newSTRef (0, P0)

mkNode :: NodeType -> OptLam s NodeAddr
mkNode nodeType = do
    addr <- alloc
    heap <- asks heap
    nodeID <- freshID
    nodePort0 <- mkPort
    nodePort1 <- mkPort
    nodePort2 <- mkPort
    let node = Node{..}
    lift $ writeArray heap addr node
    return addr

readNode :: NodeAddr -> OptLam s (Node s)
readNode addr = do
    heap <- asks heap
    lift $ readArray heap addr

getPort :: NodeAddr -> PortNum -> OptLam s (Port s)
getPort addr pnum = do
    Node{..} <- readNode addr
    return $ case pnum of
        P0 -> nodePort0
        P1 -> nodePort1
        P2 -> nodePort2

readPort :: NodeAddr -> PortNum -> OptLam s (NodeAddr, PortNum)
readPort addr pnum = lift . readSTRef =<< getPort addr pnum

readID :: NodeAddr -> OptLam s NodeID
readID addr = nodeID <$> readNode addr

linkHalf :: NodeAddr -> PortNum -> (NodeAddr, PortNum) -> OptLam s ()
linkHalf addr pnum to = do
    from <- getPort addr pnum
    lift $ writeSTRef from to

link :: (NodeAddr, PortNum) -> (NodeAddr, PortNum) -> OptLam s ()
link a b = do
    uncurry linkHalf a b
    uncurry linkHalf b a

annihilate :: NodeAddr -> NodeAddr -> OptLam s ()
annihilate a b = do
    a1 <- readPort a P1
    b1 <- readPort b P1
    link a1 b1
    a2 <- readPort a P2
    b2 <- readPort b P2
    link a2 b2
    free [b, a]

commute :: NodeAddr -> NodeAddr -> OptLam s ()
commute a b = do
    a2 <- mkNode . nodeType =<< readNode a
    b2 <- mkNode . nodeType =<< readNode b
    link (b, P0) =<< readPort a P1
    link (a, P0) =<< readPort b P1
    link (b, P1) (a, P1)
    link (b2, P0) =<< readPort a P2
    link (a2, P0) =<< readPort b P2
    link (a, P2) (b2, P1)
    link (b, P2) (a2, P1)
    link (b2, P2) (a2, P2)

erase :: NodeAddr -> NodeAddr -> OptLam s ()
erase a b = do
    e2 <- mkNode IEra
    link (a, P0) =<< readPort b P1
    link (e2, P0) =<< readPort b P2
    free [b]

encodeLam :: Lam -> OptLam s NodeAddr
encodeLam lam = do
    root <- mkNode IRot
    nextTag <- do
        ref <- lift $ newSTRef 0
        return $ lift $ do
            modifySTRef ref succ
            readSTRef ref

    let go scope up (Lam body) = do
            del <- mkNode IEra
            lam <- mkNode ILam
            linkHalf lam P0 up
            link (lam, P1) (del, P0)
            link (del, P1) (del, P2)
            bod <- go (lam:scope) (lam, P2) body
            linkHalf lam P2 bod
            return (lam, P0)
        go scope up (App f e) = do
            app <- mkNode IApp
            linkHalf app P2 up
            linkHalf app P0 =<< go scope (app, P0) f
            linkHalf app P1 =<< go scope (app, P1) e
            return (app, P2)
        go scope up (Var v) = do
            let lam = scope !! v
            (target, targetPort) <- readPort lam P1
            targetType <- nodeType <$> readNode target
            case targetType of
                IEra -> do
                    linkHalf lam P1 up
                    return (lam, P1)
                _ -> do
                    dup <- mkNode . IDup =<< nextTag
                    linkHalf dup P0 (lam, P1)
                    linkHalf dup P1 up
                    link (dup, P2) =<< readPort lam P1
                    linkHalf lam P1 (dup, P0)
                    return (dup, P1)
    enc <- go [] (root, P0) lam
    linkHalf root P0 enc
    return root

reduceNet :: NodeAddr -> OptLam s NodeAddr
reduceNet net = do
    (pushVisit, popVisit) <- do
        ref <- lift $ newSTRef [(net, P0)]
        let push next = lift $ modifySTRef ref $ \vs -> (next, P1):(next, P2):vs
            pop act = do
                vs <- lift $ readSTRef ref
                case vs of
                    [] -> return ()
                    (addr, port):vs -> do
                        lift $ writeSTRef ref vs
                        act addr port
        return (push, pop)

    solid <- lift $ newSTRef mempty

    (setExitPort, getExitPort) <- do
        ref <- lift $ newSTRef mempty
        let set id port = do
                lift $ modifySTRef ref $ IntMap.insert id port
            get addr = do
                id <- nodeID <$> readNode addr
                lift $ (! id) <$> readSTRef ref
        return (set, get)

    let processNode addr port = do
            (next, nextPort) <- readPort addr port
            processNext next nextPort
        processNext next nextPort = do
            (prev, prevPort) <- readPort next nextPort
            nextID <- nodeID <$> readNode next
            nextSolid <- lift $ (nextID `IntSet.member`) <$> readSTRef solid
            unless nextSolid $ case nextPort of
                P0 -> do
                    prevTag <- nodeTag <$> readNode prev
                    nextTag <- nodeTag <$> readNode next
                    case (prevPort, prevTag, nextTag) of
                        (P0, Just prevTag, Just nextTag) -> do
                            port <- getExitPort prev
                            (exit, exitPort) <- readPort prev port
                            case nextTag of
                                TEra -> erase next prev
                                _ | prevTag == nextTag -> annihilate prev next
                                  | otherwise -> commute prev next
                            (next, nextPort) <- readPort exit exitPort
                            processNext next nextPort
                        _ -> do
                            lift $ modifySTRef solid $ IntSet.insert nextID
                            pushVisit next
                _ -> do
                    setExitPort nextID nextPort
                    (next, nextPort) <- readPort next P0
                    processNext next nextPort
    fix $ \loop -> popVisit $ \addr port -> do
                processNode addr port
                loop
    return net

decodeLam :: NodeAddr -> OptLam s Lam
decodeLam root = do
    nodeDepths <- lift $ newSTRef mempty
    let go depth exit (addr, port) = do
            Node{..} <- readNode addr
            lift $ modifySTRef nodeDepths $
              IntMap.insertWith (\ _new -> id) nodeID depth
            case nodeType of
                IDup _ -> do
                    let (port', exit') = case port of
                            P0 -> (head exit, tail exit)
                            _ -> (P0, port:exit)
                    go depth exit' =<< readPort addr port'
                ILam -> case port of
                    P1 -> do
                        depth' <- lift $ (! nodeID) <$> readSTRef nodeDepths
                        return $ Var (depth - depth' - 1)
                    _ -> Lam <$> (go (succ depth) exit =<< readPort addr P2)
                IApp -> do
                    f <- go depth exit =<< readPort addr P0
                    e <- go depth exit =<< readPort addr P1
                    return $ App f e
    go 0 [] =<< readPort root P0

runOptLam :: Int -> (forall s. OptLam s a) -> a
runOptLam memoryLimit act = runST $ do
    heap <- newArray_ (0, memoryLimit)
    garbage <- newSTRef []
    nextAddr <- newSTRef 0
    nextID <- newSTRef 1
    runReaderT act R{..}

test = putStrLn $ runOptLam 100 $ do
    node <- encodeLam term
    node <- reduceNet node
    -- s <- pprNode =<< readNode 0
    -- return s
    show <$> decodeLam node
    -- showAll node
  where
    term = App id const
      where
        id = Lam $ Var 0
        const = Lam $ Lam $ Var 1

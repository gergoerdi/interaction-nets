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
import Data.List
import Data.Ord

import Debug.Trace

data NodeType = IRot
              | ILam
              | IApp
              | IDup
              | IEra
             deriving (Show, Eq, Enum, Bounded)

-- data NodeTag = TODOTag
type NodeTag = Int -- XXX

data PortNum = P0
             | P1
             | P2
             deriving (Show, Eq, Enum, Bounded)

type NodeID = Int -- TODO

data Node s = Node{ nodeType :: !NodeType
                  , nodeTag :: !NodeTag
                  , nodeID :: !NodeID
                  , nodePort0, nodePort1, nodePort2 :: Port s
                  }

type Port s = STRef s (NodeAddr, PortNum)
type NodeAddr = Int

type Heap s = STArray s NodeAddr (Node s)
data R s = R{ heap :: Heap s
            , garbage :: STRef s [NodeAddr]
            , nextAddr :: STRef s NodeAddr
            , nextID :: STRef s NodeID
            }

type OptLam s = ReaderT (R s) (ST s)

pprNode :: Node s -> OptLam s String
pprNode Node{..} = do
    target0 <- lift $ readSTRef nodePort0
    target1 <- lift $ readSTRef nodePort1
    target2 <- lift $ readSTRef nodePort2
    return $ unlines [ unwords ["Type:", show nodeType]
                     , unwords ["ID:", show nodeID]
                     , unwords ["Tag:", show nodeTag]
                     , unwords ["P0:", show target0]
                     , unwords ["P1:", show target1]
                     , unwords ["P2:", show target2]
                     ]

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

mkNode :: NodeType -> NodeTag -> OptLam s NodeAddr
mkNode nodeType nodeTag = do
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

annihiliate :: NodeAddr -> NodeAddr -> OptLam s ()
annihiliate a b = do
    a1 <- readPort a P1
    b1 <- readPort b P1
    a2 <- readPort a P2
    b2 <- readPort b P2
    link a1 b1
    link a2 b2
    free [a, b]

commute :: NodeAddr -> NodeAddr -> OptLam s ()
commute a b = do
    a2 <- do
        Node{..} <- readNode a
        mkNode nodeType nodeTag
    b2 <- do
        Node{..} <- readNode b
        mkNode nodeType nodeTag
    link (a, P0) =<< readPort b P1
    link (a, P2) (b2, P1)
    link (a2, P0) =<< readPort b P2

    link (b, P0) =<< readPort a P1
    link (b, P1) (a, P1)
    link (b2, P0) =<< readPort a P2

    link (b, P2) (a2, P1)
    link (b2, P2) (a2, P2)

erase :: NodeAddr -> NodeAddr -> OptLam s ()
erase a b = do
    e2 <- mkNode IEra (-1)
    link (a, P0) =<< readPort b P1
    link (e2, P0) =<< readPort b P2
    free [b]

encodeLam :: Lam -> OptLam s NodeAddr
encodeLam lam = do
    root <- mkNode IRot (-2)
    nextTag <- lift $ newSTRef 1

    let go scope up (Lam body) = do
            del <- mkNode IEra (-1)
            lam <- mkNode ILam 0
            linkHalf lam P0 up
            link (lam, P1) (del, P0)
            link (del, P1) (del, P2)
            bod <- go (lam:scope) (lam, P2) body
            linkHalf lam P2 bod
            return (lam, P0)
        go scope up (App f e) = do
            app <- mkNode IApp 0
            linkHalf app P2 up
            linkHalf app P0 =<< go scope (app, P0) f
            linkHalf app P1 =<< go scope (app, P1) e
            return (app, P2)
        go scope up (Var v) = do
            let lam = scope !! v
            target <- traceShow ("lam", lam) $ readPort lam P1
            isERA <- case target of
                (addr, _) -> (== IEra) . nodeType <$> readNode addr
            if isERA then do
                linkHalf lam P1 up
                return (lam, P1)
              else do
                tag <- lift $ readSTRef nextTag
                lift $ modifySTRef nextTag succ
                dup <- mkNode IDup tag
                linkHalf dup P0 (lam, P1)
                linkHalf dup P1 up
                link (dup, P2) =<< readPort lam P1
                linkHalf lam P1 (dup, P0)
                return (dup, P1)
    enc <- go [] (root, P0) lam
    linkHalf root P0 enc
    return root

-- reduceNet :: NodeAddr -> OptLam s NodeAddr
-- reduceNet net =

decodeLam :: NodeAddr -> OptLam s Lam
decodeLam root = do
    nodeDepths <- lift $ newSTRef mempty
    let go depth exit (addr, port) = do
            Node{..} <- readNode addr
            lift $ modifySTRef nodeDepths $
              IntMap.insertWith (\ _new -> id) nodeID depth
            case nodeType of
                IDup -> do
                    let port' = case port of
                            P0 -> head exit
                            _ -> P0
                    go depth (port:exit) =<< readPort addr port'
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

runOptLam :: (forall s. OptLam s a) -> a
runOptLam act = runST $ do
    heap <- newArray_ (0, 1000) -- TODO
    garbage <- newSTRef []
    nextAddr <- newSTRef 0
    nextID <- newSTRef 1
    runReaderT act R{..}

showAll :: NodeAddr -> OptLam s String
showAll root = do
    seenref <- lift $ newSTRef mempty
    let go addr = do
            seen <- lift $ readSTRef seenref
            if addr `IntMap.member` seen then return []
              else do
                lift $ modifySTRef seenref $ IntMap.insert addr ()
                node <- readNode addr
                s <- pprNode node
                s0s <- go . fst =<< readPort addr P0
                s1s <- go . fst =<< readPort addr P1
                s2s <- go . fst =<< readPort addr P2
                return $ (addr, s) : s0s ++ s1s ++ s2s
    unlines . map (\(addr, s) -> unlines [show addr, s]) . sortBy (comparing fst) <$> go root

test = putStrLn $ runOptLam $ do
    node <- encodeLam term
    s <- pprNode =<< readNode 0
    -- return s
    show <$> decodeLam node
    -- showAll node
  where
    -- term = Lam $ Lam $ Var 0
    term = exp_mod
    -- term = App id const
    --   where
    --     id = Lam $ Var 0
    --     const = Lam $ Lam $ Var 0

exp_mod = l(l(l(a(a(a(v(0),l(l(a(v(1),l(a(a(v(1),l(l(a(v(1),a(a(v(2),v(1)),v(0)))))),v(0))))))),l(a(v(0),l(l(v(0)))))),l(a(a(a(v(2),v(3)),a(a(a(v(1),l(l(l(a(v(2),l(a(a(v(2),v(0)),v(1)))))))),l(v(0))),l(l(a(v(0),v(1)))))),a(a(a(v(1),l(l(v(1)))),l(v(0))),l(v(0)))))))))
  where
    l = Lam
    a (f, e) = App f e
    v = Var
{-# LANGUAGE RecordWildCards, Rank2Types #-}
module Language.IntNet
       ( NodeType(..), PortNum(..), NodeID, Node(..)
       , IntNet
       , mkNode, withNewRoot, root
       , link, linkHalf, readPort
       , reduce, run
       ) where

import Data.STRef
import Control.Monad.ST
import Control.Monad.Reader
import Control.Monad.Trans
import Control.Monad ((<=<), unless)
import Data.IntMap.Strict ((!))
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet

data NodeType = NRot
              | NLam
              | NApp
              | NDup Int
              | NEra
             deriving (Show)

data PortNum = P0
             | P1
             | P2
             deriving (Show, Eq, Enum, Bounded)

type NodeID = Int

data Node s = Node{ nodeType :: !NodeType
                  , nodeID :: !NodeID
                  , nodePort0, nodePort1, nodePort2 :: !(Port s)
                  }

data NodeTag = TEra
             | TLamApp
             | TDup !Int
             deriving (Show, Eq)

nodeTag :: Node s -> Maybe NodeTag
nodeTag Node{..} = case nodeType of
    NRot -> Nothing
    NLam -> Just TLamApp
    NApp -> Just TLamApp
    NDup tag -> Just $ TDup tag
    NEra -> Just TEra

type Port s = STRef s (Node s, PortNum)

data R s = R{ root :: Node s
            , nextID :: STRef s NodeID
            }

type IntNet s = ReaderT (R s) (ST s)

mkNode :: NodeType -> IntNet s (Node s)
mkNode nodeType = do
    idRef <- asks nextID
    nodeID <- lift $ readSTRef idRef <* modifySTRef idRef succ
    root <- asks root
    lift $ mkNode_ nodeType nodeID root

mkNode_ :: NodeType -> Int -> Node s -> ST s (Node s)
mkNode_ nodeType nodeID root = do
    nodePort0 <- newSTRef (root, P0)
    nodePort1 <- newSTRef (root, P0)
    nodePort2 <- newSTRef (root, P0)
    return Node{..}

mkRoot :: ST s (Node s)
mkRoot = mfix $ mkNode_ NRot 0

withNewRoot :: IntNet s a -> IntNet s a
withNewRoot act = do
    root <- lift mkRoot
    local (\r -> r{ root = root }) act

getPort :: Node s -> PortNum -> Port s
getPort Node{..} pnum = case pnum of
    P0 -> nodePort0
    P1 -> nodePort1
    P2 -> nodePort2

readPort :: Node s -> PortNum -> IntNet s (Node s, PortNum)
readPort node pnum = lift . readSTRef $ getPort node pnum

linkHalf :: Node s -> PortNum -> (Node s, PortNum) -> IntNet s ()
linkHalf node pnum to = lift $ writeSTRef (getPort node pnum) to

link :: (Node s, PortNum) -> (Node s, PortNum) -> IntNet s ()
link a b = do
    uncurry linkHalf a b
    uncurry linkHalf b a

annihilate :: Node s -> Node s -> IntNet s ()
annihilate a b = do
    a1 <- readPort a P1
    b1 <- readPort b P1
    link a1 b1
    a2 <- readPort a P2
    b2 <- readPort b P2
    link a2 b2

commute :: Node s -> Node s -> IntNet s ()
commute a b = do
    a2 <- mkNode $ nodeType a
    b2 <- mkNode $ nodeType b
    link (b, P0) =<< readPort a P1
    link (a, P0) =<< readPort b P1
    link (b, P1) (a, P1)
    link (b2, P0) =<< readPort a P2
    link (a2, P0) =<< readPort b P2
    link (a, P2) (b2, P1)
    link (b, P2) (a2, P1)
    link (b2, P2) (a2, P2)

erase :: Node s -> Node s -> IntNet s ()
erase a b = do
    e2 <- mkNode NEra
    link (a, P0) =<< readPort b P1
    link (e2, P0) =<< readPort b P2

reduce :: Node s -> IntNet s ()
reduce net = do
    (pushVisit, popVisit) <- do
        ref <- lift $ newSTRef [(net, P0)]
        let push next = lift $ modifySTRef ref $ \vs -> (next, P1):(next, P2):vs
            pop = do
                vs <- lift $ readSTRef ref
                case vs of
                    [] -> return Nothing
                    v:vs -> do
                        lift $ writeSTRef ref vs
                        return $ Just v
        return (push, pop)

    (isSolid, solidify) <- do
        ref <- lift $ newSTRef mempty
        let isSolid node = lift $ (nodeID node `IntSet.member`) <$> readSTRef ref
            solidify node = lift $ modifySTRef ref $ IntSet.insert (nodeID node)
        return (isSolid, solidify)

    (setExitPort, getExitPort) <- do
        ref <- lift $ newSTRef mempty
        let set node port = do
                lift $ modifySTRef ref $ IntMap.insert (nodeID node) port
            get node = do
                lift $ (! nodeID node) <$> readSTRef ref
        return (set, get)

    let processNode addr port = do
            (next, nextPort) <- readPort addr port
            processNext next nextPort
        processNext next nextPort = do
            (prev, prevPort) <- readPort next nextPort
            nextSolid <- isSolid next
            unless nextSolid $ case nextPort of
                P0 -> do
                    case (prevPort, nodeTag prev, nodeTag next) of
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
                            solidify next
                            pushVisit next
                _ -> do
                    setExitPort next nextPort
                    (next, nextPort) <- readPort next P0
                    processNext next nextPort
    fix $ \loop -> do
        v <- popVisit
        case v of
            Just (addr, port) -> do
                processNode addr port
                loop
            Nothing -> return ()

run :: (forall s. IntNet s a) -> a
run act = runST $ do
    nextID <- newSTRef 1
    root <- mkRoot
    runReaderT act R{..}

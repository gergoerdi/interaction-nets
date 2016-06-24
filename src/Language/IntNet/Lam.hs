module Language.IntNet.Lam where

import Language.IntNet as IntNet
import Language.Lam
import Data.STRef
import Control.Monad.Reader
import Control.Monad.Trans
import Data.IntMap.Strict ((!))
import qualified Data.IntMap.Strict as IntMap

encodeLam :: Lam -> IntNet s (Node s)
encodeLam lam = do
    nextTag <- do
        ref <- lift $ newSTRef 0
        return $ lift $ do
            modifySTRef ref succ
            readSTRef ref

    let go scope up (Lam body) = do
            del <- mkNode NEra
            lam <- mkNode NLam
            linkHalf lam P0 up
            link (lam, P1) (del, P0)
            link (del, P1) (del, P2)
            bod <- go (lam:scope) (lam, P2) body
            linkHalf lam P2 bod
            return (lam, P0)
        go scope up (App f e) = do
            app <- mkNode NApp
            linkHalf app P2 up
            linkHalf app P0 =<< go scope (app, P0) f
            linkHalf app P1 =<< go scope (app, P1) e
            return (app, P2)
        go scope up (Var v) = do
            let lam = scope !! v
            (target, targetPort) <- readPort lam P1
            case nodeType target of
                NEra -> do
                    linkHalf lam P1 up
                    return (lam, P1)
                _ -> do
                    dup <- mkNode . NDup =<< nextTag
                    linkHalf dup P0 (lam, P1)
                    linkHalf dup P1 up
                    link (dup, P2) =<< readPort lam P1
                    linkHalf lam P1 (dup, P0)
                    return (dup, P1)

    withNewRoot $ do
        root <- asks root
        enc <- go [] (root, P0) lam
        linkHalf root P0 enc
        return root

decodeLam :: Node s -> IntNet s Lam
decodeLam root = do
    (setDepth, getDepth) <- do
        ref <- lift $ newSTRef mempty
        let set node depth = lift $ modifySTRef ref $
                             IntMap.insertWith (\ _new old -> old) (nodeID node) depth
            get node = lift $ (! nodeID node) <$> readSTRef ref
        return (set, get)

    let go depth exit (node, port) = do
            setDepth node depth
            case nodeType node of
                NDup _ -> do
                    let (port', exit') = case port of
                            P0 -> (head exit, tail exit)
                            _ -> (P0, port:exit)
                    go depth exit' =<< readPort node port'
                NLam -> case port of
                    P1 -> do
                        depth' <- getDepth node
                        return $ Var (depth - depth' - 1)
                    _ -> Lam <$> (go (succ depth) exit =<< readPort node P2)
                NApp -> do
                    f <- go depth exit =<< readPort node P0
                    e <- go depth exit =<< readPort node P1
                    return $ App f e
    go 0 [] =<< readPort root P0

optLam :: Lam -> Lam
optLam term = IntNet.run $ do
    node <- encodeLam term
    IntNet.reduce node
    decodeLam node

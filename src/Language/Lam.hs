module Language.Lam where

data Lam = Var Int
         | Lam Lam
         | App Lam Lam
         deriving Show

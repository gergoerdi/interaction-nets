module Main (main) where

import Language.Lam
import Language.IntNet.Lam
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
    describe "optLam" $ do
      it "reduces 100^100 mod 31 to 25" $ do
          toNat (optLam term) `shouldBe` 25
  where
    term = theTerm

exp_mod = l(l(l(a(a(a(v(0),l(l(a(v(1),l(a(a(v(1),l(l(a(v(1),a(a(v(2),v(1)),v(0)))))),v(0))))))),l(a(v(0),l(l(v(0)))))),l(a(a(a(v(2),v(3)),a(a(a(v(1),l(l(l(a(v(2),l(a(a(v(2),v(0)),v(1)))))))),l(v(0))),l(l(a(v(0),v(1)))))),a(a(a(v(1),l(l(v(1)))),l(v(0))),l(v(0)))))))))
  where
    l = Lam
    a (f, e) = App f e
    v = Var

theTerm = app exp_mod [fromNat 100, fromNat 100, fromNat 31]
  where
    app = foldl App

fromNat :: Integer -> Lam
fromNat  = Lam . Lam . go
  where
    go 0 = zero
    go n = succ $ go (n-1)

    zero = Var 0
    succ = App (Var 1)

toNat :: Lam -> Integer
toNat (Lam (Lam e)) = go e
  where
    go (App (Var 1) e) = succ $ go e
    go (Var 0) = 0
    go _ = error "Not a Nat in normal form"
toNat _ = error "Not a Nat in normal form"

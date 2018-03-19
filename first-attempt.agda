module _ where

open import Data.Vec
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

data B (A : Set) : ℕ → Set where
  base : (a : A) → B A 0
  _*ᴮ_ : {k : ℕ} → (l r : B A k) → B A (suc k)

to : {A : Set} {k : ℕ} -> B A k -> Vec A (2 ^ k)
to (base a) = a ∷ []
to {k = suc k} (l *ᴮ r) rewrite +-identityʳ (2 ^ k) = to l ++ to r

from : {A : Set} {k : ℕ} -> Vec A (2 ^ k) -> B A k
from {k = zero} (a ∷ []) = base a
from {k = suc k} v rewrite +-identityʳ (2 ^ k) with splitAt (2 ^ k) v
... | vl , vr , p = from vl *ᴮ from vr

toFrom : {A : Set} {k : ℕ} -> (v : Vec A (2 ^ k)) -> to {k = k} (from v) ≡ v
toFrom {k = zero} (a ∷ []) = refl
toFrom {k = suc k} v = {!!}
--toFrom {k = suc k} v rewrite +-identityʳ (2 ^ k) = {!!}
{-
(2 ^ k) + 0 * (2 ^ k) != w of type ℕ
when checking that the type
(k w : ℕ) (w₁ : w ≡ (2 ^ k)) {A : Set} (v : Vec A ((2 ^ k) + w)) →
to (from v | w | w₁) ≡ v
of the generated with function is well-formed
-}

split++left : {A : Set} {j k : ℕ} (l : Vec A j) (r : Vec A k) → proj₁ (splitAt j (l ++ r)) ≡ l
split++left [] r = refl
split++left {j = suc j} (x ∷ l) r with splitAt j (l ++ r)
split++left {_} {suc j} (x ∷ l) r | l' , r' , q = {!!}

split++right : {A : Set} {j k : ℕ} (l : Vec A j) (r : Vec A k) → proj₁ (proj₂ (splitAt j (l ++ r))) ≡ r
split++right [] r = refl
split++right {j = suc j} (x ∷ l) r with splitAt j (l ++ r)
split++right {_} {suc j} (x ∷ l) r | l' , r' , q = {!!}

fromTo : {A : Set} {k : ℕ} -> (b : B A k) -> from (to b) ≡ b
fromTo (base a) = refl
fromTo {k = suc k} (l *ᴮ r)
  rewrite
    +-identityʳ (2 ^ k)
  | split++left (to l) (to r)
  | fromTo l
  | split++right (to l) (to r)
  | fromTo r
  = refl


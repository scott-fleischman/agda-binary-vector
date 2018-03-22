module _ where

open import Data.Nat
  using (ℕ; zero; suc; _^_; _+_)
open import Data.Nat.Properties
  using (+-identityʳ)
open import Data.Product
  using (∃₂; _,_; Σ; proj₁; proj₂)
open import Data.Vec
  using (Vec; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

data B (A : Set) : ℕ → Set where
  base : (a : A) → B A 0
  _*ᴮ_ : {k : ℕ} → (l r : B A k) → B A (suc k)


to : {A : Set} {k : ℕ} -> B A k -> Vec A (2 ^ k)

to-rewrite-identity+0 : ∀ {A} k → B A k → B A k → ∀ w → w ≡ (2 ^ k) → Vec A ((2 ^ k) + w)
to-rewrite-identity+0 k l r .(2 ^ k) refl = to l ++ to r

to (base a) = a ∷ []
to {k = suc k} (l *ᴮ r) = to-rewrite-identity+0 k l r (2 ^ k + 0) (+-identityʳ (2 ^ k))

split-left : {A : Set} (m : ℕ) {n : ℕ} (xs : Vec A (m + n)) → Vec A m
split-left zero xs = []
split-left (suc m) (x ∷ xs) = x ∷ split-left m xs

split-right : {A : Set} (m : ℕ) {n : ℕ} (xs : Vec A (m + n)) → Vec A n
split-right zero xs = xs
split-right (suc m) (_ ∷ xs) = split-right m xs

split-right≡ : {A : Set} {k : ℕ} (w : ℕ) (p : w ≡ (2 ^ k)) (v : Vec A ((2 ^ k) + w))
  → Vec A (2 ^ k)
split-right≡ {k = k} .(2 ^ k) refl v = split-right (2 ^ k) v

from : {A : Set} {k : ℕ} -> Vec A (2 ^ k) -> B A k
from {k = zero} (a ∷ []) = base a
from {k = suc k} v
  = from (split-left (2 ^ k) v)
  *ᴮ from (split-right≡ {k = k} (2 ^ k + 0) (+-identityʳ (2 ^ k)) v)


toFrom : {A : Set} {k : ℕ} -> (v : Vec A (2 ^ k)) -> to {k = k} (from v) ≡ v
toFrom {k = zero} (a ∷ []) = refl
toFrom {k = suc k} v = {!!}

fromTo-left : ∀ {A} k (l r : B A k)
  → (from
       (split-left (2 ^ k)
        (to-rewrite-identity+0 k l r ((2 ^ k) + 0) (+-identityʳ (2 ^ k))))) ≡ l
fromTo-left zero (base a) r = refl
fromTo-left (suc k) (ll *ᴮ lr) r = {!!}

fromTo : {A : Set} {k : ℕ} -> (b : B A k) -> from (to b) ≡ b
fromTo (base a) = refl
fromTo {k = suc k} (l *ᴮ r) = {!!}

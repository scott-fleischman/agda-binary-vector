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

splitAt-recurse : {A : Set} {n : ℕ} (m : ℕ) (x : A) (xs : Vec A (m + n))
  (r : ∃₂ λ (ys : Vec A m) (zs : Vec A n) → xs ≡ ys ++ zs)
  → ∃₂ λ (ys : Vec A (suc m)) (zs : Vec A n) → x ∷ xs ≡ ys ++ zs
splitAt-recurse m x .(ys ++ zs) (ys , zs , refl) = x ∷ ys , zs , refl

splitAt : {A : Set} (m : ℕ) {n : ℕ} (xs : Vec A (m + n))
  → ∃₂ λ (ys : Vec A m) (zs : Vec A n) → xs ≡ ys ++ zs
splitAt zero    xs        = ([] , xs , refl)
splitAt (suc m) (x ∷ xs) = splitAt-recurse m x xs (splitAt m xs)

from : {A : Set} {k : ℕ} -> Vec A (2 ^ k) -> B A k

from-split : ∀ {A} k (v : Vec A ((2 ^ k) + (2 ^ k))) → Σ (Vec A (2 ^ k)) (λ a → Σ (Vec A (2 ^ k)) (λ zs → v ≡ a ++ zs)) → B A (suc k)
from-split k v (vl , vr , p) = from vl *ᴮ from vr

from-rewrite-identity+0 : ∀ {A} k w → w ≡ (2 ^ k) → Vec A ((2 ^ k) + w) → B A (suc k)
from-rewrite-identity+0 k .(2 ^ k) refl v = from-split k v (splitAt (2 ^ k) v)

from {k = zero} (a ∷ []) = base a
from {k = suc k} v = from-rewrite-identity+0 k (2 ^ k + 0) (+-identityʳ (2 ^ k)) v


toFrom : {A : Set} {k : ℕ} -> (v : Vec A (2 ^ k)) -> to {k = k} (from v) ≡ v
toFrom {k = zero} (a ∷ []) = refl
toFrom {k = suc k} v = {!!}

split++left : {A : Set} {j k : ℕ} (l : Vec A j) (r : Vec A k) → proj₁ (splitAt j (l ++ r)) ≡ l
split++left [] r = refl
split++left {j = suc j} (x ∷ l) r = {!!}

split++right : {A : Set} {j k : ℕ} (l : Vec A j) (r : Vec A k) → proj₁ (proj₂ (splitAt j (l ++ r))) ≡ r
split++right [] r = refl
split++right {j = suc j} (x ∷ l) r = {!!}

fromTo : {A : Set} {k : ℕ} -> (b : B A k) -> from (to b) ≡ b
fromTo (base a) = refl
fromTo {k = suc k} (l *ᴮ r) = {!!}

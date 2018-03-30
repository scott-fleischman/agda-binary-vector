module _ where

open import Agda.Primitive
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec hiding (take; drop)
open import Relation.Binary.PropositionalEquality

data B (A : Set) : ℕ → Set where
  base : (a : A) → B A 0
  _*ᴮ_ : {k : ℕ} → (l r : B A k) → B A (suc k)

to : {A : Set} {k : ℕ} -> B A k -> Vec A (2 ^ k)
to (base a) = a ∷ []
to {k = suc k} (l *ᴮ r) rewrite +-identityʳ (2 ^ k) = to l ++ to r

take : {A : Set} (m : ℕ) {n : ℕ} (xs : Vec A (m + n)) → Vec A m
take zero xs = []
take (suc m) (x ∷ xs) = x ∷ take m xs

drop : {A : Set} (m : ℕ) {n : ℕ} (xs : Vec A (m + n)) → Vec A n
drop zero xs = xs
drop (suc m) (_ ∷ xs) = drop m xs

take++ : {A : Set} {m n : ℕ} (l : Vec A m) (r : Vec A n) → take m (l ++ r) ≡ l
take++ [] r = refl
take++ (x ∷ l) r = cong (x ∷_) (take++ l r)

drop++ : {A : Set} {m n : ℕ} (l : Vec A m) (r : Vec A n) → drop m (l ++ r) ≡ r
drop++ [] r = refl
drop++ (x ∷ l) r = drop++ l r

take++drop-id : {A : Set} (m : ℕ) {n : ℕ} (v : Vec A (m + n)) → take m v ++ drop m v ≡ v
take++drop-id zero v = refl
take++drop-id (suc m) (x ∷ v) = cong (x ∷_) (take++drop-id m v)

from : {A : Set} {k : ℕ} -> Vec A (2 ^ k) -> B A k
from {k = zero} (a ∷ []) = base a
from {A} {suc k} v = from (take (2 ^ k) v) *ᴮ from (subst (Vec A) (+-identityʳ (2 ^ k)) (drop (2 ^ k) v))

toFrom : {A : Set} {k : ℕ} -> (v : Vec A (2 ^ k)) -> to {k = k} (from v) ≡ v
toFrom {k = zero} (a ∷ []) = refl
toFrom {k = suc k} v
  rewrite +-identityʳ (2 ^ k)
  | toFrom {k = k} (take (2 ^ k) v)
  | toFrom {k = k} (drop (2 ^ k) v)
  = take++drop-id (2 ^ k) v

fromTo : {A : Set} {k : ℕ} -> (b : B A k) -> from (to b) ≡ b
fromTo (base a) = refl
fromTo {k = suc k} (l *ᴮ r)
  rewrite +-identityʳ (2 ^ k)
  | take++ (to l) (to r)
  | fromTo l
  | drop++ (to l) (to r)
  | fromTo r
  = refl

module Bijection where
  open import Function.Bijection
  open import Function.Equality
  open import Function.Surjection
  open import Relation.Binary.PropositionalEquality as Prop

  to-injective : ∀ {A k} {x y : B A k} → to x ≡ to y → x ≡ y
  to-injective {A}{k}{x}{y} p with Prop.cong (from {k = k}) p
  ... | r rewrite fromTo x | fromTo y = r

  bij : {A : Set} {k : ℕ} → Bijection (Prop.setoid (B A k)) (Prop.setoid (Vec A (2 ^ k)))
  bij .Bijection.to ._⟨$⟩_ = to
  bij .Bijection.to .Π.cong = Prop.cong to
  bij .Bijection.bijective .Bijective.injective = to-injective
  bij .Bijection.bijective .Bijective.surjective .Surjective.from ._⟨$⟩_ = from
  bij .Bijection.bijective .Bijective.surjective .Surjective.from .Π.cong = Prop.cong from 
  bij {k = k} .Bijection.bijective .Bijective.surjective .Function.Surjection.Surjective.right-inverse-of = toFrom {k = k}

module _ where

open import Agda.Primitive
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec
open import Relation.Binary.PropositionalEquality

data B (A : Set) : ℕ → Set where
  base : (a : A) → B A 0
  _*ᴮ_ : {k : ℕ} → (l r : B A k) → B A (suc k)

to : {A : Set} {k : ℕ} -> B A k -> Vec A (2 ^ k)
to (base a) = a ∷ []
to {k = suc k} (l *ᴮ r) rewrite +-identityʳ (2 ^ k) = to l ++ to r

from : {A : Set} {k : ℕ} -> Vec A (2 ^ k) -> B A k
from {k = zero} (a ∷ []) = base a
from {A} {suc k} v with splitAt (2 ^ k) v
... | vl , vr , p = from vl *ᴮ from (subst (Vec A) (+-identityʳ (2 ^ k)) vr)

toFrom : {A : Set} {k : ℕ} -> (v : Vec A (2 ^ k)) -> to {k = k} (from v) ≡ v
toFrom {k = zero} (a ∷ []) = refl
toFrom {k = suc k} v with splitAt (2 ^ k) v
... | vl , vr , p rewrite +-identityʳ (2 ^ k) | toFrom {k = k} vl | toFrom {k = k} vr = sym p 

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

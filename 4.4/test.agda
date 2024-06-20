module test (A B : Set) where
open import Agda.Builtin.Equality
-- open import Relation.Binary.PropositionalEquality

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data _==_ {A : Set} : A → A → Set where
  refl : {x : A} → x == x

cong : {A B : Set} {a b : A} (f : A → B) → a == b → f a == f b
cong f refl = refl

trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  → x ≡ z
trans refl refl = refl

_+_ : Nat → Nat → Nat
zero + x = x
(suc x) + y = suc (x + y)

nat1 : ( (suc zero ) + (suc zero ) ) ==  ( suc (suc zero ) )
nat1 = refl

lemma10 : (x : Nat) → ( zero + x ) == x
lemma10 x = refl

lemma11 : (x : Nat) → ( x + zero ) == x
lemma11 zero = refl
lemma11 (suc x) = cong suc (lemma11 x)


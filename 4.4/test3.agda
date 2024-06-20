module test3 where
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

zero+ : (y : ℕ) → zero + y ≡ y
zero+ y = refl

+-zero : (y : ℕ) → y ≡ y + zero
+-zero zero = refl
+-zero (suc y) = cong suc (+-zero y)

suc-distrib : (x y : ℕ) → suc (x + y) ≡ x + suc y
suc-distrib zero y = refl
suc-distrib (suc x) y = cong suc (suc-distrib x y)

add-sym : (x y : ℕ) → ( x + y ) ≡ ( y + x )
add-sym zero y = trans (zero+ y) (+-zero y)
add-sym (suc x) y = begin
  (suc x) + y
  ≡⟨⟩
  suc ( x + y )
  ≡⟨ cong suc (add-sym x y) ⟩
  suc ( y + x )
  ≡⟨ suc-distrib y x ⟩
  y + suc x
  ∎
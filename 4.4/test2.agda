module test2 where
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

suc-distrib : (x y : ℕ) → suc (x + y) ≡ x + suc y
suc-distrib zero y = refl
suc-distrib (suc x) y = cong suc (suc-distrib x y)

add-sym : (x y : ℕ) → x + y ≡ y + x
add-sym zero zero = refl
add-sym zero (suc y) = cong suc (add-sym zero y)
add-sym (suc x) zero  = cong suc (add-sym x zero)
add-sym (suc x) (suc y) = begin
    (suc x) + (suc y)
    ≡⟨⟩ -- reflにより
    suc (x + suc y) -- こう変形できる
    ≡⟨ cong suc (add-sym x (suc y)) ⟩ -- これを解くと suc (x + suc y) = suc (suc y + x) が導かれるよって、これにより
    suc (suc y + x) -- こう変形できる
    ≡⟨⟩
    suc (suc (y + x))
    ≡⟨ suc-distrib (suc y) x ⟩
    (suc y) + (suc x)
    ∎

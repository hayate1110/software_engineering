module test (A B : Set) where

data _==_ {A : Set} : A → A → Set where
  refl : {x : A} → x == x

l1 : {x y z : A} → x == y → y == z → x == z
l1 refl refl = refl

l2 : {A B : Set} { x : A } { y : A } { f : A → B } → x == y → f x == f y
l2 refl = refl

Injective : (f : A → B) → Set
Injective f = {x y : A} → f x == f y → x == y

l3 : {x y : A} {f : A → B} → Injective f → f x == f y → x == y
l3 injective pf = injective pf
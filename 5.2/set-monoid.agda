module set-monoid where

open  import  Relation.Binary.PropositionalEquality hiding ([_])
-- import Relation.Binary.EqReasoning as EqR

record Monoid {ℓ} (A : Set ℓ)  : Set ℓ where
   field
      _∙_ : A → A → A -- 何らかの演算
      id : A -- 単位元
      --  axiom of Monoid
      idL :  {a : A } → id  ∙  a ≡ a -- 単位元と何らかの値の演算は、そのまま何らかの値が返る
      idR :  {a : A } → a ∙ id  ≡ a -- 単位元と何らかの値の演算は、そのまま何らかの値が返る
      assoc : {a b c : A} →  a ∙ ( b ∙ c ) ≡  ( a ∙  b ) ∙ c -- 何らかの演算は結合法則を満たす



infixr 40 _::_ -- リストへの要素の追加、右結合の演算 ex. a - b - c = (a - b) - c

data  List {a} (A : Set a)  : Set a where
   [] : List A
   _::_ : A → List A → List A -- Aと型Aのリストを受け取って、リストを返す 


infixl 30 _++_ -- リスト同士の結合、左結合の演算 ex. a - b - c = a - (b - c)

_++_ : ∀ {a}  {A : Set a } → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)


listMonoid : ∀{a} → (A : Set a) → Monoid {a} (List A)
listMonoid {a} A  = record {
        _∙_  = _++_ ;
        id  =  []  ;
        idL =  refl ;
        idR =  λ {a} → idR a;
        assoc =  λ {x y z} → assoc  x y z
  } where
      assoc : (a b c : List A) →  a ++ ( b ++ c ) ≡  ( a ++  b ) ++ c
      assoc [] x y = refl
      assoc (xh :: xl) y z = cong (_::_ xh) ( assoc xl y z )
      idR : (a : List A ) → a ++ [] ≡ a
      idR [] = refl
      idR (x :: a) = cong (_::_ x) (idR a)


_○_ :  ∀{a} → { A B C : Set a } → ( g : B → C ) → ( f : A → B ) →  A → C 
g ○ f  = λ x → g ( f x )


funcMonoid : ∀{a} → (A : Set a) → Monoid {a} (A → A )
funcMonoid {a} A  = record {
        _∙_  = _○_ ;
        id  = λ y → y  ;
        idL =  refl ;
        idR =  refl ;
        assoc =  λ {x y z} → assoc  {x} {y} {z}
  } where
      assoc : {a b c : A → A } →  a ○ ( b ○ c ) ≡  ( a ○  b ) ○ c
      assoc  = refl


open import stdalone-kleisli
open import Level 

data *  (l : Level ) : Set (suc l) where
    ⊤ : * l

MonoidIsCategory : {l : Level} {A : Set l} →  Monoid A → Category {l}
MonoidIsCategory {l} {A} m = record {
       Obj = * l
    ;  Hom =  λ a b → A
    ;  _o_ = λ {a b c} f g  → f ∙ g
    ;  id = λ a → id 
    ;  isCategory = record {
           idL = idL
         ; idR = idR
         ; assoc = assoc
       }
   } where
      open Monoid m



MonoidCategory : {l : Level} (A : Set (suc l)) → Category {l}
MonoidCategory {l} A = record {
       Obj = Monoid {suc l} A
    ;  Hom = λ a b → {!   !}
    ;  _o_ = λ {a b c} f g  → λ x → f (g x)
    ;  id = λ a → {!   !}
    ;  isCategory = record {
           idL = {!   !}
         ; idR = {!   !}
         ; assoc = {!   !}
       }
   }

--
-- we are using ≡ for function equality in our Sets
-- so this does not work well
--
ListFunctor : Functor Sets Sets 
ListFunctor = record {
        FObj = λ x → List x
     ;  FMap = fmap
     ;  isFunctor = record {
            identity = λ {A} → {!   !}
          ; distr = λ {a} {b} {c} {f} {g} →  {!   !}
         }
  } where
      open Category 
      fmap :   {A B : Obj Sets} → Hom Sets A B → Hom Sets (List A) (List B)
      fmap f [] = []
      fmap f (x :: y) = ( f x ) :: fmap f y
      identity :  {A : Obj Sets} → ( x : List A ) → fmap (id Sets A) x ≡ id Sets (List A) x
      identity {A} [] = refl
      identity {A} (h :: t) = {!   !}
      distr :  {a b c : Obj Sets} {f : Hom Sets a b} {g : Hom Sets b c} → (x : List a)  → fmap (Sets [ g o f ]) x ≡ (Sets [ fmap g o fmap f ]) x
      distr [] = {!   !}
      distr {a} {b} {c} {f} {g} (h :: t ) = begin  
         fmap (Sets [ g o f ]) (h :: t) ≡⟨ {!   !} ⟩
         (Sets [ fmap g o fmap f ]) (h :: t) ∎ where
             open ≡-Reasoning 

ListFunctor' : (A B : Set ) → (f : A → B )  → Functor ( MonoidIsCategory (listMonoid A) ) ( MonoidIsCategory (listMonoid B) )
ListFunctor' A B f = record {
        FObj = λ x → ⊤
     ;  FMap = fmap
     ;  isFunctor = record {
            identity =  λ {A}  → refl
          ; distr = λ {a} {b} {c} {f} {g} →  distr g f 
         }
      } where
         fmap :  List A → List B
         fmap [] = []
         fmap  (x :: xs) = (f x) :: fmap  xs
         -- distr : ( g f : List A ) → fmap (MonoidIsCategory {zero} (listMonoid {zero} A) [ g o f ]) ≡ (MonoidIsCategory {zero} (listMonoid {zero} B) [ fmap g o fmap f ])
         distr : ( g h : List A ) → fmap (g ++ h) ≡  fmap g ++ fmap h
         distr [] h = refl
         distr (x :: g) h = cong (λ k → f x :: k) (distr g h)
          

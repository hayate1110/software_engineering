module Sets where

open import Level
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym )

record IsCategory {l : Level} (  Obj : Set (suc l) ) (Hom : Obj → Obj → Set l )
     ( _o_ : { a b c : Obj } → Hom b c  → Hom a b →  Hom a c )
     ( id : ( a  : Obj ) → Hom a a )
         : Set (suc l) where
  field
       idL : { a b : Obj } { f : Hom a b } → ( id b o f ) ≡ f
       idR : { a b : Obj } { f : Hom a b } → ( f o id a ) ≡ f
       assoc : { a b c d : Obj } { f : Hom c d }{ g : Hom b c }{ h : Hom a b } →  f o ( g  o h ) ≡ ( f  o g )  o h

record Category {l : Level} : Set (suc (suc l)) where
  field
       Obj : Set (suc l)
       Hom : Obj → Obj → Set l
       _o_ : { a b c : Obj } → Hom b c  → Hom a b →  Hom a c   --   (f o g) x = f ( g  x  ) ( f : b → c) ( g : a → b)
       id : ( a  : Obj ) → Hom a a                             -- λ (x : a) → x
       isCategory : IsCategory Obj Hom _o_ id

Sets : Category
Sets = record {
       Obj = Set 
    ;  Hom =  λ a b → a → b 
    ;  _o_ = λ {a b c} f g x → f (g x )
    ;  id = λ _ x → x
    ;  isCategory = record {
           idL = refl
         ; idR = refl
         ; assoc = refl
       }
   }
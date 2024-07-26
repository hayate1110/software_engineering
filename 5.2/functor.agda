module functor where

open import Level
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym )
open import Axiom.Extensionality.Propositional

--
-- Categoryの定義
-- 
-- 圏(Category)とは次を満たすもの。
-- 
-- 型aから型aへの恒等射(id a)がある
-- 型a,b,cと、二つの射 f: a ->b, g: b-> c があった時、その合成 g ○ f がある
-- id a ○ f ≡ f と f  ○ id a ≡ f が成り立つ
-- 関数の合成○に関する結合法則  f ○ (g ○ h) ≡ (f ○  g) ○ h  が成立
--

-- 構造が満たす論理式 (axiom)を表す。
record IsCategory {l : Level} (  Obj : Set (suc l) ) (Hom : Obj → Obj → Set l )
     ( _o_ : { a b c : Obj } → Hom b c  → Hom a b →  Hom a c )
     ( id : ( a  : Obj ) → Hom a a )
         : Set (suc l) where
  field
       idL : { a b : Obj } { f : Hom a b } → ( id b o f ) ≡ f
       idR : { a b : Obj } { f : Hom a b } → ( f o id a ) ≡ f
       assoc : { a b c d : Obj } { f : Hom c d }{ g : Hom b c }{ h : Hom a b } →  f o ( g  o h ) ≡ ( f  o g )  o h

-- 構造に必要とされるもの(input)と、構造で提供されるもの(output)を表す。
record Category {l : Level} : Set (suc (suc l)) where
  field
       Obj : Set (suc l)
       Hom : Obj → Obj → Set l
       _o_ : { a b c : Obj } → Hom b c  → Hom a b →  Hom a c   --   (f o g) x = f ( g  x  ) ( f : b → c) ( g : a → b)
       id : ( a  : Obj ) → Hom a a                             -- λ (x : a) → x
       isCategory : IsCategory Obj Hom _o_ id

-- Categoryのインスタンスを生成
Sets : Category
Sets = record {
        Obj = Set 
    ;  Hom =  λ a b → a → b
    ;  _o_ = λ f g x → f ( g x )
    ;  id = λ A  x → x
    ;  isCategory = record {
            idL = refl
            ; idR = refl
            ; assoc = refl
        }
    }

--
-- Functorの定義
--

open Category

_[_o_] :  {l : Level} (C : Category {l} ) → {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
C [ f o g ] = _o_ C f g

record IsFunctor {l : Level} (C D : Category {l} )
    (FObj : Obj C → Obj D)
    (FMap : {A B : Obj C} → Hom C A B → Hom D (FObj A) (FObj B))
        : Set (suc l ) where
    field
        identity : {A : Obj C} →  FMap (id C A) ≡ id D (FObj A)
        distr : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
            → FMap ( C [ g o f ])  ≡ (D [ FMap g o FMap f ] )

record Functor {l : Level} (domain codomain : Category {l} ) : Set (suc l) where
    field
        FObj : Obj domain → Obj codomain
        FMap : {A B : Obj domain} → Hom domain A B → Hom codomain (FObj A) (FObj B)
        isFunctor : IsFunctor domain codomain FObj FMap

--
-- Listの定義
--

infixr 40 _::_ -- リストへ要素を追加する演算子の定義
data  List {a} (A : Set a)  : Set a where
   [] : List A
   _::_ : A → List A → List A -- Aと型Aのリストを受け取って、リストを返す 


infixl 30 _++_ -- リスト同士の結合を行う演算子の定義

_++_ : ∀ {a}  {A : Set a } → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

--
-- ListのFunctorを証明する。
--

open Functor
open ≡-Reasoning

postulate extensionality : { c₁ c₂ : Level}  → Extensionality c₂ c₂

ListFunctor : Functor Sets Sets 
ListFunctor = record {
        FObj = λ x → List x
        ;  FMap = fmap
        ;  isFunctor = record {
            identity =  extensionality {zero} {zero} ( λ x →  identity x )
            ; distr = λ {a} {b} {c} {f} {g} →  extensionality {zero} {zero} ( λ x →  distr x )
            }
    } where
        fmap :   {A B : Obj Sets} → Category.Hom Sets A B → Hom Sets (List A) (List B)
        fmap f [] = []
        fmap f (x :: y) = ( f x ) :: fmap f y
        identity :  {A : Obj Sets} → ( x : List A ) → fmap (id Sets A) x ≡ id Sets (List A) x
        identity {A} [] = refl
        identity {A} (h :: t) = cong (_::_ h) (identity t)
        distr :  {a b c : Obj Sets} {f : Hom Sets a b} {g : Hom Sets b c} → (x : List a)  → fmap (Sets [ g o f ]) x ≡ (Sets [ fmap g o fmap f ]) x
        distr [] = refl
        distr {a} {b} {c} {f} {g} (h :: t ) =  let open ≡-Reasoning in begin
            fmap (Sets [ g o f ]) (h :: t)
            ≡⟨ cong (_::_ (g (f h))) (distr t) ⟩
            (Sets [ fmap g o fmap f ]) (h :: t)
            ∎


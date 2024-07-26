module Category1 where

open import Level
open import Relation.Binary
open import Relation.Binary.Core
open import Axiom.Extensionality.Propositional

open  import  Relation.Binary.PropositionalEquality renaming (cong to ≡-cong ) hiding ([_])
open ≡-Reasoning

--        f       g       h              f ( g ( h x ) )
--     d ←--- c ←--- b ←--- a
--

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
       _o_ : { a b c : Obj } → Hom b c  → Hom a b →  Hom a c
       id : ( a  : Obj ) → Hom a a
       isCategory : IsCategory Obj Hom _o_ id

Sets : Category
Sets = record {
       Obj = Set 
    ;  Hom =  λ  a b → a → b
    ;  _o_ = λ  f g x → f ( g x )
    ;  id = λ  A  x → x
    ;  isCategory = record {
           idL = refl
         ; idR = refl
         ; assoc = refl
       }
   }

data  List {l : Level} (A : Set l ) : Set l where
   [] : List A
   _::_ : A → List A → List A

data  One {l : Level}  : Set l where
   * : One

append : { A : Set } → List A → List A → List A
append [] x =  x
append (x :: y ) z = x :: append y z

open  import  Relation.Binary.PropositionalEquality hiding ([_])

list-assoc :  { a : Set } → ( x y z : List a ) → append (append x y ) z ≡ append x ( append y z )
list-assoc [] [] z = refl
list-assoc [] (h :: y) z   = refl
list-assoc (h :: x ) y z   = let open ≡-Reasoning in begin
     append (append (h :: x) y) z
   ≡⟨⟩
      h :: (append (append x y) z)
   ≡⟨ cong (λ k → h :: k ) (list-assoc x y z) ⟩
     h :: (append x (append y z))
   ≡⟨⟩
     append (h :: x) (append y z)
   ∎

ListMonoid : (A : Set) → Category
ListMonoid A = record {
       Obj = One
    ;  Hom =  λ  a b → List A
    ;  _o_ = λ  f g  → append f g
    ;  id = λ  A  → []
    ;  isCategory = record {
           idL = refl
         ; idR = λ  {a} {b} {f} → idR {a} {b} f
         ; assoc = λ  {a} {b} {c} {d} {f} {g} {h} → sym (list-assoc f g h)
       }
   } where
      idR  : {a b : One {suc zero}} (f : List A) → append f [] ≡ f
      idR [] = refl
      idR {a} {b} (x :: y ) = cong ( λ  z → x :: z ) (idR y)

open Category

_[_o_] :  {l : Level} (C : Category {l} ) → {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
C [ f o g ] = Category._o_ C f g

--
--           f        g
--       a ----→ b -----→ c
--       |        |         |
--      T|       T|        T|
--       |        |         |
--       v        v         v
--      Ta ----→ Tb ----→ Tc
--           Tf       Tg


record IsFunctor {l : Level} (C D : Category {l} )
                 (FObj : Obj C → Obj D)
                 (FMap : {A B : Obj C} → Hom C A B → Hom D (FObj A) (FObj B))
                 : Set (suc l ) where
  field
    identity : {A : Obj C} →  FMap (id C A) ≡ id D (FObj A)
    distr : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
      → FMap ( C [ g o f ])  ≡ (D [ FMap g o FMap f ] )

record Functor {l : Level} (domain codomain : Category {l} )
  : Set (suc l) where
  field
    FObj : Obj domain → Obj codomain
    FMap : {A B : Obj domain} → Hom domain A B → Hom codomain (FObj A) (FObj B)
    isFunctor : IsFunctor domain codomain FObj FMap

open Functor

idFunctor : {l : Level } { C : Category {l} } → Functor C C
idFunctor = record {
        FObj = λ  x → x
     ;  FMap = λ  f → f
     ;  isFunctor = record {
           identity = refl
         ; distr = refl
       }
  }

open  import  Relation.Binary.PropositionalEquality hiding ( [_] )


_●_ : {l : Level} { A B C : Category {l} }  → ( S : Functor B C ) ( T : Functor A B ) →  Functor A C
_●_ {l} {A} {B} {C} S T  = record {
        FObj = λ  x → FObj S ( FObj T x )
     ;  FMap = λ  f → FMap S ( FMap T f )
     ;  isFunctor = record {
           identity = λ  {a} → identity a
         ; distr = λ  {a} {b} {c} {f} {g} → distr
       }
   } where
       identity :  (a : Obj A) → FMap S (FMap T (id A a)) ≡ id C (FObj S (FObj T a))
       identity a = let open ≡-Reasoning in begin
              FMap S (FMap T (id A a))
           ≡⟨ cong ( λ  z → FMap S z ) ( IsFunctor.identity (isFunctor T )  ) ⟩
              FMap S (id B (FObj T a) )
           ≡⟨ IsFunctor.identity (isFunctor S )  ⟩
              id C (FObj S (FObj T a))
           ∎
       distr : {a b c : Obj A} { f : Hom A a b } { g : Hom A b c } → FMap S (FMap T (A [ g o f ])) ≡ (C [ FMap S (FMap T g) o FMap S (FMap T f) ])
       distr {a} {b} {c} {f} {g} =  let open ≡-Reasoning in begin
               FMap S (FMap T (A [ g o f ]))
           ≡⟨ cong ( λ z → FMap S z ) ( IsFunctor.distr (isFunctor T )  ) ⟩
               FMap S (  B [ FMap T g o FMap T f ] )
           ≡⟨ IsFunctor.distr (isFunctor S )     ⟩
              C [ FMap S (FMap T g) o FMap S (FMap T f) ]
           ∎


--  {A : Set c₁ } {B : Set c₂ } → { f g : A → B }   →  f x  ≡ g x → f  ≡ g
postulate extensionality : { c₁ c₂ : Level}  → Extensionality c₂ c₂

ListFunctor : Functor Sets Sets 
ListFunctor = record {
        FObj = λ  x → List x
     ;  FMap = fmap
     ;  isFunctor = record {
            identity =  extensionality {zero} {zero} ( λ  x →  identity x )
          ; distr = λ  {a} {b} {c} {f} {g} →  extensionality {zero} {zero} ( λ  x →  distr x )
         }
  } where
      fmap :   {A B : Obj Sets} → Hom Sets A B → Hom Sets (List A) (List B)
      fmap f [] = []
      fmap f (x :: y) = ( f x ) :: fmap f y
      identity :  {A : Obj Sets} → ( x : List A ) → fmap (id Sets A) x ≡ id Sets (List A) x
      identity {A} [] = refl
      identity {A} (h :: t) = cong (_::_ h) (identity t)
      distr :  {a b c : Obj Sets} {f : Hom Sets a b} {g : Hom Sets b c} → (x : List a)  → fmap (Sets [ g o f ]) x ≡ (Sets [ fmap g o fmap f ]) x
      distr [] = refl
      distr {a} {b} {c} {f} {g} (h :: t ) =  let open ≡-Reasoning in begin
             fmap (Sets [ g o f ]) (h :: t)
           ≡⟨⟩
             g ( f h ) :: ( fmap (Sets [ g o f ]) t )
           ≡⟨  cong (_::_ (g (f h))) (distr t) ⟩
             g ( f h ) :: (( Sets [ fmap g o fmap f ])  t )
           ≡⟨⟩
             fmap g ( (f h) :: fmap f t) 
           ≡⟨⟩
             fmap g ( fmap f (h :: t) )
           ≡⟨⟩
             (Sets [ fmap g o fmap f ]) (h :: t)
           ∎

open import Data.Nat hiding ( suc ; zero )
test1 : List One
test1 = FMap ListFunctor ( λ x → * ) ( 1 :: (2 :: (3 :: [] )))

--
--            t a 
--      F a -----→ G a
--        |           |
--    Ff  |           | Gf
--        v           v
--      F b ------→ G b
--            t b
--

record IsNTrans  { l : Level } (D C : Category {l} ) ( F G : Functor D C )
                 (TMap : (A : Obj D) → Hom C (FObj F A) (FObj G A))
                 : Set (suc l) where
  field
    commute : {a b : Obj D} {f : Hom D a b} 
      →  C [ (  FMap G f ) o  ( TMap a ) ]  ≡ C [ (TMap b ) o  (FMap F f)  ] 

record NTrans  {l : Level} {domain codomain : Category {l} } (F G : Functor domain codomain )
       : Set (suc l) where
  field
    TMap :  (A : Obj domain) → Hom codomain (FObj F A) (FObj G A)
    isNTrans : IsNTrans domain codomain F G TMap


data  Tree  (A : Set ) : Set  where
   Leaf : A → Tree A
   Node  : A → Tree A → Tree A → Tree A

TreeFunctor : Functor Sets Sets 
TreeFunctor = record {
        FObj = λ  x → Tree x
     ;  FMap = fmap
     ;  isFunctor = record {
           identity = λ  {A} → extensionality {zero} ( λ  x → identity x ) 
         ; distr = extensionality {zero} ( λ  x → distr x )
        }
  } where
      fmap :   {A B : Obj Sets} → Hom Sets A B → Hom Sets (Tree A) (Tree B)
      fmap f (Leaf x) = Leaf (f x)
      fmap f (Node  x left right ) = Node (f x ) ( fmap f left ) (fmap f right )
      identity : {A : Set }  (x : Tree A ) → fmap (id Sets A) x ≡ id Sets (Tree A) x
      identity (Leaf x) = refl
      identity {A} (Node x left right ) =  let open ≡-Reasoning in begin
             fmap (id Sets A) (Node x left right)
           ≡⟨⟩
             Node x ( fmap (id Sets A) left )  ( fmap (id Sets A) right ) 
           ≡⟨ cong₂ (λ l r → Node x l r ) (identity left) (identity right) ⟩
             Node x left right
           ≡⟨⟩
             id Sets (Tree A) (Node x left right)
           ∎
      distr : {a b c : Obj Sets} {f : Hom Sets a b} {g : Hom Sets b c} ( x : Tree a ) → fmap (Sets [ g o f ]) x ≡ (Sets [ fmap g o fmap f ]) x
      distr {a} {b} {c} {f} {g} ( Leaf x ) = refl
      distr {a} {b} {c} {f} {g} ( Node x left right ) =  let open ≡-Reasoning in begin
              fmap (Sets [ g o f ]) (  Node x left right )
           ≡⟨⟩
              Node (g (f x)) (fmap (λ x₁ → g (f x₁)) left) (fmap (λ x₁ → g (f x₁)) right)
           ≡⟨ cong₂ (λ j k → Node (g (f x)) j k ) (distr left) (distr right) ⟩
              Node (g (f x)) (fmap g (fmap f left)) (fmap g (fmap f right))
           ≡⟨⟩
             (Sets [ fmap g o fmap f ])  (Node x left right )
           ∎


--
--              flatten a
--     Tree a  ------------→ List a
--       |                     |
--       |                     |
-- fmap f|                     |fmap f
--       |                     |
--       v                     v
--     Tree b  ------------→ List b
--              flatten b
--

flatten : {A : Set} → Tree A → List A
flatten ( Leaf a ) = a :: [] 
flatten ( Node a left right ) = append (flatten left ) ( append ( a :: [] ) (flatten right ))

appendF : {A B : Set } ( a b : List A ) { f : A → B } → FMap ListFunctor f (append a b ) ≡ append ( FMap ListFunctor f a )  ( FMap ListFunctor f b )
appendF [] b = refl
appendF (h :: t) b {f} = cong ( λ  z → ( f  h) :: z ) (appendF t b)

Tree→List : NTrans TreeFunctor ListFunctor
Tree→List = record {
       TMap = λ  a x → flatten {a} x
     ; isNTrans = record {
       commute =  extensionality {zero} ( λ  x → commute x )
     }
   } where
    commute :  {a b : Obj Sets} {f : Hom Sets a b} ( x : Tree a )
         → (Sets [ FMap ListFunctor f o flatten  ]) x ≡ (Sets [ flatten o FMap TreeFunctor f ]) x
    commute (Leaf x ) = refl
    commute {a} {b} {f} (Node x left right ) =  let open ≡-Reasoning in begin
              (Sets [ FMap ListFunctor f o flatten  ])  (Node x left right )
           ≡⟨⟩
              FMap ListFunctor f (append (flatten left) (x :: flatten right)) 
           ≡⟨ appendF (flatten left) (x :: flatten right) ⟩
              append (FMap ListFunctor f (flatten left)) (FMap ListFunctor f (x :: flatten right))
           ≡⟨ cong₂ append (commute left) (cong (λ z → f x :: z) (commute right)) ⟩
              append (flatten (FMap TreeFunctor f left)) (f x :: flatten (FMap TreeFunctor f right))
           ≡⟨⟩
              (Sets [ flatten o FMap TreeFunctor f ])  (Node x left right )
           ∎




open NTrans

--
--
--    η   : 1 ------→ T                          f : a → T b        f o g : a → T c =    TMap μ a o (FMap T g)
--    μ   : TT -----→ T
--
--        η                       μTT
--    T -----→ TT          TTT ------→ TT
--    |         |            |           |
-- Tη |         |μ        Tμ |           |Tμ
--    v         |            v           v
--   TT -----→ T           TT -------→ T
--        μ                       μT


record IsMonad {l : Level} { C : Category {l} } (T : Functor C C) ( η :  NTrans idFunctor T ) ( μ :  NTrans (T ● T) T )
      : Set (suc l) where
   field 
       assoc  : {a : Obj C} → C [ TMap μ a o TMap μ ( FObj T a ) ] ≡  C [  TMap μ a o FMap T (TMap μ a) ] 
       unity1 : {a : Obj C} → C [ TMap μ a o TMap η ( FObj T a ) ] ≡ id C (FObj T a) 
       unity2 : {a : Obj C} → C [ TMap μ a o (FMap T (TMap η a ))] ≡ id C (FObj T a) 


record Monad {l : Level} { C : Category {l} } (T : Functor C C) : Set (suc l) where
   field 
      η : NTrans idFunctor T
      μ :  NTrans (T ● T) T 
      isMonad : IsMonad T η μ

data maybe {c : Level}  (A : Set c) :  Set c where
    just :  A → maybe A
    nothing : maybe A

Maybe : Functor Sets Sets
Maybe = record {
      FObj = λ a → maybe a
    ; FMap = λ {a} {b} f → fmap f
    ; isFunctor = record {
          identity = extensionality {zero} ( λ  x → identity x )
        ; distr = extensionality {zero} ( λ  x → distr x )
      }
  } where
      fmap : { a b : Obj Sets } ( f : a → b ) → maybe a → maybe b
      fmap f ( just x ) = just (f x)
      fmap f nothing = nothing
      identity : {A : Obj Sets} → (x : maybe A)  → fmap (id Sets A) x ≡ id Sets (maybe A) x
      identity (just x) = refl
      identity nothing = refl
      distr : {a b c : Obj Sets} {f : Hom Sets a b} {g : Hom Sets b c} (x : maybe a) → fmap (Sets [ g o f ]) x ≡ (Sets [ fmap g o fmap f ]) x
      distr nothing = refl
      distr (just x) = refl


MaybeMonad : Monad Maybe
MaybeMonad = record {
       η  = record { TMap = λ  a x → just x ; isNTrans = record { commute = refl } }
    ;  μ  =  record { TMap = λ  a x → mu a x ; isNTrans = record { commute = extensionality {zero} ( λ  m → mu-commute m ) } }
    ;  isMonad = record {
         assoc = extensionality {zero} ( λ  m → assoc m )
       ; unity1 = extensionality {zero} ( λ  m → unity1 m )
       ; unity2 =  extensionality {zero} ( λ  m → unity2 m )
     }
  } where  -- NTrans (Maybe ● Maybe) Maybe
      mu : (a : Obj Sets) ( x : maybe ( maybe a ) ) → FObj Maybe a
      mu _ nothing = nothing
      mu _ (just nothing) =  nothing
      mu _ (just (just x)) = just x 
      mu-commute : {a b : Obj Sets} {f : Hom Sets a b} → (m : maybe (maybe a) )
         → (Sets [ FMap Maybe f o (λ x → mu a x) ]) m ≡ (Sets [ (λ x → mu b x) o FMap (Maybe ● Maybe) f ]) m
      mu-commute nothing = refl
      mu-commute (just nothing) = refl
      mu-commute (just (just x)) = refl
      assoc :  {a : Obj Sets} → (x : maybe ( maybe ( maybe a)))
          →  (Sets [ (λ x → mu a x) o (λ x → mu (FObj Maybe a) x) ]) x ≡ (Sets [ (λ x → mu a x) o FMap Maybe (λ x → mu a x) ]) x
      assoc nothing = refl
      assoc (just nothing) = refl
      assoc (just (just nothing)) = refl
      assoc (just (just (just x))) = refl
      unity1 : {a : Obj Sets} → (x : maybe a) → (Sets [ (λ x → mu a x) o (λ x → just x) ]) x ≡ id Sets (FObj Maybe a) x
      unity1 nothing = refl
      unity1 (just x) = refl
      unity2 : {a : Obj Sets} → (x : maybe a) → (Sets [ (λ x → mu a x) o FMap Maybe (λ x → just x) ]) x ≡ id Sets (FObj Maybe a) x
      unity2 nothing = refl
      unity2 (just x) = refl

ListMonad : Monad ListFunctor
ListMonad = record {
       η  = record { TMap = λ  a x → x :: [] ; isNTrans = record { commute = refl } }
    ;  μ  = record { TMap = λ  a x → mu a x ; isNTrans = record { commute =   extensionality {zero} ( λ  ll → mu-commute ll ) } }
    ;  isMonad = record {
         assoc =  λ  {a} → extensionality {zero} ( λ  m → assoc m )
       ; unity1 =  extensionality {zero} ( λ  m → unity1 m )
       ; unity2 =  extensionality {zero} ( λ  m → unity2 m )
     }
  } where
      mu : (a : Obj Sets) ( x : List ( List a ) ) → List a
      mu a [] = []
      mu a (h :: t ) = append h ( mu a t )
      mu-commute :  {a b : Obj Sets} {f : Hom Sets a b} → ( x : List ( List a ) ) 
          → (Sets [ FMap ListFunctor f o (λ x → mu a x) ]) x ≡ (Sets [ (λ x → mu b x) o FMap (ListFunctor ● ListFunctor) f ]) x
      mu-commute [] = refl
      mu-commute {a} {b} {f} (h :: t ) =  let open ≡-Reasoning in begin
              FMap ListFunctor f (append h (mu a t))
           ≡⟨  ? ⟩
              append (FMap ListFunctor f h) (mu b (FMap ListFunctor (FMap ListFunctor f) t))
           ∎
      assoc :  {a : Obj Sets } ( m : List ( List ( List a )))
         → (Sets [ (λ x → mu a x) o (λ x → mu (FObj ListFunctor a) x) ]) m ≡ (Sets [ (λ x → mu a x) o FMap ListFunctor (λ x → mu a x) ]) m
      assoc x = {!!}
      unity1 : {a : Obj Sets} → (m : List a) → (Sets [ (λ x → mu a x) o (λ x → x :: []) ]) m ≡ id Sets (FObj ListFunctor a) m
      unity1 x = {!!}
      unity2 : {a : Obj Sets} → (m : List a) → (Sets [ (λ x → mu a x) o FMap ListFunctor (λ x → x :: []) ]) m ≡ id Sets (FObj ListFunctor a) m
      unity2 x = {!!}



record KleisliHom { c : Level} { A : Category {c} } { T : Functor A A } (a : Obj A)  (b : Obj A)
      : Set c where
    field
        KMap :  Hom A a ( FObj T b )

open KleisliHom

                          
right-x : { a b c  : Set } {h1 h2 : a → b } → h1 ≡ h2 →  { f : b → c } → {x : a} → f (h1 x) ≡ f (h2 x)
right-x eq {f} {x}  = cong (λ k → f k) (cong (λ k → k x) eq)

left-x : { a b  : Set } {h1 h2 : a → b } → h1 ≡ h2 →  {x : a} → h1 x ≡ h2 x
left-x eq {x}  = cong (λ k → k x) eq

KleisliSets : {l : Level}  (T : Functor Sets Sets) ( M : Monad T ) → Category {Level.zero}
KleisliSets {l} T M = record {
       Obj = Set 
    ;  Hom = λ  a b → a → (FObj T b)    -- a → T b
    ;  _o_ = λ  {a} {b} {c} f g  → Sets [ TMap μ c o Sets [ FMap T f o g ] ]   -- μ ( fmap f ( g x ))
    ;  id = λ  a  → TMap η a
    ;  isCategory = record {
            idL = idL
          ; idR = idR
          ; assoc = assoc
       }
  } where
      open Monad M
      nat  = IsNTrans.commute (isNTrans  (Monad.μ M) )
      idL  : {a b : Set} {f : a → FObj T b} → Sets [ TMap μ b o Sets [ FMap T (TMap η b) o f ] ]  ≡ f
      idL {a} {b} {f} = extensionality {zero} ( λ x  → begin
          TMap μ b (FMap T (TMap η b) (f x))
        ≡⟨ cong (λ k → k (f x) ) ( IsMonad.unity2 (Monad.isMonad M ) ) ⟩
          f x
        ∎ ) where open  ≡-Reasoning 
      idR  : {a b : Set} {f : a → FObj T b} → Sets [ TMap μ b o Sets [ FMap T f o TMap η a ] ]  ≡ f
      idR {a} {b} {f} = extensionality {zero} ( λ x  → begin
          TMap μ b (FMap T f (TMap η a x) )
        ≡⟨ cong (λ k → TMap μ b (k x) ) (IsNTrans.commute (isNTrans  (Monad.η M) )) ⟩
          TMap μ b (TMap η (FObj T b) (f x)) 
        ≡⟨ cong (λ k → (λ y → k y ) (f x )) ( IsMonad.unity1 (Monad.isMonad M ) ) ⟩
          f x
        ∎ ) where open  ≡-Reasoning 
      assoc : {a b c d : Set} {f : c → FObj T d} {g : b → FObj T c}
            {h : a → FObj T b} → (Sets o TMap μ d) ((Sets o FMap T f) ((Sets o TMap μ c) ((Sets o FMap T g) h)))
              ≡ (Sets o TMap μ d) ((Sets o FMap T ((Sets o TMap μ d) ((Sets o FMap T f) g))) h)
      assoc {a} {b} {c} {d} {f} {g} {h}  =  extensionality {zero} ( λ  m  → begin
           TMap μ d (FMap T f (TMap μ c (FMap T g (h m))))
        ≡⟨ right-x nat {TMap μ d} {FMap T g (h m)} ⟩
           TMap μ d (TMap μ (FObj T d) (FMap (T ● T) f (FMap T g (h m)))) 
        ≡⟨⟩
           TMap μ d (TMap μ (FObj T d) (FMap T (FMap T f ) (FMap T g (h m)))) 
        ≡⟨ left-x (IsMonad.assoc (Monad.isMonad M ) ) {FMap T (FMap T f) (FMap T g (h m))} ⟩
           TMap μ d (FMap T (TMap μ  d) (FMap T (FMap T f ) (FMap T g (h m)))) 
        ≡⟨ sym (right-x (IsFunctor.distr (isFunctor T )) {λ x → TMap μ d x } ) ⟩
           TMap μ d (FMap T (λ x → TMap μ d (FMap T f x)) (FMap T g (h m)))
        ≡⟨ sym (right-x (IsFunctor.distr (isFunctor T )) {λ x → TMap μ d x } ) ⟩
           TMap μ d (FMap T (λ x → TMap μ d (FMap T f (g x))) (h m))
        ∎ ) where open  ≡-Reasoning 
      --     f ∙ ( g ∙ h )
      --
      --        TMap (Monad.μ M) d ・ (  FMap T f ・ (  TMap (Monad.μ M) c ・ (  FMap T g ・ h ) ) ) ) 
      --
      --      h                T g                       μ c          
      --   a ---→ T b -----------------→ T T c -------------------------→ T c 
      --            |                       |                                |
      --            |                       |                                |
      --            |                       | T T f     NAT μ                | T f
      --            |                       |                                |
      --            |                       v            μ (T d)             v  
      --            |      distr T       T T T d -------------------------→ T T d 
      --            |                       |                                |
      --            |                       |                                |
      --            |                       | T μ d     Monad-assoc          | μ d
      --            |                       |                                |
      --            |                       v                                v
      --            +------------------→ T T d -------------------------→ T d 
      --               T (μ d・T f・g)                   μ d
      --
      --        TMap (Monad.μ M) d ・ (  FMap T (( TMap (Monad.μ M) d ・ (  FMap T f ・ g ) ) ) ・ h ) )  
      --
      --     (f ∙  g ) ∙ h 


data T1  (M : Set  )  (A : Set ) :  Set  where
    T :  List M → A → T1 M A

FunctorT1 : (M : Set ) → Functor Sets Sets
FunctorT1 M = record {
     FObj = λ  x → T1 M x
   ; FMap = λ  {a} {b} f → fmap f
   ; isFunctor = record {
          identity = λ  {A} → extensionality {zero} ( λ  x → identity x )
       ;  distr = λ {a} {b} {c} {f} {g} →  extensionality {zero} ( λ  x → distr f g x )
     }
  } where
     fmap : {a b : Obj Sets} (f : a → b ) → T1 M a → T1 M b
     fmap f (T m x) = T m (f x)
     identity : { A : Obj Sets } ( x : T1 M A ) → fmap (id Sets A) x ≡ id Sets (T1 M A) x
     identity (T m x) = refl
     distr : {a b c : Obj Sets} (f : a → b ) (g : b → c) ( x : T1 M a ) → fmap (Sets [ g o f ]) x ≡ (Sets [ fmap g o fmap f ]) x
     distr f g (T m x) = refl

T1Monad : (M : Set) → Monad (FunctorT1 M)
T1Monad M = record {
         η  = record { TMap = λ  a x → T [] x  ; isNTrans = record { commute = refl } }
      ;  μ  = record { TMap = λ  a x → mu a x ; isNTrans = record { commute =   extensionality {zero} ( λ  tt →  mu-commute tt ) } }
      ;  isMonad = record {
                 assoc =  extensionality {zero} ( λ  m → assoc m )
               ; unity1 =  extensionality {zero} ( λ  m → unity1 m )
               ; unity2 =  extensionality {zero} ( λ  m → unity2 m )
     }} where
         mu : (a : Obj Sets) (x :  T1 M ( T1 M a ) ) → (T1 M a )
         mu a (T m (T m' x) ) = T (append m m') x
         mu-commute : {a b : Obj Sets} {f : a → b } ( tt : T1 M ( T1 M a ) )
                    → (Sets [ FMap (FunctorT1 M) f o (λ x → mu a x) ]) tt ≡ (Sets [ (λ x → mu b x) o FMap (FunctorT1 M ● FunctorT1 M) f ]) tt
         mu-commute {a} {b} {f} (T m (T m' x) ) = let open ≡-Reasoning in begin
              (Sets [ FMap (FunctorT1 M) f o mu a ]) (T m (T m' x))
           ≡⟨⟩
              T (append m m') (f x)
           ≡⟨⟩
              (Sets [ mu b o FMap (FunctorT1 M ● FunctorT1 M) f ]) (T m (T m' x))
           ∎
         assoc :  {a : Obj Sets } ( m : T1 M ( T1 M ( T1 M a )))
                 → (Sets [ (λ x → mu a x) o (λ x → mu (FObj (FunctorT1 M) a) x) ]) m ≡ (Sets [ (λ x → mu a x) o FMap (FunctorT1 M) (λ x → mu a x) ]) m
         assoc {a} ( T m ( T m' ( T m'' x ) ) ) = let open ≡-Reasoning in begin
              T (append (append m m') m'') x
           ≡⟨ cong ( λ  z → T z x ) ( list-assoc m m' m'' ) ⟩
              T (append m (append m' m'')) x
           ∎
         unity1 : {a : Obj Sets} → (m : T1 M a) → (Sets [ (λ x → mu a x) o (λ x → T [] x) ]) m ≡ id Sets (FObj (FunctorT1 M) a) m
         unity1  x = {!!}
         app-tail : {a : Obj Sets} ( t : List a ) → append t [] ≡ t
         app-tail [] = refl
         app-tail (h :: t) = cong ( λ  z → h :: z ) ( app-tail t )
         unity2 : {a : Obj Sets} → (m : T1 M a) → (Sets [ (λ x → mu a x) o FMap (FunctorT1 M) (λ x → T [] x) ]) m ≡ id Sets (FObj (FunctorT1 M) a) m
         unity2 x = {!!} 


--- advanced topic

record MonadCompositable (M N : Functor Sets Sets ) : Set (suc zero) where
   field
      nm→mn : {a : Set } → FObj (N ● M) a → FObj (M ● N) a
      mc : Monad M
      nc : Monad N

open Monad
open MonadCompositable

lemma : (M N : Functor Sets Sets ) → MonadCompositable M N →  Monad ( M ● N )
lemma M N C = record {
         η  = record { TMap = λ a → Sets [ TMap (η (mc C)) (FObj N a) o TMap (η (nc C)) a ] ; isNTrans = {!!} }
      ;  μ  = record { TMap = λ a → mn-mu ; isNTrans = {!!} }
      ;  isMonad = record {
                 assoc =  extensionality {zero} ( λ  m → {!!} )
               ; unity1 =  extensionality {zero} ( λ  m → {!!} )
               ; unity2 =  extensionality {zero} ( λ  m → {!!} )
      }
  } where
      mn-mu : {a : Set } → FObj ((M ● N) ● (M ● N)) a → FObj (M ● N) a
      mn-mu {a} mnmn = {!   !}
 
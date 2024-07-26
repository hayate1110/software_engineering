module stdalone-kleisli where

open import Level
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality hiding ( [_] ; sym )

--        h       g       f
--     a ---→ b ---→ c ---→ d
--
--       f ( g ( h x ) )   -- x 
--       (f o g) o h    
--       f o (g o h)
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
        FObj = λ x → x
     ;  FMap = λ f → f
     ;  isFunctor = record {
           identity = refl
         ; distr = refl
       }
  }

open  import  Relation.Binary.PropositionalEquality hiding ( [_] )


_●_ : {l : Level} { A B C : Category {l} }  → ( S : Functor B C ) ( T : Functor A B ) →  Functor A C
_●_ {l} {A} {B} {C} S T  = record {
        FObj = λ x → FObj S ( FObj T x )
     ;  FMap = λ f → FMap S ( FMap T f )
     ;  isFunctor = record {
           identity = λ {a} → identity a
         ; distr = λ {a} {b} {c} {f} {g} → distr
       }
   } where
       identity :  (a : Obj A) → FMap S (FMap T (id A a)) ≡ id C (FObj S (FObj T a))
       identity a = let open ≡-Reasoning in begin
              FMap S (FMap T (id A a))
           ≡⟨ cong ( λ z → FMap S z ) ( IsFunctor.identity (isFunctor T )  ) ⟩
              FMap S (id B (FObj T a) )
           ≡⟨ IsFunctor.identity (isFunctor S )   ⟩
              id C (FObj S (FObj T a))
           ∎
       distr : {a b c : Obj A} { f : Hom A a b } { g : Hom A b c } → FMap S (FMap T (A [ g o f ])) ≡ (C [ FMap S (FMap T g) o FMap S (FMap T f) ])
       distr {a} {b} {c} {f} {g} =  let open ≡-Reasoning in begin
               FMap S (FMap T (A [ g o f ]))
           ≡⟨ cong ( λ z → FMap S z ) ( IsFunctor.distr (isFunctor T )  ) ⟩
               FMap S (  B [ FMap T g o FMap T f ] )
           ≡⟨  IsFunctor.distr (isFunctor S )    ⟩
              C [ FMap S (FMap T g) o FMap S (FMap T f) ]
           ∎


--  {A : Set c₁ } {B : Set c₂ } → { f g : A → B }   → (x : A) →  f x  ≡ g x → f  ≡ g
-- import Axiom.Extensionality.Propositional
-- postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m

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
      →  C [  FMap G f  o   TMap a  ]  ≡ C [ TMap b  o  FMap F f  ] 

record NTrans  {l : Level} {domain codomain : Category {l} } (F G : Functor domain codomain )
       : Set (suc l) where
  field
    TMap :  (A : Obj domain) → Hom codomain (FObj F A) (FObj G A)
    isNTrans : IsNTrans domain codomain F G TMap



open NTrans

--
--
--    η   : 1 ------→ T
--    μ   : TT -----→ T
--
--        η                       μT
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
      η : NTrans idFunctor T      -- constructor
      μ :  NTrans (T ● T) T     
      isMonad : IsMonad T η μ

                          
Left : {l : Level} (C : Category {l} ) {a b c : Obj C } {f f' : Hom C b c } {g : Hom C a b } →  f ≡ f' → C [ f  o g ] ≡ C [ f'  o g ]
Left {l} C {a} {b} {c} {f} {f'} {g} refl = cong ( λ z → C [ z  o g  ] ) refl

Right : {l : Level} (C : Category {l} ) {a b c : Obj C } {f : Hom C b c } {g g' : Hom C a b } →  g ≡ g' → C [ f  o g ] ≡ C [ f  o g' ]
Right {l} C {a} {b} {c} {f} {g} {g'} refl = cong ( λ z → C [ f  o z  ] ) refl

Assoc : {l : Level} (C : Category {l} ) {a b c d : Obj C } {f : Hom C c d } {g : Hom C b c } { h : Hom C a b }
   → C [ f  o C [ g  o h ] ]  ≡ C [ C [ f   o g ] o h ]
Assoc {l} C = IsCategory.assoc ( isCategory C )


Kleisli : {l : Level} (C : Category {l} ) (T : Functor C C ) ( M : Monad T ) → Category {l}
Kleisli C T M = record {
       Obj = Obj C 
    ;  Hom = λ a b → Hom C a ( FObj T b )   -- a → T b
    ;  _o_ = λ {a} {b} {c} f g  → join {a} {b} {c} f g
    ;  id = λ a  → TMap (Monad.η M) a 
    ;  isCategory = record {
            idL = idL
          ; idR = idR
          ; assoc = assoc
       }
  } where
      join : { a b c : Obj C } → (f : Hom C b ( FObj T c )) → (g : Hom C a ( FObj T b )) → Hom C a ( FObj T c )
      join {a} {b} {c} f g = C [ TMap (Monad.μ M) c o  C [ FMap T f o  g  ] ] 
      idL : {a b : Obj C} {f : Hom C a ( FObj T b )} → join ( TMap (Monad.η M) b) f ≡ f
      idL {a} {b} {f} =  let open ≡-Reasoning in begin
               C [  TMap (Monad.μ M) b o C [  FMap T (TMap (Monad.η M) b) o f ] ] 
           ≡⟨ cong ( λ z → z  ) ( begin
                C [  TMap (Monad.μ M) b o C [  FMap T (TMap (Monad.η M) b) o f ] ]
             ≡⟨ IsCategory.assoc ( isCategory C ) ⟩
                C [  C [ TMap (Monad.μ M) b o  FMap T (TMap (Monad.η M) b) ] o f  ]
             ≡⟨ cong ( λ z → C [ z  o f ] ) ( IsMonad.unity2 (Monad.isMonad M )  )   ⟩
                C [ id C (FObj T b) o f  ]
             ≡⟨ IsCategory.idL ( isCategory C ) ⟩
                f
             ∎ ) ⟩
              f
            ∎
      idR : {a b : Obj C} {f : Hom C a ( FObj T b ) } → join f (TMap (Monad.η M) a ) ≡ f
      idR {a} {b} {f} =  let open ≡-Reasoning in begin
               C [ TMap (Monad.μ M) b o C [ FMap T (f) o TMap (Monad.η M) a ] ]  
           ≡⟨ cong ( λ z → z  ) ( begin
                C [ TMap (Monad.μ M) b o C [ FMap T (f) o TMap (Monad.η M) a ] ]
             ≡⟨  cong ( λ z → C [ TMap (Monad.μ M) b  o z ] ) ( IsNTrans.commute (isNTrans  (Monad.η M) ))  ⟩
                C [ TMap (Monad.μ M) b o C [ TMap (Monad.η M) (FObj T b) o  f  ] ]
             ≡⟨  IsCategory.assoc ( isCategory C )  ⟩
                C [ C [ TMap (Monad.μ M) b o TMap (Monad.η M) (FObj T b) ] o  f  ] 
             ≡⟨ cong ( λ z → C [ z  o f ] ) ( IsMonad.unity1 (Monad.isMonad M )  )  ⟩
                C [ id C  (FObj T b)  o  f  ] 
             ≡⟨ IsCategory.idL ( isCategory C )  ⟩
                f
             ∎ ) ⟩
              f
           ∎
      --
      --        TMap (Monad.μ M) d ・ (  FMap T (KMap f) ・ (  TMap (Monad.μ M) c ・ (  FMap T (KMap g) ・ KMap h ) ) ) ) 
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
      --        TMap (Monad.μ M) d ・ (  FMap T (( TMap (Monad.μ M) d ・ (  FMap T (KMap f) ・ KMap g ) ) ) ・ KMap h ) )  
      --
      _・_ : {a b c : Obj C } ( f : Hom C b c ) ( g : Hom C a b ) → Hom C a c
      f ・ g  = C [ f  o g ]
      assoc :  {a b c d : Obj C} {f : Hom C c ( FObj T d ) } {g : Hom C b ( FObj T c ) } {h : Hom C a ( FObj T b ) }
          → join f (join g h) ≡ join (join f g) h
      assoc {a} {b} {c} {d} {f} {g} {h} =  let open ≡-Reasoning in begin
            join f (join g h)
         ≡⟨⟩
             TMap (Monad.μ M) d ・ ( FMap T ( f) ・ ( TMap (Monad.μ M) c ・ ( FMap T ( g) ・   h ))) 
         ≡⟨ cong ( λ z →  z  ) ( begin
                 (  TMap (Monad.μ M) d ・ (  FMap T ( f) ・ (  TMap (Monad.μ M) c ・ (  FMap T ( g) ・  h ) ) ) ) 
             ≡⟨ Right C ( Right C (Assoc C)) ⟩
                 (  TMap (Monad.μ M) d ・ (  FMap T ( f) ・ (  ( TMap (Monad.μ M) c ・ FMap T ( g) ) ・  h ) ) ) 
             ≡⟨  Assoc C  ⟩
                 ( (  TMap (Monad.μ M) d ・  FMap T ( f) ) ・  ( ( TMap (Monad.μ M) c ・ FMap T ( g) ) ・  h ) ) 
             ≡⟨  Assoc C  ⟩
                 ( ( ( TMap (Monad.μ M) d ・  FMap T ( f) ) ・  ( TMap (Monad.μ M) c ・ FMap T ( g) ) )  ・  h  ) 
             ≡⟨ sym ( Left  C (Assoc C )) ⟩
                 ( (  TMap (Monad.μ M) d  ・ (  FMap T ( f)  ・  ( TMap (Monad.μ M) c ・ FMap T ( g) ) ) )  ・  h  ) 
             ≡⟨ Left C ( Right C (Assoc C)) ⟩
                 ( (  TMap (Monad.μ M) d  ・ ( ( FMap T ( f)   ・  TMap (Monad.μ M) c )  ・  FMap T ( g)  ) ) ・  h  ) 
             ≡⟨ Left C (Assoc C)⟩
                 ( (  ( TMap (Monad.μ M) d  ・  ( FMap T ( f)   ・  TMap (Monad.μ M) c ) )  ・  FMap T ( g)  ) ・  h  ) 
             ≡⟨ Left C ( Left C ( Right C  ( IsNTrans.commute (isNTrans  (Monad.μ M) )  ) ))  ⟩
                ( ( ( TMap (Monad.μ M) d ・ ( TMap (Monad.μ M) (FObj T d) ・ FMap (T ● T) ( f) ) ) ・ FMap T ( g) ) ・  h )
             ≡⟨ sym ( Left  C (Assoc C)) ⟩
                ( ( TMap (Monad.μ M) d ・ ( ( TMap (Monad.μ M) (FObj T d) ・ FMap (T ● T) ( f) ) ・ FMap T ( g) ) ) ・  h )
             ≡⟨ sym ( Left C ( Right  C (Assoc C))) ⟩
                ( ( TMap (Monad.μ M) d ・ ( TMap (Monad.μ M) (FObj T d) ・ ( FMap (T ● T) ( f) ・ FMap T ( g) ) ) ) ・  h )
             ≡⟨ sym ( Left C ( Right C (Right C (IsFunctor.distr (isFunctor T ) ) ) )) ⟩
                ( ( TMap (Monad.μ M) d ・ ( TMap (Monad.μ M) (FObj T d) ・ FMap T (( FMap T ( f) ・  g )) ) ) ・  h )
             ≡⟨ Left C (Assoc C)  ⟩
                ( ( ( TMap (Monad.μ M) d ・ TMap (Monad.μ M) (FObj T d) ) ・ FMap T (( FMap T ( f) ・  g )) ) ・  h )
             ≡⟨ Left C (Left C ( IsMonad.assoc (Monad.isMonad M ) ) ) ⟩
                ( ( ( TMap (Monad.μ M) d ・ FMap T (TMap (Monad.μ M) d) ) ・ FMap T (( FMap T ( f) ・  g )) ) ・  h )
             ≡⟨ sym ( Left C (Assoc C)) ⟩
                ( ( TMap (Monad.μ M) d ・ ( FMap T (TMap (Monad.μ M) d) ・ FMap T (( FMap T ( f) ・  g )) ) ) ・  h )
             ≡⟨ sym (Assoc C) ⟩
                ( TMap (Monad.μ M) d ・ ( ( FMap T (TMap (Monad.μ M) d) ・ FMap T (( FMap T ( f) ・  g )) ) ・  h ) )
             ≡⟨ sym (Right C ( Left C (IsFunctor.distr (isFunctor T ))))  ⟩
                 (  TMap (Monad.μ M) d ・ (  FMap T (( TMap (Monad.μ M) d ・ (  FMap T ( f) ・  g ) ) ) ・  h ) )  
             ∎ ) ⟩
            (  TMap (Monad.μ M) d ・ (  FMap T (( TMap (Monad.μ M) d ・ (  FMap T ( f) ・  g ) ) ) ・  h ) )  
         ≡⟨⟩
            join (join f g) h
         ∎


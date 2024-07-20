module DAG where

--         f0         f1
--       -----→     -----→
--    t0         t1         t2

data ThreeObject : Set where
    t0 : ThreeObject
    t1 : ThreeObject
    t2 : ThreeObject
data TwoArrow : ThreeObject → ThreeObject → Set where
    f0 : TwoArrow t0 t1
    f1 : TwoArrow t1 t2

--         r0         r1       
--       -----→     -----→
--    t0        t1          t2
--       ←----------------
--              r2

data Circle : ThreeObject → ThreeObject → Set where
    r0 : Circle t0 t1
    r1 : Circle t1 t2
    r2 : Circle t2 t0

-- 矛盾は、constructorのないdata型として定義される。
data ⊥ : Set where

-- 矛盾からはなんでも出てくる。
-- ()は起きない場合分けを表す。
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- 否定を以下のように定義する。
¬_ : Set → Set
¬ A = A → ⊥

-- 有向グラフのedgeをたどって、到達できるvertexを到達可能(connected)という。
-- 直接つながっている場合と、間接的につながっている場合がある。それを場合分けしよう。
data connected {V : Set} (E : V → V → Set) (x y : V) : Set where
    direct : E x y → connected E x y
    indirect : {z : V} → E x z → connected {V} E z y → connected E x y

lemma1 : connected TwoArrow t0 t1
lemma1 = direct f0

lemma2 : connected TwoArrow t0 t2
lemma2 = indirect f0 (direct f1)

lemma3 : ¬ (connected TwoArrow t1 t0)
lemma3 (direct ())
lemma3 (indirect f1 (direct ()))

dag : {V : Set} (E : V → V → Set) → Set
dag {V} E = ∀ (n : V) → ¬ (connected E n n)

lemma4 : dag TwoArrow
lemma4 t0 (direct ())
lemma4 t0 (indirect f0 (direct ()))
lemma4 t0 (indirect f0 (indirect f1 (direct ())))

lemma5 : connected Circle t0 t0
lemma5 = indirect r0 (indirect r1 (direct r2))

lemma6 : dag Circle → ⊥
lemma6 x = ⊥-elim (x t0 lemma5)
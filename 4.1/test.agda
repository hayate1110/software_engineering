module test (A B C : Set) where

{-
record ∧ (A B : Set) : Set where
    field
        and1 : A
        and2 : B
-}

data _∧_ (A B : Set) : Set where
    and : A → B → A ∧ B

l1 : A → A
l1 a = a

l2 : A → (B → A)
l2 a = λ b → a

lemma31 : (A ∧ (A → B)) → (A → B)
lemma31 (and a f) = f

lemma32 : (A ∧ (A → B)) → A
lemma32 (and a f) = a

lemma33 : A → (A → B) → B --Aと、AからBを返す関数を受け取り、AからBを返す関数に、Aを入力して、Bを得る
lemma33 a f = f a

l3 : (A ∧ (A → B)) → B
l3 x = lemma33 (lemma32 x) (lemma31 x)

l4 : B → (B ∧ (A → B))
l4 b = and b (λ a → b)
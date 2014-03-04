module 5-Proofs where

open import 5-Basics using (ℕ; suc; zero; _+_; Bool; true; false; ¬; _∧_)
-- data types
--
infixr 10 _∷_

data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)


-- functions
--
_++_ : ∀ {A n m} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


-- Equality
--
infix 2 _≡_

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
--  trans : { x y z : A } → x ≡ y → y ≡ z → x ≡ z

-- data _≡_ {A : Set} (x : A) : A → Set where
--   refl : x ≡ x

3equals3 : 3 ≡ 3
3equals3 = refl

n-equals-n : {n : ℕ} → n ≡ n
n-equals-n = refl

-- λ x → x + y 

-- x-equals-x : ∀ {A x} → x ≡ x  -- Doesn't work. It's not clear how x, A, and Set are related!
x-equals-x : {A : Set} {x : A} → x ≡ x
x-equals-x = refl

true-equals-true : true ≡ true
true-equals-true = x-equals-x

suc-equals-suc : {n : ℕ} → suc n ≡ suc n
suc-equals-suc = refl

0-isLeftNeutral : {n : ℕ} → 0 + n ≡ n
0-isLeftNeutral = refl

neg-cancel : ∀ {b} -> ¬ (¬ b) ≡ b
neg-cancel {true}  = refl
neg-cancel {false} = refl


-- congruence
--
cong : {A B : Set} (f : A → B) → {x : A} → {y : A} → x ≡ y → f x ≡ f y
cong f refl = refl
-- cong f trans = trans

0-isRightNeutral : {n : ℕ} → n + 0 ≡ n
0-isRightNeutral {zero}  = refl 
0-isRightNeutral {suc n} = cong suc (0-isRightNeutral {n})

{-
_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
-}

{-
  0-isRightNeutral {zero}
= refl : 0 + 0 ≡ 0  ~  0 + 0 ≡ 0
= refl :     0 ≡ 0  ~      0 ≡ 0  {+.1}

  0-isRightNeutral {suc n}
= cong suc (0-isRightNeutral {n})  ~  suc n + 0 ≡ suc n
= cong suc (p : n + 0 ≡ n)         ~  suc n + 0 ≡ suc n
= cong suc (p : n + 0 ≡ n)         ~  suc (n + 0) ≡ suc n  {+.2}
= p : suc (n + 0) ≡ suc n          ~  suc (n + 0) ≡ suc n

-}



{-
lemma : (n m : ℕ) → n + (suc m) ≡ suc n + m
lemma zero    m = refl
lemma (suc n) m = cong suc (lemma n m)
-}
{-
lemma : (n : ℕ) → n + (suc 0) ≡ suc n 
lemma zero    = refl
lemma (suc n) = cong suc (lemma n)
-}
lemma : {n : ℕ} → n + (suc 0) ≡ suc n 
lemma {zero}  = refl
lemma {suc n} = cong suc (lemma {n})

{-
  lemma {suc n}
= cong suc (lemma {n})                 ~  suc n + (suc 0) ≡ suc (suc n)
= cong suc (p : n + (suc 0) ≡ suc n)   ~  suc n + (suc 0) ≡ suc (suc n)
= p : suc (n + (suc 0)) ≡ suc (suc n)  ~  suc n + (suc 0) ≡ suc (suc n)
= p : suc (n + (suc 0)) ≡ suc (suc n)  ~  suc (n + (suc 0)) ≡ suc (suc n)   {+.2}

-}


subst : {A : Set} → (P : A → Set) → ∀{x y} → x ≡ y → P x → P y
subst P refl p = p

vec : ∀ {A} (k : ℕ) → Set
vec {A} k = Vec A k

reverse : ∀ {A n} → Vec A n → Vec A n
reverse []       = []
reverse {A} {suc n} (x ∷ xs) = subst (λ k → Vec A k) (lemma {n}) (reverse xs ++ ( x  ∷ []))
-- reverse {A} {suc n} (x ∷ xs) = subst vec (lemma {n}) (reverse xs ++ ( x  ∷ []))
-- reverse (x ∷ xs) = reverse xs ++ (x  ∷ []) -- Doesn't work!

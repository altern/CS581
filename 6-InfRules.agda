module 6-InfRules where


open import 5-Basics using 
     (ℕ; suc; zero; _=ℕ_; 
      Bool; true; false; _∧_;
      List; []; _∷_)

-- example relations
--
data Even : ℕ → Set where
  0-even : Even 0
  sucsuc : ∀ {n} → Even n → Even (suc (suc n))
{-
  sucsuc : ∀ {n} → 

                  Even n      → 
           ------------------
           Even (suc (suc n))
-}


data _<_ : ℕ → ℕ → Set where
  <-suc   : ∀ {n} → n < suc n
  <-trans : ∀ {k n m} → k < n → n < m → k < m
{-
  <-trans : ∀ {k n m} → 

            k < n   →    n < m   → 
            --------------------
                 k < m
-}


data Term : Set where
  true : Term
  false : Term
  not : Term → Term
  if_then_else_ : (t₁ t₂ t₃ : Term) → Term 


-- CT : "Contains a True constant"
--
data CT : Term → Set where
  true-CT : CT true
  not-CT  : ∀ {t} → CT t → CT (not t)
  if-CT-1 : ∀ {t₁ t₂ t₃} → CT t₁ → CT (if t₁ then t₂ else t₃)
  if-CT-2 : ∀ {t₁ t₂ t₃} → CT t₂ → CT (if t₁ then t₂ else t₃)
  if-CT-3 : ∀ {t₁ t₂ t₃} → CT t₃ → CT (if t₁ then t₂ else t₃)


-- example expression and functions
--
one = suc zero
two = suc one
three = suc two

even : ℕ → Bool
even 0 = true
even 1 = false
even (suc (suc n)) = even n

_<'_ : ℕ → ℕ → Bool
zero  <' suc _ = true
suc n <' suc m = n <' m
_     <' zero  = false


-- some lemmas and theorems
--
2-is-even : Even 2
2-is-even = sucsuc (0-even)

-- 0<1 : zero < one
0<1 : 0 < 1
0<1 = <-suc
-- 0<1 = <-suc {0}

lemma : 0 < 2
-- lemma = <-trans 0<1 <-suc
-- lemma = <-trans <-suc <-suc
-- lemma = <-trans 0<1 0<1 -- INCORRECT
lemma = <-trans 0<1 <-suc
-- lemma = <-trans 0<1 (<-suc {1})
-- lemma = <-trans 0<1 (<-suc {0}) -- INCORRECT
 
0-is-less-than-3 : 0 < 3
0-is-less-than-3 = <-trans (<-trans <-suc <-suc) <-suc
-- 0-is-less-than-3 = <-trans lemma <-suc
 
ct : CT (if not true then false else true)
-- ct = if-CT-3 true-CT 
ct = if-CT-1 (not-CT true-CT) -- alternative proof

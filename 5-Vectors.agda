module 5-Vectors where


open import 5-Basics using 
     (ℕ; suc; zero; _+_; _*_; _=ℕ_; 
      Bool; true; false; ¬; _∧_; 
      Maybe; just; nothing)


-- data types
--
infixr 10 _∷_

data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

Matrix : ∀ {A} → ℕ → ℕ → Set
Matrix {A} n m = Vec (Vec A m) n

-- Matrix : Set → ℕ → ℕ → Set
-- Matrix : (A : Set) (n : ℕ) (m : ℕ) → Set
-- Matrix : (A : Set) → ℕ → ℕ → Set
-- Matrix A n m = Vec (Vec A m) n

-- values
--
x = 0
y = 1
xs = y ∷ 2 ∷ 7 ∷ []
ys = 9 ∷ xs

-- functions
--
_++_ : ∀ {A n m} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

tail : ∀ {A n} → Vec A (suc n) → Vec A n
tail (_ ∷ xs) = xs

-- head : {A : Set} → List A → A
-- head []       = {!!}
-- head (x :: _) = x

head : {A : Set} → {n : ℕ} → Vec A (suc n) → A
--head : ∀ {A n} → Vec A (suc n) → A
head (x ∷ _) = x

last : ∀ {A n} → Vec A n → Maybe A
-- last {A} {0} []       = nothing
-- last {A} {1} (x ∷ []) = just x
-- last {A} {suc n} (_ ∷ xs) = last xs 
last []       = nothing
last (x ∷ []) = just x
last (_ ∷ xs) = last xs 

infix 8 _=V_

_=V_ : ∀ {n} → Vec ℕ n → Vec ℕ n → Bool
[]     =V []     = true
n ∷ ns =V m ∷ ms = n =ℕ m ∧ ns =V ms

size : ∀ {A n} → Vec A n → ℕ 
size {A} {n} _ = n
-- size = λ {A} {n} _ → n

map : ∀ {A B n} → (A → B) → Vec A n → Vec B n 
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

firstRow : ∀ {A n m} → Vec (Vec A m) (suc n) → Vec A m
-- firstRow : ∀ {A n m} → Matrix A (suc n) m → Vec A m
firstRow (xs ∷ _) = xs

firstCol : ∀ {A n m} → Vec (Vec A (suc m)) n → Vec A n
-- firstCol : ∀ {A n m} → Matrix A n (suc m) → Vec A n
firstCol = map head

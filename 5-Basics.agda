module 5-Basics where
-- data types
--
data Bool : Set where
  false : Bool
  true  : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data _≡_ {A : Set} : A → A → Set where
 refl : {x : A} → x ≡ x

cong : {A B : Set} (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

infixr 10 _∷_

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A


-- values
--
one : ℕ
one = suc zero

two : ℕ
two = suc one

xs' : List ℕ
xs' = zero ∷ one ∷ two ∷ []

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

x = 0
y = 1
xs = y ∷ 2 ∷ 7 ∷ []
ys = 9 ∷ xs


-- functions
--
¬ : Bool → Bool
¬ true  = false
¬ false = true

infix 3 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

_*_ : ℕ → ℕ → ℕ
zero  * m = zero
suc n * m = m + (n * m)

infix 6 _=ℕ_

_=ℕ_ : ℕ → ℕ → Bool
zero  =ℕ zero  = true
suc n =ℕ suc m = n =ℕ m
_     =ℕ _     = false 

fold-ℕ : ℕ → (ℕ → ℕ) → ℕ → ℕ
-- fold-ℕ : ∀{B} → ℕ → (B → ℕ) → ℕ → ℕ
-- fold-ℕ : ∀{B} → B → (B → B) → ℕ → B
fold-ℕ u _ zero    = u
fold-ℕ u f (suc n) = f (fold-ℕ u f n)

plus : ℕ → ℕ → ℕ
plus n m = fold-ℕ m suc n

_+'_ : ℕ → ℕ → ℕ
n +' m = fold-ℕ m suc n

times : ℕ → ℕ → ℕ
times n m = fold-ℕ zero (plus m) n



--_++_ : ∀ {A} → List A → List A → List A
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

tail : {A : Set} → List A → List A
tail []        = []
tail (_ ∷ xs) = xs

-- head : {A : Set} → List A → A
-- head []       = {!!}
-- head (x ∷ _) = x

head : {A : Set} → List A → Maybe A
head []      = nothing
head (x ∷ _) = just x

last : {A : Set} → List A → Maybe A
last []       = nothing
last (x ∷ []) = just x
last (_ ∷ xs) = last xs

reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ (x  ∷ [])

_!!_ : {A : Set} → List A → ℕ → Maybe A
[]       !! _       = nothing
(x ∷ _)  !! zero    = just x
(_ ∷ xs) !! (suc n) = xs !! n

infix 8 _=L_

_=L_ : List ℕ → List ℕ → Bool
[]     =L []     = true
n ∷ ns =L m ∷ ms = n =ℕ m ∧ ns =L ms
_      =L _      = false 

size : ∀ {A} → List A → ℕ 
size []       = 0
size (_ ∷ xs) = suc (size xs)


module 6-Bool where


-- a small language for boolean expressions with negation and conditional

-- open import Data.List hiding (or) -- List type needed for "or" constructor

open import 5-Basics using 
     (List; []; _∷_)


-- syntax 
--
data Term : Set where
  true  : Term
  false : Term
  not   : Term → Term
--  if_then_else_ : Term → Term → Term → Term 
  if_then_else_ : (t₁ t₂ t₃ : Term) → Term 
  or    : List Term → Term

infix 60 if_then_else_

data Bool : Set where
  true : Bool
  false : Bool

¬ : Bool → Bool
¬ true = false
¬ false = true

_∧_ : Bool → Bool → Bool
false ∧ _ = false
true ∧ a  = a

infix 3 _∨_

infix 2 _≡_

_∨_ : Bool → Bool → Bool
true ∨ _ = true
false ∨ a = a

data _≡_ {A : Set} : A → A → Set where
  refl : ∀ { x : A } → x ≡ x

deMorgan1 : ∀ {a b} → ¬(a ∧ b) ≡ ¬ a ∨ ¬ b
deMorgan1 {true} {x} = refl
deMorgan1 {false} {y} = refl

neg-cancel : {a : Bool} → ¬(¬ a) ≡ a
neg-cancel {true} = refl
neg-cancel {false} = refl

-- example expression
--
nt : Term
nt = not true

nnt : Term
nnt = not (not true)

iff : Term
iff = if false then false else not false

ifnt : Term
ifnt = if nt then false else not false

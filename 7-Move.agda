module 7-Move where

-- a language for movements in the 2D plane

open import 5-Basics

-- one more function on ℕ we need
--
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n


-- syntax of robot programs
--
data Move : Set where
  up down right left : ℕ → Move
  home : Move

Prog : Set
Prog = List Move


-- example programs
--
goto35 : Prog
goto35 = up 3 ∷ right 5 ∷ []
 

-- machine state for small-step semantics
--
data State : Set where
  _~_,_ : Prog → ℕ → ℕ → State

infix 4 _~_,_

state : State
state = goto35 ~ 0 , 0


-- two reduction relations: final step & intermediate transitions
-- plus a transitive closure reduction relation
--
infix 3 _↦_
infix 3 _↦*_ 

data _↦_ : State → State → Set where
  Up    : ∀ {p n x y} →     up n ∷ p ~ x , y  ↦  p ~ x     , y + n
  Down  : ∀ {p n x y} →   down n ∷ p ~ x , y  ↦  p ~ x     , y ∸ n
  Right : ∀ {p n x y} →  right n ∷ p ~ x , y  ↦  p ~ x + n , y
  Left  : ∀ {p n x y} →   left n ∷ p ~ x , y  ↦  p ~ x ∸ n , y
  Home  : ∀ {p x y}   →     home ∷ p ~ x , y  ↦  p ~ 0     , 0

infixr 5 _then_

data _↦*_ : State → State → Set where
  refl   : ∀ {s} → s ↦* s
  _then_ : ∀ {s₁ s₂ s₃} → s₁ ↦ s₂ → s₂ ↦* s₃ → s₁ ↦* s₃


lemma : (up 3 ∷ right 5 ∷ [] ~ 0 , 0) ↦* [] ~ 5 , 3
lemma = Up then Right then refl

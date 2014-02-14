module 7-Motions where

open import Data.List 
open import Data.Nat

data Move : Set where
  up down left right : ℕ → Move
  home : Move

Prog : Set
Prog = List Move

data State : Set where 
  _~_,_ : Prog → ℕ → ℕ → State

goto23 : State 
goto23 = (up 2 ∷ right 3 ∷ []) ~ 0 , 0

infixr 20 _~_,_

_-_ : ℕ → ℕ → ℕ
0 - _ = 0
a - 0 = a
suc a - suc b = a - b



data _↦_ : State → State → Set where
  ↦Up : ∀ {xs} {n x y : ℕ} → (up n ∷ xs) ~ x , y ↦  xs ~ x , ( y + n )
  ↦Down : ∀ {xs} {n x y : ℕ} → (down n ∷ xs) ~ x , y ↦  xs ~ x , ( y - n )
  ↦Right : ∀ {xs} {n x y : ℕ} → (right n ∷ xs) ~ x , y ↦  xs ~ (x + n) , y
  ↦Left : ∀ {xs} {n x y : ℕ} → (left n ∷ xs) ~ x , y ↦  xs ~ (x - n) , y
  ↦Home : ∀ {xs x y} → (home ∷ xs) ~ x , y ↦ xs ~ 0 , 0
  
data _↦*_ : State → State → Set where
  refl : ∀ {x} → x ↦* x
  _then_ :  ∀ {x y z } → x ↦ y → y ↦* z → x ↦* z

infix 3 _↦_
infix 3 _↦*_

infixr 5 _then_

testUp : ( up 2 ∷ [] ) ~ 0 , 0 ↦ [] ~ 0 , 2
testUp = ↦Up

testUp2 : (up 3 ∷ down 1 ∷ []) ~ 0 , 0 ↦ ( down 1 ∷ []) ~ 0 , 3
testUp2 = ↦Up 

testRefl : [] ~ 6 , 10 ↦* [] ~ 6 , 10
testRefl = refl

testMultiple1 : ( up 3 ∷ [] ) ~ 0 , 0 ↦* ( [] ) ~ 0 , 5
testMultiple1 = ↦Up then refl

-- testMultiple : ( right 5 ∷ up 3 ∷ [] ) ~ 0 , 0 ↦* ([]) ~ 5 , 3
-- testMultiple = ↦Right then ↦Up then refl

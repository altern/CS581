module 7-Motions where

--open import 5-Basics using 
--     (ℕ; suc; zero; _=ℕ_; 
--      Bool; true; false; _∧_;
--      List; []; _∷_)

open import Data.List
open import Data.Nat

data Move : Set where
     up down right left : ℕ → Move
     home : Move

Prog : Set
Prog = List Move

-- 1 :: 2 :: []

goto35 : Prog
goto35 = (up 3 ∷ right 5 ∷ []) 

data State : Set where 
  _~_,_ : Prog → ℕ → ℕ → State

state : State
state = goto35 ~ 0 , 0

state2 : State
state2 = ( up 1 ∷ [] ) ~ 0 , 1

infixr 10 _↦_ 
infixr 11 _~_,_

_-_ : ℕ → ℕ → ℕ
0 - _ = 0
a - 0 = a
suc a - suc b = a - b

data _↦_ : State → State → Set where
  ↦Up : ∀ { xs n x y } → (up n ∷ xs) ~ x , y ↦ xs ~ x , (y + n)
  ↦Down : ∀ { xs n x y } → (down n ∷ xs) ~ x , y ↦ xs ~ x , (y - n)
  ↦Left : ∀ { xs n x y } → (left n ∷ xs) ~ x , y ↦ xs ~ (x - n) , y 

testUp : (up 2 ∷ []) ~ 0 , 0 ↦ [] ~ 0 , 2
testUp = ↦Up

testDown : (down 1 ∷ []) ~ 0 , 2 ↦ [] ~ 0 , 1
testDown = ↦Down

testLeft : [] ~ 0 , 0 ↦ [] ~ 0 , 0
testLeft = ↦Left
 
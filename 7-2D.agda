module 7-2D where

open import 5-Basics using 
     (ℕ; suc; zero; _=ℕ_; 
      Bool; true; false; _∧_;
      List; []; _∷_)

data Move : Set where
     up down right left : ℕ → Move
     home : Move

Prog : Set
Prog = List Move

-- 1 :: 2 :: []

-- goto35 : Prog
-- goto35 = (up 3 :: right 5 :: [])
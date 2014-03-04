module 7-Quiz where

open import 5-Basics using 
     (List; []; _∷_; ℕ; _+_; suc; zero; true; false; Bool)

-- open import Data.List

infix 3 _#_

data Term : Set where
  true : Term
  false : Term
  not : Term → Term
  if_then_else_ : Term → Term → Term → Term

data _#_ : Term → ℕ → Set where
  #true : true # 1
  #false : false # 1
  #not : ∀ { t n } → t # n → not t # n
  #ifthenelse : ∀ { t₁ t₂ t₃ n₁ n₂ n₃ } → t₁ # n₁ → t₂ # n₂ → t₃ # n₃ → if t₁ then t₂ else t₃ # n₁ + (n₂ + n₃)

t : Term
t = if true then false else not true 

t#3 : t # 3
t#3 = #ifthenelse (#true) (#false) (#not #true)

data _∈_ : ℕ → List ℕ → Set where
  ∈-Head : ∀ { n xs } → n ∈ (n ∷ xs)
  ∈-Tail : ∀ { n m xs } → n ∈ xs → n ∈ (m ∷ xs)

2inList : 2 ∈ (1 ∷ 2 ∷ 5 ∷ 10 ∷ 2 ∷ 4 ∷ 123 ∷ 3 ∷ [])
2inList = ∈-Tail ∈-Head
--2inList = ∈-Tail (∈-Tail (∈-Tail ∈-Head))

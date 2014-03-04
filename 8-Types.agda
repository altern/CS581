module 8-Types where

data Type : Set where
  Int : Type
  Bool : Type

data Term : Set where
  0 : Term
  succ : Term
  true : Term 
  false : Term
  if_then_else_ : Term → Term → Term → Term

data _:_ : Term → Type → Set where
  :-zero : 0:Int
  :-true : true:Bool
  :-false : false:Bool
  :-int : ∀{t} →  t:Int → (succ t):Int
  :-if : ∀{t t₁ t₂}(T:Type) → t:Bool → t₁:T → t₂:T → if t then t₁ else t₂:T
  


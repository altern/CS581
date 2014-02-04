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

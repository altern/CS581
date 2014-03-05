module SCMF where

open import Data.Fin
-- open import Data.Nat
open import Data.Sum

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

{-# BUILTIN NATURAL Nat    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

VN = Fin
X = Nat

VC = [ X , VN ]

-- data _∈_ : Nat → Fin → Bool
--  in : 

-- First finite set of natural numbers
N : VN 1
N = zero 

n = N

-- Second finite set of natural numbers
M : VN 2
M = zero

m = M

-- Third finite set of natural numbers
K : VN 3
K = zero

k = K

-- 4th finite set of natural numbers

L : VN 4
L = zero

l = L

-- Pattern application operator
-- PATTERN #=> value
-- Examples: 
--          K #=> 0, K #=> 1, K #=> 2, ... , K #=> 345, ... , K #=> k
--          M #=> 0, M #=> 1, M #=> 2, ... , M #=> 128, ... , M #=> m

data _#=>_ : (N : VN) → Nat → Set where
     num : (n : Nat) → N #=> n

-- Validating pattern application operator properties

k0 : K #=> 0
k1 : K #=> 1
k2 : K #=> 2
--   ... 
k345 : K #=> 345
--   ...
kk : K #=> k

m0 : M #=> 0
m1 : M #=> 1
m2 : M #=> 2
--   ... 
m128 : m #=> 128
--   ...
mm : M #=> m

-- Instantiation operator
-- Examples: 
--      Patterns: x ↓ N, x ↓ M, ... 
--      Values:   x ↓ 0, x ↓ 1, ... x ↓ 53, ... x ↓ n 

data _↓_ : VC → VC → Set where
  ↓Pattern : (x : X) (K' : K) → x ↓ K'
  ↓Value : (x : X) (k : Nat) (K' : K) → K' #=> k → x ↓ K' → x ↓ k

↓N : X ↓ N
↓M : X ↓ M
----------
↓0 : X ↓ 0
↓1 : X ↓ 1
--  ... 
↓53 : X ↓ 53
--  ...
↓n : X ↓ n

k0 = num
k1 = num
k2 = num
k345 = num
kk = num

m0 = num
m1 = num
m2 = num
m128 = num
mm = num

↓N = ↓Pattern
↓M = ↓Pattern
↓0 = ↓Value
↓1 = ↓Pattern
↓53 = ↓Pattern
↓n = ↓Pattern


module Num where

data Term = N Int
          | Plus Term Term
       	  | Neg Term
          deriving (Eq,Show) 

sem :: Term -> Int
sem (N i)       = i
sem (Plus t t') = sem t + sem t'
sem (Neg t)     = -(sem t)

t = Neg (N 5) `Plus` N 7

module NumBool where

data Term = N Int
          | Plus Term Term
       	  | Neg Term
       	  | T Bool
       	  | Equal Term Term
       	  | If Term Term Term
          deriving (Eq, Show) 

data Value = I Int | B Bool
             deriving (Eq, Show)


n = N 3 `Plus` N 5
b = Equal (N 8) n


-- First approach
--
sem1 :: Term -> Value
sem1 (N i)        = I i
-- sem1 (Plus t t') = sem1 t + sem1 t'  -- INCORRECT!
sem1 (Plus t t')  = case (sem1 t,sem1 t') of
                      (I i,I j) -> I (i+j)
-- sem1 (Equal t t') = B (t == t')  -- INCORRECT!
sem1 (Equal t t') = B (sem1 t == sem1 t')
sem1 _ = undefined                 


-- int (bool) forces its argument value to be Int (Bool).
-- If the value is not the expected Int (Bool), the function fails
--
int :: Value -> Int
int (I i) = i
int v     = error ("Value "++show v++" is not an integer")

bool :: Value -> Bool
bool (B b) = b
bool v     = error ("Value "++show v++" is not a boolean")


-- Second approach
--
sem2 :: Term -> Value
sem2 (N i)        = I i
sem2 (Plus t t')  = I (int v+int w) where (v,w) = (sem2 t,sem2 t')
sem2 (Equal t t') = B (sem2 t == sem2 t')
sem2 _ = undefined                 


-- liftI lifts a binary Int operation to one that operates on values
--
liftI :: (Int -> Int -> Int) -> Value -> Value -> Value
liftI f (I i) (I j) = I (f i j)


-- Third approach
--
sem3 :: Term -> Value
sem3 (N i)        = I i
sem3 (Plus t t')  = liftI (+) (sem3 t) (sem3 t')
sem3 (Equal t t') = B (sem3 t == sem3 t')
sem3 _ = undefined                 


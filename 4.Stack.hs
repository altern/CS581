module Stack where

type Prog = [Cmd]

data Cmd = LD Int
         | ADD 
         | MULT
         | DUP
         deriving Show

type Stack = [Int]


sem :: Prog -> Stack -> Stack
--sem []     s = s
--sem (c:cs) s = sem cs (semC c s)
sem = foldl (.) id . map semC

semC :: Cmd -> Stack -> Stack
semC (LD i) s       = i:s
semC ADD    (x:y:s) = x+y:s
semC MULT   (x:y:s) = x*y:s
semC DUP    s@(x:_) = x:s
semC _      s       = s       -- ignore error-producing commands

p1 = [LD 3, DUP, ADD, DUP, MULT]
p2 = []::Prog
err1 = [LD 3, ADD]
err2 = [LD 3, MULT]
err3 = [DUP]

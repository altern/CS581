module Lamda where 

import Prelude hiding (const)

type V = String

data E = Var V
       | App E E 
       | Abs V E
--          deriving Show

instance Show E where
  show (Var v)     = v
  show (App e1 e2) = showBrack e1++showBrack e2
  show (Abs v e)   = '\\':v++showAbs e
  
showBrack :: E -> String
showBrack (Var v) = v
showBrack e       = '(':show e++")"

showAbs :: E -> String
showAbs (Abs v e) = v++showAbs e
showAbs e         = '.':show e


-- free variables
-- 
fv :: E -> [V]
fv (Var x)     = [x]
fv (App e1 e2) = fv e1 ++ fv e2
fv (Abs x e)   = remove x (fv e)

remove :: Eq a => a -> [a] -> [a]
remove x = filter (/=x)


-- substitution
-- 
subst :: E -> V -> E -> E
subst (Var w) v e | v==w      = e
subst e v (Var w) | v==w      = e
                  | otherwise = Var w
subst e v (App e1 e2)         = App (subst e v e1) (subst e v e2)
subst e v (Abs w e1) | w==v   = Abs w e1
                     | not (w `elem` fv e) = Abs w (subst e v e1) 
                     | True   = Abs z (subst e v (subst (Var z) w e1))
                                where z = fresh (v:fv (Abs w e1)++fv e)

fresh:: [String] -> String
fresh xs = head [x | x <- vars, not (elem x xs)]
           where vars = map (('x':).show) [1..]


-- full beta reduction
--
red :: E -> E
red (App (Abs x m) n)     = red (subst n x m)
red (App m n) | isAbs m'  = red (App m' n')
              | otherwise = App m' n' where (m',n') = (red m,red n)
red (Abs x m)             = Abs x (red m)
red v@(Var _)             = v

isAbs (Abs _ _) = True
isAbs _         = False


-- Church numnberals
-- 
fn 0 = x
fn n = App f (fn (n-1))

-- cn converts positive integers into Church numerals
-- 
cn n = Abs "f" (Abs "x" (fn n))

-- some functions on Church numerals
-- 
suc  = abss "nfx" (App f (apps "nfx"))
add  = abss "nmfx" (App (App n f) (apps "mfx"))
mult = abss "nmf" (App n (apps "nf"))


-- abbreviations 
-- 
cVar = Var . (:[])

[x,y,z,f,n,m] = map cVar "xyzfnm"

abss s e = foldr (\c e->Abs [c] e) e s

apps s = foldl1 App (map cVar s)


-- fixpoint combinater
--
fix :: (a -> a) -> a
fix f = f (fix f)

s :: Int -> Int
s x = x+1

const = \x y -> x

swap = \x y -> y x

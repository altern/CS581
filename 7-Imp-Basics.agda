module 7-Imp-Basics where

-- Imperative language 
-- (use this version instead of 7-Imp if you don't
--  hace access to the standard library)

open import 5-Basics hiding (plus; x; y)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B


-- syntax 
--
Var = ℕ

data Exp : Set where
  num : ℕ → Exp
  var : Var → Exp
  plus : Exp → Exp → Exp

infix 10 _:=_
infixr 8 _⁏_

data Prog : Set where
  _:=_ : Var → Exp → Prog
  dec : Var → Prog
  _⁏_ : Prog → Prog → Prog       -- NOTE: Inverse Semicolon
  while_❴_❵ : Exp → Prog → Prog  -- NOTE: use U+2774 for "{" and U+2775 for "}"


-- state manipulation
--
State = List (Var × ℕ)

infix 3  _!_⇒_

data _!_⇒_ : State → Var → ℕ → Set where
  ⇒Match  : ∀ {s v n} → (v , n) ∷ s ! v ⇒ n
  ⇒Search : ∀ {s v w n m} → s ! v ⇒ n → (w , m) ∷ s ! v ⇒ n

infix 3  _!_←_⇒_

data _!_←_⇒_ : State → Var → ℕ → State → Set where
  ←Init : ∀ {v n} → [] ! v ← n ⇒ (v , n) ∷ []
  ←Upd  : ∀ {s v n m} → (v , n) ∷ s ! v ← m ⇒ (v , m) ∷ s
  ←Ctxt : ∀ {s s' v w n m} → s ! v ← m ⇒ s' → (w , n) ∷ s ! v ← m ⇒ (w , n) ∷ s'


-- Big-step operational semantics
--
-- Three relations:
--  s ! e ↓ n    evaluates expression e in the context of sate s to number n
--  s ! p ⇓ s'   evaluates the program p in the context of s to a new state s'
--

infix 3 _!_↓_
infix 3 _!_⇓_ 

data _!_↓_ : State → Exp → ℕ → Set where
  ↓Num  : ∀ {s n} → s ! num n ↓ n

  ↓Plus : ∀ {s e e' n m} → 
            s ! e ↓ n   →   s ! e' ↓ m   →
            --------------------------
              s ! plus e e' ↓ n + m

  ↓Var  : ∀ {s v n} → 
          s ! v ⇒ n      →
          -------------
          s ! var v ↓ n


data _!_⇓_ : State → Prog → State → Set where
  ⇓Assg : ∀ {s s' v e n} → 

            s ! e ↓ n   →   s ! v ← n ⇒ s'  →
            ------------------------------- 
                     s ! v := e ⇓ s'

  ⇓Dec : ∀ {s s' v n} → 

            s ! v ⇒ suc n   →   s ! v ← n ⇒ s'  →
            ----------------------------------- 
                     s ! dec v ⇓ s'

  ⇓Seq  : ∀ {s s₁ s₂ p₁ p₂} → 

             s ! p₁ ⇓ s₁   →   s₁ ! p₂ ⇓ s₂  →
             -----------------------------
                    s ! p₁ ⁏ p₂ ⇓ s₂

  ⇓While-F  : ∀ {s e p} → 

                  s ! e ↓ 0       → 
            ---------------------
            s ! while e ❴ p ❵ ⇓ s

  ⇓While-T  : ∀ {s s₁ s₂ e n p} → 

            s ! e ↓ suc n  →  s ! p ⇓ s₁  →  s₁ ! while e ❴ p ❵ ⇓ s₂  →
            --------------------------------------------------------
                            s ! while e ❴ p ❵ ⇓ s₂

infix 5 _then_

_then_ : ∀ {s s₁ s₂ p₁ p₂} → s ! p₁ ⇓ s₁ → s₁ ! p₂ ⇓ s₂ → s ! p₁ ⁏ p₂ ⇓ s₂
_then_ = ⇓Seq
-- p then q = ⇓Seq p q


-- auxiliary definitions and lemmas
--
x : Var
y : Var
z : Var
x = 0
y = 1
z = 2

x2y3 : State
x2y3 = (x , 2) ∷ (y , 3) ∷ []

x⇒2 : x2y3 ! x ⇒ 2
x⇒2 = ⇒Match

y⇒3 : x2y3 ! y ⇒ 3
y⇒3 = ⇒Search ⇒Match

def-z7 : x2y3 ! z ← 7 ⇒ x2y3 ++ ((z , 7) ∷ [])
def-z7 = ←Ctxt (←Ctxt ←Init)

upd-y : x2y3 ! y ← 4 ⇒ (x , 2) ∷ (y , 4) ∷ []
upd-y = ←Ctxt ←Upd


-- example programs and their meanings
--
x↓2 : x2y3 ! var x ↓ 2
-- x↓2 = ↓Var ⇒Match
x↓2 = ↓Var x⇒2

y↓3 : x2y3 ! var y ↓ 3
-- y↓3 = ↓Var (⇒Search ⇒Match)
y↓3 = ↓Var y⇒3

x+4 : x2y3 ! plus (var x) (num 4) ↓ 6
-- x+4 = ↓Plus (↓Var ⇒Match) ↓Num
x+4 = ↓Plus x↓2 ↓Num

x+4+y : x2y3 ! plus (plus (var x) (num 4)) (var y) ↓ 9 
-- x+4+y = ↓Plus (↓Plus (↓Var ⇒Match) ↓Num) (↓Var (⇒Search ⇒Match))
-- x+4+y = ↓Plus x+4 (↓Var (⇒Search ⇒Match))
-- x+4+y = ↓Plus x+4 (↓Var y⇒3)
x+4+y = ↓Plus x+4 y↓3

eval-x=2 : [] ! x := num 2 ⇓ (x , 2) ∷ []
eval-x=2 = ⇓Assg ↓Num ←Init

eval-whilex0 : (x , 0) ∷ [] ! while var x ❴ dec x ❵ ⇓ (x , 0) ∷ []
eval-whilex0 = ⇓While-F (↓Var ⇒Match)

cd1 : Prog
cd1 = x := num 1 ⁏
      while var x ❴ dec x ❵
--
eval-cd1 : [] ! cd1 ⇓ (x , 0) ∷ []
eval-cd1 = ⇓Assg ↓Num ←Init then
           ⇓While-T (↓Var ⇒Match) (⇓Dec ⇒Match ←Upd) (⇓While-F (↓Var ⇒Match))

cd2 : Prog
cd2 = x := num 2 ⁏
      while var x ❴ dec x ❵
--
eval-cd2 : [] ! cd2 ⇓ (x , 0) ∷ []
eval-cd2 = ⇓Assg ↓Num ←Init then
           ⇓While-T (↓Var ⇒Match) (⇓Dec ⇒Match ←Upd) while-x1
           where while-x1 = ⇓While-T (↓Var ⇒Match) (⇓Dec ⇒Match ←Upd) (⇓While-F (↓Var ⇒Match))

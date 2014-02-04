module 6-Imp where

-- syntax 
--
data Expr : Set where
  zero : Expr
  succ : Expr → Expr

data Stmt : Set where
  noop : Stmt
  _⁏_ : Stmt → Stmt → Stmt        -- NOTE: Inverse Semicolon
  while_❴_❵ : Expr → Stmt → Stmt  -- NOTE: use U+2774 for "{" and U+2775 for "}"


-- example expression
--
s : Stmt
s = while succ zero ❴ noop ⁏ while zero ❴ noop ❵ ❵


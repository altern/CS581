module 7-BoolNot where


-- Syntax of Bool language
--
data Term : Set where
  true          : Term
  false         : Term
  not           : Term → Term
  if_then_else_ : (t₁ t₂ t₃ : Term) → Term


-- Small-step semantics
--
data _↦_ : Term → Term → Set where
  ↦NotFalse : not false ↦ true

  ↦NotTrue  : not true ↦ false

  ↦Not      :  ∀ {t t′} →

                  t ↦ t′     →
              --------------
              not t ↦ not t′

  ↦IfTrue   : ∀ {t₁ t₂} → if true  then t₁ else t₂ ↦ t₁

  ↦IfFalse  : ∀ {t₁ t₂} → if false then t₁ else t₂ ↦ t₂

  ↦If       : ∀ {t t′ t₂ t₃} →

                                 t ↦ t′                     →
              ---------------------------------------------
              if t then t₂ else t₃ ↦ if t′ then t₂ else t₃


infixr 5 _then_

data _↦*_ : Term → Term → Set where
  refl   : ∀ {t} → t ↦* t
  _then_ : ∀ {t₁ t₂ t₃} → t₁ ↦ t₂ → t₂ ↦* t₃ → t₁ ↦* t₃


-- examples
--
t : true ↦* true
t = refl

nt : not true ↦ false
nt = ↦NotTrue

nt* : not true ↦* false
nt* = ↦NotTrue then refl

nf : not false ↦ true
nf = ↦NotFalse

nnt : not (not true) ↦ not false
nnt = ↦Not ↦NotTrue

nnt* : not (not true) ↦* true
nnt* = ↦Not ↦NotTrue then ↦NotFalse then refl

nnnt* : not (not (not true)) ↦* false
nnnt* = ↦Not (↦Not ↦NotTrue) then  ↦Not ↦NotFalse then ↦NotTrue then refl


-- Big-step semantics
--
data _⇓_ : Term → Term → Set where
  ⇓True     : true  ⇓ true
  ⇓False    : false ⇓ false
  ⇓NotTrue  : ∀ {t} → t ⇓ true → not t ⇓ false
  ⇓NotFalse : ∀ {t} → t ⇓ false → not t ⇓ true
  ⇓IfTrue   : ∀ {t t₁ t₂ v} → t ⇓ true → t₁ ⇓ v →
              if t then t₁ else t₂ ⇓ v
  ⇓IfFalse  : ∀ {t t₁ t₂ v} → t ⇓ false → t₂ ⇓ v →
              if t then t₁ else t₂ ⇓ v

-- examples
--
tB : true ⇓ true
tB = ⇓True

ntB : not true ⇓ false
ntB = ⇓NotTrue ⇓True

nntB : not (not true) ⇓ true
nntB = ⇓NotFalse (⇓NotTrue ⇓True)

nnntB : not (not (not true)) ⇓ false
nnntB = ⇓NotTrue (⇓NotFalse (⇓NotTrue ⇓True))

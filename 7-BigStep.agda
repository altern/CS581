module 7-BigStep where

data Term : Set where
  true : Term
  false : Term
  not : Term → Term
  if_then_else_ : (t₁ t₂ t₃ : Term) → Term 

-- SmallStep
data _↦_ : Term → Term → Set where
  ↦IfTrue : ∀ {t₁ t₂} → if true then t₁ else t₂ ↦ t₁
  ↦IfFalse : ∀ {t₁ t₂} → if false then t₁ else t₂ ↦ t₂
  ↦If : ∀ {t t' t₂ t₃} → t ↦ t' → if t then t₂ else t₃ ↦ t₂ → if t' then t₂ else t₃ ↦ t₃
  ↦NotTrue : not true ↦ false
  ↦NotFalse : not false ↦ true
  ↦Not : ∀ {t t'} → t ↦ t' → not t ↦ not t'

-- BigStep
data _↦*_ : Term → Term → Set where
  refl : {t : Term} → t ↦* t
  _then_ : {t₁ t₂ t₃ : Term} → t₁ ↦ t₂ → t₂ ↦* t₃ → t₁ ↦* t₃

p₁ : not false ↦ true
p₁ = ↦NotFalse

p₂ : not true ↦ false
p₂ = ↦NotTrue

p₃ : not ( not true ) ↦ not false
p₃ = ↦Not ↦NotTrue

p₄ : not (not false) ↦ not true
p₄ = ↦Not ↦NotFalse

p₅ : not (not true) ↦* true
p₅ = ↦Not ↦NotTrue then (↦NotFalse then refl)

p₆ : true ↦* true
p₆ = refl

p₇ : false ↦* false
p₇ = refl

p₈ : not true ↦* false
p₈ = ↦NotTrue then refl

p₉ : not (not false) ↦* false
p₉ = ↦Not ↦NotFalse then (↦NotTrue then refl)

p₁₀ : not ( not ( not true ) ) ↦* false
p₁₀ = ↦Not ( ↦Not ↦NotTrue) then (↦Not ↦NotFalse then (↦NotTrue then  refl))


module well-typed-initial-context where
open import well-typed-syntax
open import common

pattern ε₀▻‘Typ’ = ε₀
  ▻Typ ε₀ {- ‘Context’ : Typ ε -}
pattern ‘Context’p₀ = ‘TVAR₀₀’
pattern ε₀▻‘Typ’▻‘Context’ = ε₀▻‘Typ’
  ▻Typ (ε₀▻‘Typ’ ▻ ‘Context’p₀) {- ‘Typ’ : Typ (ε ▻ ‘Context’)-}
pattern ‘Context’p₁ = WT ‘Context’p₀
pattern ‘Typ’p₁     = ‘TVAR₀₁’
pattern ε₀▻‘Typ’▻‘Context’▻‘Term’ = ε₀▻‘Typ’▻‘Context’
  ▻Typ (ε₀▻‘Typ’▻‘Context’ ▻ ‘Context’p₁ ▻ ‘Typ’p₁) {- ‘Term’ : Typ (ε ▻ ‘Context’ ▻ ‘Typ’) -}

pattern εp₂        = ε₀▻‘Typ’▻‘Context’▻‘Term’
pattern ‘Context’p₂ = WT ‘Context’p₁
pattern ‘Typ’p₂     = WT₁ ‘Typ’p₁
pattern ‘Term’p₂    = ‘TVAR₀₂’

pattern εp₃ = εp₂
  ▻ ‘Context’p₂ {- ‘ε₀’ -}
pattern ‘Context’p₃ = W ‘Context’p₂
pattern ‘Typ’p₃     = W1 ‘Typ’p₂
pattern ‘Term’p₃    = W2 ‘Term’p₂
pattern ‘ε₀’p₃       = ‘VAR₀’

pattern εp₄ = εp₃
  ▻ (‘Context’p₃ ‘→’ W ‘Context’p₃ ‘→’ W (W ‘Context’p₃)) {- ‘ε₀’ -}
pattern ‘Context’p₄ = W ‘Context’p₃
pattern ‘Typ’p₄     = W1 ‘Typ’p₃
pattern ‘Term’p₄    = W2 ‘Term’p₃
pattern ‘ε₀’p₄       = w ‘ε₀’p₃
pattern _‘▻’p₄_     = ‘VAR₀’


{-  ▻ {!!} {- record Σ {A : Set} (P : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : P proj₁ -}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}-}
{-postulate
  ‘Context’ : Typ ε
  ‘Typ’ : Typ (ε ▻ ‘Context’)-}


arrow-tower : Set → Set → ℕ → Set
arrow-tower T R 0 = R
arrow-tower T R (suc n) = T → (arrow-tower T R n)

lambda-tower : ∀ {T} → (T → T → T) → (n : ℕ) → T → arrow-tower T T n
lambda-tower F 0 = λ x → x
lambda-tower F (suc n) = λ x y → lambda-tower F n (F x y)

arrow-tower-to-arrow : ∀ {T} {R} → (R → Set) → (n : ℕ) → arrow-tower T R n → Set
arrow-tower-to-arrow {T} f 0 X = f X
arrow-tower-to-arrow {T} f (suc n) X = {x : T} → arrow-tower-to-arrow f n (X x)

lambda-tower-to-lambda : ∀ {T}
  → (F : T → T → T)
  → (P : T → Set)
  → (f : ∀ {a b : T} → P a → P (F a b))
  → (n : ℕ)
  → (x : T)
  → (y : T)
  → (p : P (F x y))
  → arrow-tower-to-arrow P n (lambda-tower F n (F x y))
lambda-tower-to-lambda {T} F P f 0 x y p = p
lambda-tower-to-lambda {T} F P f (suc n) x y p = λ {z} → lambda-tower-to-lambda F P f n (F x y) z (f p)

Context-Tower : (n : ℕ) → arrow-tower Context Context (suc n)
Context-Tower = lambda-tower _▻Typ_

Typ-Context-Tower : (n : ℕ) → Set
Typ-Context-Tower n = {Γ : Context} → arrow-tower-to-arrow {Context} {Context} Typ n (Context-Tower (suc n) Γ Γ)

‘TVAR_₀’ : (n : ℕ) → Typ-Context-Tower n
‘TVAR_₀’ n = λ {Γ} → lambda-tower-to-lambda {Context} _▻Typ_ Typ WT n Γ Γ ‘TVAR₀₀’

{-‘TVAR_₁’ : (n : ℕ) → Typ-Context-Tower n
‘TVAR_₁’ n = λ {Γ} {Γ'} → {!lambda-tower-to-lambda {Context} _▻Typ_ Typ WT n Γ Γ' {!!} {-‘TVAR₀₀’-}!}-}

abstract
  pattern εp        = εp₃
  pattern ‘Context’p = ‘Context’p₃
  pattern ‘Typ’p     = ‘Typ’p₃
  pattern ‘Term’p    = ‘Term’p₃
  pattern ‘ε₀’p       = ‘ε₀’p₃
  pattern _‘▻’p_     = _‘▻’p₄_

  ε : Context
  ε = εp

  ‘Context’ : Typ ε
  ‘Context’ = ‘Context’p

  ‘Typ’ : Typ (ε ▻ ‘Context’)
  ‘Typ’ = ‘Typ’p

  ‘Term’ : Typ (ε ▻ ‘Context’ ▻ ‘Typ’)
  ‘Term’ = ‘Term’p

  ‘ε₀’ : Term ‘Context’
  ‘ε₀’ = ‘ε₀’p

  {-_‘▻’_ : Term (‘Context’ ‘→’ W ‘Context’ ‘→’ W (W ‘Context’))
  _‘▻’_ = {!_‘▻’p_!}-}

  context-pick-if' : ∀ {P : Context → Set}
    → {Γ : Context}
    → (dummy : P (ε ▻ ‘Σ'’ ‘Context’ ‘Typ’))
    → (val : P Γ)
    → P (ε ▻ ‘Σ'’ ‘Context’ ‘Typ’)
  context-pick-if' {P} {εp ▻ ‘Σ'’ ._ ‘Typ’p} dummy val = val
  context-pick-if' {P} {_} dummy val = dummy

  context-pick-if-refl' : ∀ {P dummy val} →
    context-pick-if' {P} {ε ▻ ‘Σ'’ ‘Context’ ‘Typ’} dummy val ≡ val
  context-pick-if-refl' = refl

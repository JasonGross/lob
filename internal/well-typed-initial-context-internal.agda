module well-typed-initial-context-internal where
open import well-typed-syntax
open import well-typed-syntax-helpers
open import common

pattern ε₀▻‘Typ’ = ε₀
  ▻Typε {- ‘Context’ : Typ ε -}
pattern ‘Context’p₀ = ‘TVAR₀₀’
pattern ε₀▻‘Typ’▻‘Context’ = ε₀▻‘Typ’
  ▻Typ₁ ‘Context’p₀ {- ‘Typ’ : Typ (ε ▻ ‘Context’)-}
pattern ‘Context’p₁ = WT ‘Context’p₀
pattern ‘Typ’p₁     = ‘TVAR₀₁’
pattern ε₀▻‘Typ’▻‘Context’▻‘Term’ = ε₀▻‘Typ’▻‘Context’
  ▻Typ₂ ‘Context’p₁ ▻T ‘Typ’p₁ {- ‘Term’ : Typ (ε ▻ ‘Context’ ▻ ‘Typ’) -}

pattern εp₂        = ε₀▻‘Typ’▻‘Context’▻‘Term’
pattern ‘Context’p₂ = WT₁ ‘Context’p₁
pattern ‘Typ’p₂     = WT₁₂ ‘Typ’p₁
pattern ‘Term’p₂    = ‘TVAR₀₂’

pattern εp₃ = εp₂
  ▻ ‘Context’p₂ {- ‘ε₀’ -}
pattern ‘Context’p₃ = W ‘Context’p₂
pattern ‘Typ’p₃     = W1 ‘Typ’p₂
pattern ‘Term’p₃    = W2 ‘Term’p₂
pattern ‘ε₀’p₃       = ‘VAR₀’

εp₄ : Context
εp₄ = εp₃
  ▻ (‘Context’p₃ ‘→’ ‘Typ’p₃ ‘→'’ W ‘Context’p₃) {- ‘_▻Typ_’ -}
‘Context’p₄ : Typ εp₄
‘Context’p₄ = W ‘Context’p₃
‘Typ’p₄     : Typ (εp₄ ▻ ‘Context’p₄)
‘Typ’p₄     = W1 ‘Typ’p₃
‘Term’p₄    : Typ (εp₄ ▻ ‘Context’p₄ ▻ ‘Typ’p₄)
‘Term’p₄    = W2 ‘Term’p₃
‘ε₀’p₄       : Term ‘Context’p₄
‘ε₀’p₄       = w ‘ε₀’p₃
‘_▻_’p₄     : Term (‘Context’p₄ ‘→’ ‘Typ’p₄ ‘→'’ W ‘Context’p₄)
‘_▻_’p₄     = weakenTyp-tProd-tProd-nd-nd ‘VAR₀’

{-εp₅ : Context
εp₅ = εp₄
  ▻ (‘Context’p₄ ‘→’ ‘Typ’p₄ ‘→'’ W ‘Context’p₄) {- ‘_▻_’ -}
‘Context’p₅ : Typ εp₅
‘Context’p₅ = W ‘Context’p₄
‘Typ’p₅     : Typ (εp₅ ▻ ‘Context’p₅)
‘Typ’p₅     = W1 ‘Typ’p₄
‘Term’p₅    : Typ (εp₅ ▻ ‘Context’p₅ ▻ ‘Typ’p₅)
‘Term’p₅    = W2 ‘Term’p₄
‘ε₀’p₅       : Term ‘Context’p₅
‘ε₀’p₅       = w ‘ε₀’p₄
‘_▻Typ_’p₅     : Term (‘Context’p₅ ‘→'’ ‘Context’p₅ ‘→'’ ‘Context’p₅)
‘_▻Typ_’p₅     = w→→ ‘_▻Typ_’p₄
‘_▻_’p₅     : Term (‘Context’p₅ ‘→’ ‘Typ’p₅ ‘→'’ W ‘Context’p₅)
‘_▻_’p₅     = weakenTyp-tProd-tProd-nd-nd ‘VAR₀’-}


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

{-Context-Tower : (n : ℕ) → arrow-tower Context Context (suc n)
Context-Tower = lambda-tower _▻Typ_

Typ-Context-Tower : (n : ℕ) → Set
Typ-Context-Tower n = {Γ : Context} → arrow-tower-to-arrow {Context} {Context} Typ n (Context-Tower (suc n) Γ Γ)

‘TVAR_₀’ : (n : ℕ) → Typ-Context-Tower n
‘TVAR_₀’ n = λ {Γ} → lambda-tower-to-lambda {Context} _▻Typ_ Typ WT n Γ Γ ‘TVAR₀₀’
-}
{-‘TVAR_₁’ : (n : ℕ) → Typ-Context-Tower n
‘TVAR_₁’ n = λ {Γ} {Γ'} → {!lambda-tower-to-lambda {Context} _▻Typ_ Typ WT n Γ Γ' {!!} {-‘TVAR₀₀’-}!}-}

ε : Context
ε = εp₄

‘Context’ : Typ ε
‘Context’ = ‘Context’p₄

‘Typ’ : Typ (ε ▻ ‘Context’)
‘Typ’ = ‘Typ’p₄

‘Term’ : Typ (ε ▻ ‘Context’ ▻ ‘Typ’)
‘Term’ = ‘Term’p₄

‘ε₀’ : Term ‘Context’
‘ε₀’ = ‘ε₀’p₄

--‘_▻Typ_’ : Term (‘Context’ ‘→'’ ‘Context’ ‘→'’ ‘Context’)
--‘_▻Typ_’ = ‘_▻Typ_’p₄

‘_▻_’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→'’ W ‘Context’)
‘_▻_’ = ‘_▻_’p₄

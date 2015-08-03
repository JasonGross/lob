{-# OPTIONS --without-K #-}
module well-typed-syntax-context-helpers where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers
open import well-typed-syntax-context-pre-helpers

infixr 1 _‘‘→'’’_

□_ : Typ ε → Set
□_ T = Term {Γ = ε} T

‘Σ’ : ∀ (T : Typ ε) → Typ (ε ▻ T) → Typ ε
‘Σ’ = ‘Σ'’

‘proj₁’ : ∀ {T : Typ ε} {P : Typ (ε ▻ T)} → Term (‘Σ’ T P ‘→'’ T)
‘proj₁’ {T} {P} = ‘proj₁'’

‘proj₂’ : ∀ {T : Typ ε} {P : Typ (ε ▻ T)} → Term {ε ▻ ‘Σ’ T P} (W1 P ‘’ (w→ ‘proj₁’ ‘'’ₐ ‘VAR₀’))
‘proj₂’ {T} {P} = ‘proj₂'’

‘existT’ : ∀ {T P} (x : Term T) (p : Term (P ‘’ x)) → Term (‘Σ’ T P)
‘existT’ {T} {P} x p = S₁₀WW (S∀ (‘existT'’ ‘’ₐ x) ‘’ₐ p)

context-pick-if : ∀ {P : Context → Set}
         {Γ : Context}
         (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
         (val : P Γ) →
    P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
context-pick-if {P} {Γ} dummy val = context-pick-if-gen {P = P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} {Γ} dummy val

context-pick-if-refl : ∀ {P dummy val} →
    context-pick-if {P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} dummy val ≡ val
context-pick-if-refl {P} {dummy} {val} = context-pick-if-gen-refl {P = P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} {dummy} {val}

_‘‘→'’’_ : ∀ {Γ} → (A : □ (‘Typ’ ‘’ Γ)) → (B : □ (‘Typ’ ‘’ Γ)) → □ (‘Typ’ ‘’ Γ)
_‘‘→'’’_ {Γ = Γ} A B = (S₂₁₀WW (‘tProd-nd’ ‘t’₂ Γ ‘t’₁ A ‘t’ S₁₀W' B))

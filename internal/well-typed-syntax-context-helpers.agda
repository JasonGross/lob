{-# OPTIONS --without-K #-}
module well-typed-syntax-context-helpers where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers
open import well-typed-syntax-eq-dec
open import well-typed-initial-context

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

context-pick-if-helper : ∀ {P : Context → Set}
         {Γ : Context}
         {Γ' : Context}
         (p : dec-eq-on Γ Γ')
         (dummy : P Γ')
         (val : P Γ) →
    P Γ'
context-pick-if-helper (inj₁ refl) dummy val = val
context-pick-if-helper (inj₂ y) dummy val = dummy

context-pick-if-helper-refl : ∀ {P Γ p dummy val} → inj₁ refl ≡ p →
    context-pick-if-helper {P} {Γ} {Γ} p dummy val ≡ val
context-pick-if-helper-refl refl = refl


context-pick-if : ∀ {P : Context → Set}
         {Γ : Context}
         (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
         (val : P Γ) →
    P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
context-pick-if {P} {Γ} dummy val = context-pick-if-helper {P} {Γ} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} (_ ≟-ctx _) dummy val

context-pick-if-refl : ∀ {P dummy val} →
    context-pick-if {P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} dummy val ≡ val
context-pick-if-refl {P} {dummy} {val} = context-pick-if-helper-refl {P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} {_ ≟-ctx _} {dummy} {val} (sym (≟-ctx-refl _))

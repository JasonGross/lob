{-# OPTIONS --without-K #-}
module well-typed-syntax-context-helpers where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers

□_ : Typ ε → Set
□_ T = Term {Γ = ε} T

‘proj₁’ : ∀ {T : Typ ε} {P : Typ (ε ▻ T)} → Term (‘Σ’ T P ‘→'’ T)
‘proj₁’ {T} {P} = ‘proj₁'’

‘proj₂’ : ∀ {T : Typ ε} {P : Typ (ε ▻ T)} → Term {ε ▻ ‘Σ’ T P} (W1 P ‘’ (w→ ‘proj₁’ ‘'’ₐ ‘VAR₀’))
‘proj₂’ {T} {P} = ‘proj₂'’

‘existT’ : ∀ {T P} (x : □ T) (p : Term (P ‘’ x)) → Term (‘Σ’ T P)
‘existT’ {T} {P} x p = S₁₀WW (S∀ (‘existT'’ ‘’ₐ x) ‘’ₐ p)

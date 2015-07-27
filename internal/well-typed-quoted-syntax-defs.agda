module well-typed-quoted-syntax-defs where
open import common
open import well-typed-syntax
open import well-typed-initial-context
open import well-typed-syntax-helpers
open import well-typed-syntax-context-helpers

postulate cheat : ∀ {T : Set} → T

mutual
  abstract
    ⌜_⌝c : Context → Term {Γ = ε} ‘Context’
    ⌜ ε₀ ⌝c = ‘ε₀’
    ⌜ Γ ▻ x ⌝c = S₁₀WW (S∀ (‘_▻_’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ x ⌝T)
    ⌜ Γ ▻Typε ⌝c = cheat
    ⌜ Γ ▻Typ₁ x ⌝c = cheat
    ⌜ Γ ▻Typ₂ A ▻T x ⌝c = cheat
    ⌜ Γ ▻Typ₃ A ▻T B ▻T x ⌝c = cheat
{-    ⌜ ε₀ ⌝c = ‘ε₀’
    ⌜ Γ ▻Typ Γ₁ ⌝c = ‘_▻Typ_’ ‘'’ₐ ⌜ Γ₁ ⌝c ‘'’ₐ ⌜ Γ₁ ⌝c
    ⌜ Γ ▻ x ⌝c = S₁₀WW (S∀ (‘_▻_’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ x ⌝T)-}

    ⌜_⌝T : ∀ {Γ} → Typ Γ → □ (‘Typ’ ‘’ ⌜ Γ ⌝c)
    ⌜ x₁ ‘’ x₂ ⌝T = cheat
    ⌜ x₂ ‘’₁ a ⌝T = cheat
    ⌜ x₃ ‘’₂ a ⌝T = cheat
    ⌜ x₄ ‘’₃ a ⌝T = cheat
    ⌜ W x₁ ⌝T = cheat
    ⌜ W1 x₂ ⌝T = cheat
    ⌜ W2 x₃ ⌝T = cheat
    ⌜ x ‘→’ x₁ ⌝T = cheat
    ⌜ WT x ⌝T = cheat
    ⌜ WT₁ x₁ ⌝T = cheat
    ⌜ WT₁₂ x₂ ⌝T = cheat
    ⌜ ‘TVAR₀₀’ ⌝T = cheat
    ⌜ ‘TVAR₀₁’ ⌝T = cheat
    ⌜ ‘TVAR₀₂’ ⌝T = cheat
    ⌜ ‘Σ'’ x x₁ ⌝T = cheat

    ⌜_⌝t : ∀ {Γ} {A : Typ Γ} → Term {Γ = Γ} A → □ (‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ A ⌝T)
    ⌜ x ⌝t = cheat

‘context-extend’ : Term {Γ = (ε ▻ ‘Context’ ▻ ‘Typ’)} (W (W ‘Context’))
‘context-extend’ = un‘λ'∙’ (un‘λ∙’ ‘_▻_’)

_‘▻’_ : (Γ : □ ‘Context’) → □ (‘Typ’ ‘’ Γ) → □ ‘Context’
Γ ‘▻’ x = (S₁₀WW (‘context-extend’ ‘t’₁ Γ ‘t’ x))

‘ε’ : Term {Γ = ε} ‘Context’
‘ε’ = ⌜ ε ⌝c

‘□’ : Typ (ε ▻ ‘Typ’ ‘’ ‘ε’)
‘□’ = ‘Term’ ‘’₁ ‘ε’

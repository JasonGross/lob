{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax-defs where
open import common
open import well-typed-syntax
open import well-typed-initial-context
open import well-typed-syntax-helpers
open import well-typed-syntax-helpers-postulates
open import well-typed-syntax-context-helpers

postulate cheat : ∀ {T : Set} → T

abstract
  mutual
    ⌜_⌝c : Context → Term {Γ = ε} ‘Context’
    ⌜ ε₀ ⌝c = ‘ε₀’
    ⌜ Γ ▻ x ⌝c = S₁₀WW (S∀ (‘_▻_’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ x ⌝T)

    ⌜_⌝T : ∀ {Γ} → Typ Γ → □ (‘Typ’ ‘’ ⌜ Γ ⌝c)
    ⌜ x₁ ‘’ x₂ ⌝T = cheat
    ⌜ x₂ ‘’₁ a ⌝T = cheat
    ⌜ x₃ ‘’₂ a ⌝T = cheat
    ⌜ x₄ ‘’₃ a ⌝T = cheat
    ⌜ W x₁ ⌝T = cheat
    ⌜ W1 x₂ ⌝T = cheat
    ⌜ W2 x₃ ⌝T = cheat
    ⌜ ‘Set’ ⌝T = cheat
    ⌜ El x ⌝T = cheat
    ⌜ x ‘→’ x₁ ⌝T = cheat
    ⌜ ‘Σ'’ {Γ} x x₁ ⌝T = S₁₀W (S₂₁₀W (S₁₀∀ (S∀ (‘‘Σ'’’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ x ⌝T) ‘’ₐ S₀₁₀W1W1' ⌜ x₁ ⌝T))

    ⌜_⌝t : ∀ {Γ} {A : Typ Γ} → Term {Γ = Γ} A → □ (‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ A ⌝T)
    ⌜ x ⌝t = cheat

  distr⌜▻⌝ : ∀ {Γ a}
    → Term (‘Typ’ ‘’ ⌜ Γ ▻ a ⌝c)
    → Term (‘Typ’ ‘’ S₁₀WW (S∀ (‘_▻_’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ a ⌝T))
  distr⌜▻⌝ x = x

  distr⌜‘Σ'’⌝ : ∀ {ℓ Γ a b} (P : □ (‘Typ’ ‘’ ⌜ Γ ⌝c) → Set ℓ)
    → P (S₁₀W (S₂₁₀W (S₁₀∀ (S∀ (‘‘Σ'’’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ a ⌝T) ‘’ₐ S₀₁₀W1W1' (distr⌜▻⌝ ⌜ b ⌝T))))
    → P ⌜ ‘Σ'’ {Γ} a b ⌝T
  distr⌜‘Σ'’⌝ P x = x


‘context-extend’ : Term {Γ = (ε ▻ ‘Context’ ▻ ‘Typ’)} (W (W ‘Context’))
‘context-extend’ = un‘λ'∙’ (un‘λ∙’ ‘_▻_’)

_‘▻’_ : (Γ : □ ‘Context’) → □ (‘Typ’ ‘’ Γ) → □ ‘Context’
Γ ‘▻’ x = (S₁₀WW (‘context-extend’ ‘t’₁ Γ ‘t’ x))

‘ε’ : Term {Γ = ε} ‘Context’
‘ε’ = ⌜ ε ⌝c

‘□’ : Typ (ε ▻ ‘Typ’ ‘’ ‘ε’)
‘□’ = ‘Term’ ‘’₁ ‘ε’

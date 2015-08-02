{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax-defs where
open import common
open import well-typed-syntax
open import well-typed-initial-context
open import well-typed-syntax-helpers
open import well-typed-syntax-helpers-postulates
open import well-typed-syntax-context-helpers

infixl 3 _‘‘’’_

postulate cheat : ∀ {T : Set} → T

abstract
  mutual
    ⌜_⌝c : Context → Term {Γ = ε} ‘Context’
    ⌜ ε₀ ⌝c = ‘ε₀’
    ⌜ Γ ▻ x ⌝c = S₁₀WW (S∀ (‘_▻_’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ x ⌝T)

    ⌜_⌝T : ∀ {Γ} → Typ Γ → □ (‘Typ’ ‘’ ⌜ Γ ⌝c)
    ⌜ _‘’_ {Γ} {A} T x ⌝T = S₂₁₀WW (S₁₀∀ (S→ (S∀→ (‘_‘’_’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ A ⌝T) ‘'’ₐ S₀₁₀W1W1' ⌜ T ⌝T) ‘’ₐ ⌜ x ⌝t)
    ⌜ x₂ ‘’₁ a ⌝T = cheat
    ⌜ x₃ ‘’₂ a ⌝T = cheat
    ⌜ x₄ ‘’₃ a ⌝T = cheat
    ⌜ W {Γ} {A} T ⌝T = S₀₁₀W1W1 (S₁₀W (S∀ (S∀→ (‘W’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ A ⌝T) ‘’ₐ S₁₀W' ⌜ T ⌝T))
    ⌜ W1 x₂ ⌝T = cheat
    ⌜ W2 x₃ ⌝T = cheat
    ⌜ ‘Set’ ⌝T = cheat
    ⌜ El x ⌝T = cheat
    ⌜ _‘→’_ {Γ} A B ⌝T = S₁₀W (S→ (S∀→ (‘_‘→’_’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ A ⌝T) ‘'’ₐ S₀₁₀W1W1' ⌜ B ⌝T)
    ⌜ ‘Σ'’ {Γ} x x₁ ⌝T = S₁₀W (S₂₁₀W (S₁₀∀ (S∀ (‘‘Σ'’’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ x ⌝T) ‘’ₐ S₀₁₀W1W1' ⌜ x₁ ⌝T))

    ⌜_⌝t : ∀ {Γ} {A : Typ Γ} → Term {Γ = Γ} A → □ (‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ A ⌝T)
    ⌜ x ⌝t = cheat

  distrP⌜▻⌝ : ∀ {Γ a ℓ} (P : □ ‘Context’ → Set ℓ)
    → P ⌜ Γ ▻ a ⌝c
    → P (S₁₀WW (S∀ (‘_▻_’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ a ⌝T))
  distrP⌜▻⌝ P x = x

  distr⌜‘Σ'’⌝ : ∀ {ℓ Γ a b} (P : □ (‘Typ’ ‘’ ⌜ Γ ⌝c) → Set ℓ)
    → P (S₁₀W (S₂₁₀W (S₁₀∀ (S∀ (‘‘Σ'’’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ a ⌝T) ‘’ₐ S₀₁₀W1W1' (distrP⌜▻⌝ (λ Γ▻a → Term (‘Typ’ ‘’ Γ▻a)) ⌜ b ⌝T))))
    → P ⌜ ‘Σ'’ {Γ} a b ⌝T
  distr⌜‘Σ'’⌝ P x = x

distr⌜▻⌝ : ∀ {Γ a}
  → Term (‘Typ’ ‘’ ⌜ Γ ▻ a ⌝c)
  → Term (‘Typ’ ‘’ S₁₀WW (S∀ (‘_▻_’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ a ⌝T))
distr⌜▻⌝ = distrP⌜▻⌝ (λ Γ▻a → Term (‘Typ’ ‘’ Γ▻a))

‘context-extend’ : Term {Γ = (ε ▻ ‘Context’ ▻ ‘Typ’)} (W (W ‘Context’))
‘context-extend’ = un‘λ'∙’ (un‘λ∙’ ‘_▻_’)

_‘▻’_ : (Γ : □ ‘Context’) → □ (‘Typ’ ‘’ Γ) → □ ‘Context’
Γ ‘▻’ x = (S₁₀WW (S∀ (‘_▻_’ ‘’ₐ Γ) ‘’ₐ x))

‘ε’ : Term {Γ = ε} ‘Context’
‘ε’ = ⌜ ε ⌝c

‘□’ : Typ (ε ▻ ‘Typ’ ‘’ ‘ε’)
‘□’ = ‘Term’ ‘’₁ ‘ε’

‘substTyp’ : ∀ {Γ} {A : Term {ε} (‘Typ’ ‘’ Γ)} →
  □ (‘Typ’ ‘’ (Γ ‘▻’ A)
      ‘→'’ ‘Term’ ‘’₁ Γ ‘’ A
      ‘→'’ ‘Typ’ ‘’ Γ)
‘substTyp’ {Γ} {A} = ‘λ'∙’
                       (weakenTyp-tProd-nd-inv
                        (‘λ'∙’
                         (WWS₁₀W (un‘λ'∙’ (w→→ (S→→ (S∀→→ (‘_‘’_’ ‘’ₐ Γ) ‘’ₐ A)) ‘'’ₐ WS₀₁₀W1W1' ‘VAR₀’)))))

_‘‘’’_ : ∀ {Γ} {A : □ (‘Typ’ ‘’ Γ)}
  → □ (‘Typ’ ‘’ (Γ ‘▻’ A))
  → □ (‘Term’ ‘’₁ Γ ‘’ A)
  → □ (‘Typ’ ‘’ Γ)
f ‘‘’’ x = (‘substTyp’ ‘'’ₐ f ‘'’ₐ x)

‘‘Σ’’ : ∀ {Γ} (A : □ (‘Typ’ ‘’ Γ)) (B : □ (‘Typ’ ‘’ (Γ ‘▻’ A))) → □ (‘Typ’ ‘’ Γ)
‘‘Σ’’ {Γ} A B = S₁₀W (S₂₁₀W (S₁₀∀ (S∀ (‘‘Σ'’’ ‘’ₐ Γ) ‘’ₐ A) ‘’ₐ S₀₁₀W1W1' B))

{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax-defs where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers
open import well-typed-syntax-helpers-postulates
open import well-typed-syntax-context-helpers

infixl 3 _‘‘’’_

‘ε’ : Term {Γ = ε} ‘Context’
‘ε’ = ⌜ ε ⌝c

‘□’ : Typ (ε ▻ ‘Typ’ ‘’ ‘ε’)
‘□’ = ‘Term’ ‘’₁ ‘ε’

_‘‘’’_ : ∀ {Γ} {A : Typ Γ}
  → □ (‘Typ’ ‘’ ⌜ Γ ▻ A ⌝c)
  → □ (‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ A ⌝T)
  → □ (‘Typ’ ‘’ ⌜ Γ ⌝c)
f ‘‘’’ x = (‘substTyp’ ‘'’ₐ f ‘'’ₐ x)

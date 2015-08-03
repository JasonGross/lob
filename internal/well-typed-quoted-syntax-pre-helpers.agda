{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax-pre-helpers where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers
open import well-typed-syntax-context-helpers
open import well-typed-quoted-syntax-defs public

‘context-pick-if’ : ∀ (dummy : Term (‘Typ’ ‘’ ⌜ (ε ▻ ‘Σ’ ‘Context’ ‘Typ’) ⌝c))
  → □ (‘Context’ ‘→’ ‘Typ’ ‘→'’ W (‘Typ’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c))
‘context-pick-if’ dummy = S→W∀W1→W (‘context-pick-if'’ ‘’ₐ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c) ‘'’ₐ dummy

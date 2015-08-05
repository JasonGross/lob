{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax-defs where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers
open import well-typed-syntax-context-helpers

‘ε’ : Term {Γ = ε} ‘Context’
‘ε’ = ⌜ ε ⌝c

‘□’ : Typ (ε ▻ ‘Typ’ ‘’ ‘ε’)
‘□’ = ‘Term’ ‘’₁ ‘ε’

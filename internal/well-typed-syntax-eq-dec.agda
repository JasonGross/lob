{-# OPTIONS --without-K #-}
module well-typed-syntax-eq-dec where
open import well-typed-syntax
open import common

context-pick-if : ∀ {ℓ} {P : Context → Set ℓ}
                        {Γ : Context}
                        (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
                        (val : P Γ) →
                      P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
context-pick-if {P = P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} dummy val = val
context-pick-if {P = P} {Γ} dummy val = dummy

context-pick-if-refl : ∀ {ℓ P dummy val} →
                           context-pick-if {ℓ} {P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} dummy val ≡ val
context-pick-if-refl {P = P} = refl

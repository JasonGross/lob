{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax where
open import common
open import well-typed-syntax
open import well-typed-quoted-syntax1 public
open import well-typed-syntax-context-pre-helpers

context-pick-if : ∀ {P : Context → Set}
         {Γ : Context}
         (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
         (val : P Γ) →
    P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
context-pick-if {P} {Γ} dummy val = context-pick-if-gen {P = P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} {Γ} dummy val

context-pick-if-refl : ∀ {P dummy val} →
    context-pick-if {P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} dummy val ≡ val
context-pick-if-refl {P} {dummy} {val} = context-pick-if-gen-refl {P = P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} {dummy} {val}

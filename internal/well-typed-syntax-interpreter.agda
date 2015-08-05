{-# OPTIONS --without-K #-}
module well-typed-syntax-interpreter where
open import common public
open import well-typed-syntax
import well-typed-syntax-pre-interpreter
open import well-typed-syntax-eq-dec

max-level : Level
max-level = well-typed-syntax-pre-interpreter.max-level

Context⇓ : (Γ : Context) → Set (lsuc max-level)
Context⇓ = well-typed-syntax-pre-interpreter.inner.Context⇓
           (λ ℓ P Γ' dummy val → context-pick-if {P = P} dummy val)
           (λ ℓ P dummy val → context-pick-if-refl {P = P} {dummy})

Typ⇓ : {Γ : Context} → Typ Γ → Context⇓ Γ → Set max-level
Typ⇓ = well-typed-syntax-pre-interpreter.inner.Typ⇓
       (λ ℓ P Γ' dummy val → context-pick-if {P = P} dummy val)
       (λ ℓ P dummy val → context-pick-if-refl {P = P} {dummy})

Term⇓ : ∀ {Γ : Context} {T : Typ Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Typ⇓ T Γ⇓
Term⇓ = well-typed-syntax-pre-interpreter.inner.Term⇓
        (λ ℓ P Γ' dummy val → context-pick-if {P = P} dummy val)
        (λ ℓ P dummy val → context-pick-if-refl {P = P} {dummy})

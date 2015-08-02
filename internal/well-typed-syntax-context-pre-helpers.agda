{-# OPTIONS --without-K #-}
module well-typed-syntax-context-pre-helpers where
open import common
open import well-typed-syntax
open import well-typed-syntax-eq-dec

context-pick-if-helper : ∀ {ℓ} {P : Context → Set ℓ}
         {Γ : Context}
         {Γ' : Context}
         (p : dec-eq-on Γ Γ')
         (dummy : P Γ')
         (val : P Γ) →
    P Γ'
context-pick-if-helper (inj₁ refl) dummy val = val
context-pick-if-helper (inj₂ y) dummy val = dummy

context-pick-if-helper-refl : ∀ {ℓ P Γ p dummy val} → inj₁ refl ≡ p →
    context-pick-if-helper {ℓ} {P} {Γ} {Γ} p dummy val ≡ val
context-pick-if-helper-refl refl = refl


context-pick-if-gen : ∀ {ℓ} {P : Context → Set ℓ}
         {Γ' Γ : Context}
         (dummy : P Γ')
         (val : P Γ) →
    P Γ'
context-pick-if-gen {ℓ} {P} {Γ'} {Γ} dummy val = context-pick-if-helper {ℓ} {P} {Γ} {Γ'} (_ ≟-ctx _) dummy val

context-pick-if-gen-refl : ∀ {ℓ P Γ dummy val} →
    context-pick-if-gen {ℓ} {P} {Γ} {Γ} dummy val ≡ val
context-pick-if-gen-refl {ℓ} {P} {Γ} {dummy} {val} = context-pick-if-helper-refl {ℓ} {P} {Γ} {_ ≟-ctx _} {dummy} {val} (sym (≟-ctx-refl _))

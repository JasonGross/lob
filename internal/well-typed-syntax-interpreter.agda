{-# OPTIONS --without-K #-}
module well-typed-syntax-interpreter where
open import well-typed-syntax
import well-typed-syntax-pre-interpreter
open import well-typed-syntax-context-pre-helpers

Context⇓ : (Γ : Context) → Set (lsuc max-level)
Context⇓ = well-typed-syntax-pre-interpreter.inner.Context⇓

Typ⇓ : {Γ : Context} → Typ Γ → Context⇓ Γ → Set max-level
Typ⇓ = well-typed-syntax-pre-interpreter.inner.Typ⇓

Term⇓ : ∀ {Γ : Context} {T : Typ Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Typ⇓ T Γ⇓
Term⇓ = well-typed-syntax-pre-interpreter.inner.Term⇓

{-# OPTIONS --without-K #-}
module well-typed-syntax-interpreter-full where
open import common public
open import well-typed-syntax
open import well-typed-syntax-interpreter

Contextε⇓ : Context⇓ ε
Contextε⇓ = tt

Typε⇓ : Typ ε → Set max-level
Typε⇓ T = Typ⇓ T Contextε⇓

Termε⇓ : {T : Typ ε} → Term T → Typε⇓ T
Termε⇓ t = Term⇓ t Contextε⇓

Typε▻⇓ : ∀ {A} → Typ (ε ▻ A) → Typε⇓ A → Set max-level
Typε▻⇓ T A⇓ = Typ⇓ T (Contextε⇓ , A⇓)

Termε▻⇓ : ∀ {A} → {T : Typ (ε ▻ A)} → Term T → (x : Typε⇓ A) → Typε▻⇓ T x
Termε▻⇓ t x = Term⇓ t (Contextε⇓ , x)

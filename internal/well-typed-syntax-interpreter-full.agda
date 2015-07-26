module well-typed-syntax-interpreter-full where
open import common public
open import well-typed-syntax
open import well-typed-syntax-interpreter
open import well-typed-initial-context-internal


Contextε⇓ : Context⇓ ε
Contextε⇓ = tt , Context , Typ , (λ Γ → Term {Γ}) , ε₀ , _▻_ -- , {!!} , {!!}

Typε⇓ : Typ ε → Set max-level
Typε⇓ T = Typ⇓ T Contextε⇓

Termε⇓ : {T : Typ ε} → Term T → Typε⇓ T
Termε⇓ t = Term⇓ t Contextε⇓

Typε▻⇓ : ∀ {A} → Typ (ε ▻ A) → Typε⇓ A → Set max-level
Typε▻⇓ T A⇓ = Typ⇓ T (Contextε⇓ , A⇓)

Termε▻⇓ : ∀ {A} → {T : Typ (ε ▻ A)} → Term T → (x : Typε⇓ A) → Typε▻⇓ T x
Termε▻⇓ t x = Term⇓ t (Contextε⇓ , x)

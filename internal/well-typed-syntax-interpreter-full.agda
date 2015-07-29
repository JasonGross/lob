module well-typed-syntax-interpreter-full where
open import common public
open import well-typed-syntax
open import well-typed-syntax-interpreter
open import well-typed-initial-context-internal

lift→ : ∀ {ℓ ℓ′ ℓ′′ A} {R : Set ℓ′′} → (A → R) → (Lifted {ℓ} {ℓ′} A → R)
lift→ f (lift x) = f x

lift→→ : ∀ {ℓ ℓ′ ℓ′′ ℓ′′′ ℓ′′′′ A B} {R : Set ℓ′′′′} → ((x : A) → B x → R) → ((x : Lifted {ℓ} {ℓ′} A) → Lifted {ℓ′′} {ℓ′′′} (lift→ B x) → R)
lift→→ f (lift x) (lift y) = f x y

Context' : Set₀
Context' = Context

Typ' : (Γ⇓ : Lifted {_} {max-level} Context') → Set₀
Typ' = lift→ Typ

Term' : (Γ⇓ : Lifted {_} {max-level} Context') → (T⇓ : Lifted {_} {max-level} (Typ' Γ⇓)) → Set₀
Term' = lift→→ (λ Γ → Term {Γ})

ε₀' : Lifted {_} {max-level} Context'
ε₀' = lift ε₀

_▻'_ : (Γ⇓ : Lifted {_} {max-level} Context') → (T⇓ : Lifted {_} {max-level} (Typ' Γ⇓)) → Lifted {_} {max-level} Context'
Γ⇓ ▻' T⇓ = lift (lift→→ _▻_ Γ⇓ T⇓)

Contextε⇓ : Context⇓ ε
Contextε⇓ = tt , Context' , Typ' , Term' , ε₀' , _▻'_ -- , {!!} , {!!}

Typε⇓ : Typ ε → Set max-level
Typε⇓ T = Typ⇓ T Contextε⇓

Termε⇓ : {T : Typ ε} → Term T → Typε⇓ T
Termε⇓ t = Term⇓ t Contextε⇓

Typε▻⇓ : ∀ {A} → Typ (ε ▻ A) → Typε⇓ A → Set max-level
Typε▻⇓ T A⇓ = Typ⇓ T (Contextε⇓ , A⇓)

Termε▻⇓ : ∀ {A} → {T : Typ (ε ▻ A)} → Term T → (x : Typε⇓ A) → Typε▻⇓ T x
Termε▻⇓ t x = Term⇓ t (Contextε⇓ , x)

{-# OPTIONS --without-K #-}
module well-typed-syntax-interpreter-full where
open import common public
open import well-typed-syntax
open import well-typed-syntax-interpreter
open import well-typed-initial-context-internal

lift→ : ∀ {ℓ ℓ′ ℓ′′ A} {R : Set ℓ′′} → (A → R) → (Lifted {ℓ} {ℓ′} A → R)
lift→ f (lift x) = f x

lift→→ : ∀ {ℓ ℓ′ ℓ′′ ℓ′′′ ℓ′′′′ A B} {R : Set ℓ′′′′} → ((x : A) → B x → R) → ((x : Lifted {ℓ} {ℓ′} A) → Lifted {ℓ′′} {ℓ′′′} (lift→ B x) → R)
lift→→ f (lift x) (lift y) = f x y

lift→→→ : ∀ {ℓ₀ ℓ ℓ′ ℓ′′ ℓ′′′ ℓ′′′′ ℓ′′′′′ A B C} {R : Set ℓ₀} → ((x : A) → (y : B x) → C x y → R)
  → ((x : Lifted {ℓ} {ℓ′} A) → (y : Lifted {ℓ′′} {ℓ′′′} (lift→ B x)) → Lifted {ℓ′′′′} {ℓ′′′′′} (lift→→ C x y) → R)
lift→→→ f (lift x) (lift y) (lift z) = f x y z

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

‘Σ'’' : (Γ⇓ : Lifted {_} {max-level} Context')
  → (T⇓ : Lifted {_} {max-level} (Typ' Γ⇓))
  → Lifted {_} {max-level} (Typ' (Γ⇓ ▻' T⇓))
  → Lifted {_} {max-level} (Typ' Γ⇓)
‘Σ'’' (lift Γ) (lift T) (lift P) = lift (‘Σ'’ {Γ} T P)

_‘’'_ : (Γ⇓ : Lifted {_} {max-level} Context')
  → (T⇓ : Lifted {_} {max-level} (Typ' Γ⇓))
  → Lifted {_} {max-level} (Typ' (Γ⇓ ▻' T⇓))
  → Lifted {_} {max-level} (Term' Γ⇓ T⇓)
  → Lifted {_} {max-level} (Typ' Γ⇓)
_‘’'_ (lift Γ) (lift A) (lift T) (lift a) = lift (T ‘’ a)

_‘→’'_ : (Γ⇓ : Lifted {_} {max-level} Context')
  → (T⇓ : Lifted {_} {max-level} (Typ' Γ⇓))
  → Lifted {_} {max-level} (Typ' (Γ⇓ ▻' T⇓))
  → Lifted {_} {max-level} (Typ' Γ⇓)
_‘→’'_ (lift Γ) (lift A) (lift B) = lift (A ‘→’ B)

W' : (Γ⇓ : Lifted {_} {max-level} Context')
  → (T⇓ : Lifted {_} {max-level} (Typ' Γ⇓))
  → Lifted {_} {max-level} (Typ' Γ⇓)
  → Lifted {_} {max-level} (Typ' (Γ⇓ ▻' T⇓))
W' (lift Γ) (lift A) (lift B) = lift (W B)


Contextε⇓ : Context⇓ ε
Contextε⇓ = tt , Context' , Typ' , Term' , ε₀' , _▻'_ , ‘Σ'’' , _‘’'_ , _‘→’'_ , W' -- , {!!} , {!!}

Typε⇓ : Typ ε → Set max-level
Typε⇓ T = Typ⇓ T Contextε⇓

Termε⇓ : {T : Typ ε} → Term T → Typε⇓ T
Termε⇓ t = Term⇓ t Contextε⇓

Typε▻⇓ : ∀ {A} → Typ (ε ▻ A) → Typε⇓ A → Set max-level
Typε▻⇓ T A⇓ = Typ⇓ T (Contextε⇓ , A⇓)

Termε▻⇓ : ∀ {A} → {T : Typ (ε ▻ A)} → Term T → (x : Typε⇓ A) → Typε▻⇓ T x
Termε▻⇓ t x = Term⇓ t (Contextε⇓ , x)

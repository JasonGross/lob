module well-typed-syntax-interpreter-full where
open import common public
open import well-typed-syntax
open import well-typed-syntax-interpreter
open import well-typed-initial-context

Context' : ∀ {ℓ} → ⊤ {ℓ} → Set
Context' _ = Context

Typ' : Context⇓ (ε₀ ▻Typ ε₀ ▻ ‘TVAR₀₀’) → Set
Typ' (tt , proj₂ , proj₃) = {!!}

Contextε⇓ : Context⇓ ε
Contextε⇓ = tt , Context' , Typ' , {!!} , {!!} , {!!} , {!!}

Typε⇓ : Typ ε → Set max-level
Typε⇓ T = Typ⇓ T Contextε⇓

Termε⇓ : {T : Typ ε} → Term T → Typε⇓ T
Termε⇓ t = Term⇓ t Contextε⇓

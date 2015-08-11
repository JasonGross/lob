{-# OPTIONS --without-K #-}
module mini-lob where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixr 1 _‘→’_
infixl 3 _‘’ₐ_
infixr 2 _‘∘’_

mutual
  data Context : Set where
    ε : Context
    _▻_ : (Γ : Context) → Type Γ → Context

  data Type : Context → Set where
    _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
    ‘Typeε’ : Type ε
    ‘□’ : Type (ε ▻ ‘Typeε’)
    _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
    ‘⊤’ : ∀ {Γ} → Type Γ
    ‘⊥’ : ∀ {Γ} → Type Γ

  data Term : {Γ : Context} → Type Γ → Set where
    ⌜_⌝ : Type ε → Term {ε} ‘Typeε’
    ⌜_⌝t : ∀ {T} → Term {ε} T → Term {ε} (‘□’ ‘’ ⌜ T ⌝)
    _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
    Lӧb : ∀ {X} → Term {ε} (‘□’ ‘’ ⌜ X ⌝ ‘→’ X) → Term {ε} X
    →Lӧb : ∀ {P} → Term {ε} (‘□’ ‘’ (P ‘’ₐ ⌜ Lӧb {‘Typeε’} P ⌝t) ‘→’ ‘□’ ‘’ Lӧb {‘Typeε’} P)
    ←Lӧb : ∀ {P} → Term {ε} (‘□’ ‘’ Lӧb {‘Typeε’} P ‘→’ ‘□’ ‘’ (P ‘’ₐ ⌜ Lӧb {‘Typeε’} P ⌝t))
    ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
    ‘λx∙x’ : ∀ {Γ A} → Term {Γ} (A ‘→’ A)
    _‘∘’_ : ∀ {Γ A B C} → Term {Γ} (B ‘→’ C) → Term {Γ} (A ‘→’ B) → Term {Γ} (A ‘→’ C)

□ : Type ε → Set _
□ = Term {ε}

max-level : Level
max-level = lzero

mutual
  Context⇓ : (Γ : Context) → Set (lsuc max-level)
  Context⇓ ε = ⊤
  Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

  Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
  Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
  Type⇓ ‘Typeε’ Γ⇓ = Lifted (Type ε)
  Type⇓ ‘□’ Γ⇓ = Lifted (Term {ε} (lower (Σ.proj₂ Γ⇓)))
  Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
  Type⇓ ‘⊤’ Γ⇓ = ⊤
  Type⇓ ‘⊥’ Γ⇓ = ⊥

  Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓
  Term⇓ ⌜ x ⌝ Γ⇓ = lift x
  Term⇓ ⌜ x ⌝t Γ⇓ = lift x
  Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
  Term⇓ (Lӧb □‘X’→X) Γ⇓ = Term⇓ □‘X’→X Γ⇓ (lift (Lӧb □‘X’→X))
  Term⇓ ‘tt’ Γ⇓ = tt
  Term⇓ ‘λx∙x’ Γ⇓ x = x
  Term⇓ (g ‘∘’ f) Γ⇓ x = Term⇓ g Γ⇓ (Term⇓ f Γ⇓ x)
  Term⇓ →Lӧb Γ⇓ x = x
  Term⇓ ←Lӧb Γ⇓ x = x
  --Term⇓ (S‘⊤’ v) Γ⇓ = tt

⌞_⌟ : Type ε → Set _
⌞ T ⌟ = Type⇓ T tt

‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
‘¬’ T = T ‘→’ ‘⊥’

lӧb : ∀ {‘X’} → □ (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = Term⇓ (Lӧb f) tt

incompleteness : ¬ □ (‘¬’ (‘□’ ‘’ ⌜ ‘⊥’ ⌝))
incompleteness = lӧb

soundness : ¬ □ ‘⊥’
soundness x = Term⇓ x tt

non-emptyness : Σ (Type ε) (λ T → □ T)
non-emptyness = ‘⊤’ , ‘tt’

module modal-fixpoint where
  {-mutual
    count-worlds-under-c : Context → Set
    count-worlds-under-c ε = ⊤
    count-worlds-under-c (Γ ▻ x) = Σ (λ (_ : Term x) → count-worlds-under-c Γ)

    count-worlds : ∀ {Γ} → Type Γ → count-worlds-under-c Γ → ℕ
    count-worlds {Γ} (T₁ ‘’ x) v = count-worlds T₁ (x , v)
    count-worlds {.ε} ‘Typeε’ v = 0
    count-worlds {.ε ▻ ‘Typeε’} ‘□’ v = 1 + {!!}
    count-worlds {Γ} (T ‘→’ T₁) v = max (count-worlds T v) (count-worlds T₁ v)
    count-worlds {Γ} ‘⊤’ v = 0
    count-worlds {Γ} ‘⊥’ v = 0

{-    count-worlds-t : ∀ {T} → Term {ε} T → ℕ
    count-worlds-t ⌜ x ⌝ = count-worlds x tt
    count-worlds-t (t ‘’ₐ t₁) = count-worlds-t t {!!}
    count-worlds-t (Lӧb t) v = {!!}
    count-worlds-t ‘tt’ v = {!!}-}
-}
  context-to-term : Context → Set
  context-to-term ε = ⊤
  context-to-term (Γ ▻ x) = Σ (context-to-term Γ) (λ _ → Term x)

  Type-in : ∀ {Γ} → Type Γ → context-to-term Γ → Type ε
  Type-in {ε} T v = T
  Type-in (T ‘→’ T₁) v = (Type-in T v) ‘→’ (Type-in T₁ v)
  Type-in ‘⊤’ v = ‘⊤’
  Type-in ‘⊥’ v = ‘⊥’
  Type-in {Γ ▻ x} T v = Type-in (T ‘’ Σ.proj₂ v) (Σ.proj₁ v)

  kripke-reduce : ∀ {Γ} → Type Γ → context-to-term Γ → Type ε
  kripke-reduce ‘□’ v = lower (Term⇓ (Σ.proj₂ v) tt)
  kripke-reduce ‘Typeε’ v = ‘Typeε’
  kripke-reduce (T₁ ‘’ x) v = kripke-reduce T₁ (v , x)
  kripke-reduce (T ‘→’ T₁) v = kripke-reduce T v ‘→’ kripke-reduce T₁ v
  kripke-reduce ‘⊤’ v = ‘⊤’
  kripke-reduce ‘⊥’ v = ‘⊥’

  kripke-eval' : ℕ → Type ε → Type ε
  kripke-eval' 0 T = T
  kripke-eval' (suc n) T = kripke-eval' n (kripke-reduce T tt)

  kripke-finalize : ∀ {Γ} → Type Γ → context-to-term Γ → Type ε
  kripke-finalize (T₁ ‘’ x) v = kripke-finalize T₁ (v , x)
  kripke-finalize ‘Typeε’ v = ‘Typeε’
  kripke-finalize ‘□’ v = ‘⊤’
  kripke-finalize (T ‘→’ T₁) v = kripke-finalize T v ‘→’ kripke-finalize T₁ v
  kripke-finalize ‘⊤’ v = ‘⊤’
  kripke-finalize ‘⊥’ v = ‘⊥’

  box-free? : ∀ {Γ} → Type Γ → context-to-term Γ → Set
  box-free? (T₁ ‘’ x) v = box-free? T₁ (v , x)
  box-free? ‘Typeε’ v = ⊤
  box-free? ‘□’ v = ⊥
  box-free? (T ‘→’ T₁) v = box-free? T v × box-free? T₁ v
  box-free? ‘⊤’ v = ⊤
  box-free? ‘⊥’ v = ⊤

  mutual
    kripke-lift→ : ∀ (n : ℕ) (T : Type ε) → box-free? (kripke-eval' n T) tt
      → Term (kripke-eval' n T ‘→’ T)
    kripke-lift→ zero T H = ‘λx∙x’
    kripke-lift→ (suc n) (T₁ ‘’ x) H = {!!}
    kripke-lift→ (suc n) (T ‘→’ T₁) H = {!!} ‘∘’ (kripke-lift→ n (kripke-reduce (T ‘→’ T₁) tt) H)
    kripke-lift→ (suc n) ‘Typeε’ H = kripke-lift→ n _ H
    kripke-lift→ (suc n) ‘⊤’ H = kripke-lift→ n _ H
    kripke-lift→ (suc n) ‘⊥’ H = kripke-lift→ n _ H

    kripke-lift← : ∀ (n : ℕ) (T : Type ε) → box-free? (kripke-eval' n T) tt
      → Term (kripke-eval' n T)
      → Term T
    kripke-lift← n T H t = {!!}
{-    kripke-lift : ∀ {Γ} (T : Type Γ) v → Term (kripke-reduce T v ‘→’ Type-in T v)
    kripke-lift (T₁ ‘’ x) = {!!}
    kripke-lift ‘Typeε’ v = {!!}
    kripke-lift ‘□’ v = {!!}
    kripke-lift {ε} (T ‘→’ T₁) v = {!!}
  kripke-lift {Γ ▻ x} (T ‘→’ T₁) v = {!!}
  kripke-lift ‘⊤’ v = {!!}
  kripke-lift ‘⊥’ v = {!!}-}

  Quine : Type (ε ▻ ‘Typeε’) → Type ε
  Quine φ = {!!}

  quine→ : ∀ {φ} → Term {ε} (Quine φ        ‘→’ φ ‘’ ⌜ Quine φ ⌝)
  quine← : ∀ {φ} → Term {ε} (φ ‘’ ⌜ Quine φ ⌝ ‘→’ Quine φ)

  quine→ = {!!}
  quine← = {!!}

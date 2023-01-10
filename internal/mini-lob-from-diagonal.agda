{-# OPTIONS --without-K #-}
module mini-lob-from-diagonal where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixr 1 _‘→’_
infixr 2 _‘×’_
infixr 2 _‘××’_
infixr 1 _‘≡’_
infixl 3 _‘’ₐ_
infixl 3 _‘∘’_

data Context : Set
data Type : Context → Set
data Term : {Γ : Context} → Type Γ → Set

data Context where
  ε : Context
  _▻_ : (Γ : Context) → Type Γ → Context

data Type where
  _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
  ‘Typeε’ : Type ε
  ‘□’ : Type (ε ▻ ‘Typeε’)
  _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  _‘×’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  ‘⊤’ : ∀ {Γ} → Type Γ
  ‘⊥’ : ∀ {Γ} → Type Γ
  ‘Δ’ : Type ε → Type ε
  _‘≡’_ : ∀ {Γ} {A : Type Γ} → Term A → Term A → Type Γ

data Term where
  ⌜_⌝ : Type ε → Term {ε} ‘Typeε’
  ⌜_⌝ₜ : ∀ {T} → Term T → Term (‘□’ ‘’ ⌜ T ⌝)
  ‘quote’ : ∀ {T} → Term (‘□’ ‘’ ⌜ T ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘□’ ‘’ ⌜ T ⌝ ⌝)
  ‘id’ : ∀ {Γ A} → Term {Γ} (A ‘→’ A)
  ‘eval’ : ∀ {Γ A B} → Term {Γ} (((A ‘→’ B) ‘×’ A) ‘→’ B)
  ‘curry’ : ∀ {Γ A B C} → Term {Γ} ((A ‘×’ B ‘→’ C) ‘→’ (A ‘→’ (B ‘→’ C)))
  ‘uncurry’ : ∀ {Γ A B C} → Term {Γ} ((A ‘→’ (B ‘→’ C)) ‘→’ (A ‘×’ B ‘→’ C))
  _‘,’_ : ∀ {Γ A B} → Term {Γ} A → Term {Γ} B → Term {Γ} (A ‘×’ B)
  _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
  ‘‘’’ₐ : ∀ {A B} → Term (‘□’ ‘’ ⌜ A ‘→’ B ⌝ ‘→’ ‘□’ ‘’ ⌜ A ⌝ ‘→’ ‘□’ ‘’ ⌜ B ⌝)
  ‘dup’ : ∀ {Γ A} → Term {Γ} (A ‘→’ A ‘×’ A)
  _‘××’_ : ∀ {Γ A B C D} → Term {Γ} (A ‘→’ C) → Term {Γ} (B ‘→’ D) → Term {Γ} (A ‘×’ B ‘→’ C ‘×’ D)
  ‘‘,’’ : ∀ {A B} → Term (‘□’ ‘’ ⌜ A ⌝ ‘×’ ‘□’ ‘’ ⌜ B ⌝ ‘→’ ‘□’ ‘’ ⌜ A ‘×’ B ⌝)
  _‘∘’_ : ∀ {Γ A B C} → Term {Γ} (B ‘→’ C) → Term {Γ} (A ‘→’ B) → Term {Γ} (A ‘→’ C)
  ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
  ‘refl’ : ∀ {Γ A} {x : Term {Γ} A} → Term (x ‘≡’ x)
  ‘Δ-fwd’ : ∀ {T} → Term (‘Δ’ T ‘→’ (‘□’ ‘’ ⌜ ‘Δ’ T ⌝ ‘→’ T))
  ‘Δ-bak’ : ∀ {T} → Term (‘□’ ‘’ ⌜ ‘Δ’ T ⌝ ‘→’ T) → Term (‘Δ’ T)
  ‘Δ’-point-surjection : ∀ {T} {f : Term (‘□’ ‘’ ⌜ ‘Δ’ T ⌝ ‘→’ T)} {d}
    → Term (‘Δ-fwd’ ‘’ₐ (‘Δ-bak’ f) ‘’ₐ d ‘≡’ f ‘’ₐ d)

Lӧb : ∀ {X} → Term {ε} (‘□’ ‘’ ⌜ X ⌝ ‘→’ X) → Term {ε} X
Lӧb {X} f = K ‘’ₐ ⌜ ‘Δ-bak’ K ⌝ₜ
  module Lӧb where
    K : Term (‘□’ ‘’ ⌜ ‘Δ’ X ⌝ ‘→’ X)
    K = f ‘∘’ (‘‘’’ₐ ‘’ₐ ⌜ ‘eval’ ‘∘’ (‘Δ-fwd’ ‘××’ ‘id’) ⌝ₜ) ‘∘’ ‘‘,’’ ‘∘’ (‘id’ ‘××’ ‘quote’) ‘∘’ ‘dup’

□ : Type ε → Set _
□ = Term {ε}

max-level : Level
max-level = lzero

Context⇓ : (Γ : Context) → Set max-level
Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓

Context⇓ ε = ⊤
Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
Type⇓ ‘Typeε’ Γ⇓ = Lifted (Type ε)
Type⇓ ‘□’ Γ⇓ = Lifted (Term {ε} (lower (Σ.proj₂ Γ⇓)))
Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
Type⇓ ‘⊤’ Γ⇓ = ⊤
Type⇓ ‘⊥’ Γ⇓ = ⊥
Type⇓ (‘Δ’ T) Γ⇓ = Term (‘Δ’ T) → Type⇓ T Γ⇓
Type⇓ (x ‘≡’ y) Γ⇓ = Term⇓ x Γ⇓ ≡ Term⇓ y Γ⇓
Type⇓ (A ‘×’ B) Γ⇓ = Type⇓ A Γ⇓ × Type⇓ B Γ⇓

Term⇓-‘Δ’-point-surjection : ∀ {T} {f : Term (‘□’ ‘’ ⌜ ‘Δ’ T ⌝ ‘→’ T)} {d}
      → ∀ Γ⇓ → Type⇓ (‘Δ-fwd’ ‘’ₐ (‘Δ-bak’ f) ‘’ₐ d ‘≡’ f ‘’ₐ d) Γ⇓

Term⇓ ⌜ x ⌝ Γ⇓ = lift x
Term⇓ ⌜ x ⌝ₜ Γ⇓ = lift x
Term⇓ ‘quote’ Γ⇓ t = lift ⌜ lower t ⌝ₜ
Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
Term⇓ ‘‘’’ₐ Γ⇓ f x = lift (lower f ‘’ₐ lower x)
Term⇓ ‘tt’ Γ⇓ = tt
Term⇓ ‘refl’ Γ⇓ = refl
Term⇓ ‘Δ-fwd’ Γ⇓ f⇓ d = f⇓ (lower d)
Term⇓ (‘Δ-bak’ f) Γ⇓ d = Term⇓ f Γ⇓ (lift d)
Term⇓ ‘id’ Γ⇓ = λ x → x
Term⇓ ‘eval’ Γ⇓ ( f , x ) = f x
Term⇓ ‘curry’ Γ⇓ f a b = f (a , b)
Term⇓ ‘uncurry’ Γ⇓ f ( a , b ) = f a b
Term⇓ (x ‘,’ y) Γ⇓ = Term⇓ x Γ⇓ , Term⇓ y Γ⇓
Term⇓ ‘‘,’’ Γ⇓ (a , b) = lift (lower a ‘,’ lower b)
Term⇓ ‘dup’ Γ⇓ = λ x → x , x
Term⇓ (f ‘××’ g) Γ⇓ (a , b) = (Term⇓ f Γ⇓ a , Term⇓ g Γ⇓ b)
Term⇓ (f ‘∘’ g) Γ⇓ = λ x → Term⇓ f Γ⇓ (Term⇓ g Γ⇓ x)
Term⇓ (‘Δ’-point-surjection {T} {f} {d}) Γ⇓ = Term⇓-‘Δ’-point-surjection {T} {f} {d} Γ⇓

Term⇓-‘Δ’-point-surjection Γ⇓ = refl

-- We want to prove this, but it's not true unless we quotient syntax by conversion
-- Lӧb⇓-≡ : ∀ {X f Γ⇓} → Term⇓ (Lӧb {X} f) Γ⇓ ≡ Term⇓ f Γ⇓ (lift (Lӧb {X} f))
-- Lӧb⇓-≡ = {!!}

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

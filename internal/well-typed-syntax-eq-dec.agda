{-# OPTIONS --without-K #-}
module well-typed-syntax-eq-dec where
open import well-typed-syntax
open import common
open import common-utilities
-- open import well-typed-syntax-pre-eq-dec-defs
-- open import well-typed-syntax-pre-eq-dec

≟-helper' : {A : Set} → (dec : ∀ (x y : A) → Maybe (x ≡ y)) → ∀ {x y} → (p : Maybe (x ≡ y)) → p ≡ (dec x y) → (∀ x → dec x x ≡ just refl) → dec-eq-on x y
≟-helper' dec (just x₁) q dec-refl = inj₁ x₁
≟-helper' dec nothing q dec-refl = inj₂ (helper q)
  where
    helper : ∀ {x y} → nothing ≡ (dec x y) → x ≡ y → ⊥
    helper {x} {.x} p refl with trans p (dec-refl x)
    helper p refl | q = Maybe-encode q

≟-helper : {A : Set} → (dec : ∀ (x y : A) → Maybe (x ≡ y)) → ∀ (x y : A) → (∀ x → dec x x ≡ just refl) → dec-eq-on x y
≟-helper dec x y dec-refl = ≟-helper' dec (dec x y) refl dec-refl

≟-helper'-refl : ∀ {A dec x p q dec-refl} → just refl ≡ p → ≟-helper' {A} dec {x} {x} p q dec-refl ≡ inj₁ refl
≟-helper'-refl {A} {dec} {x} {._} {q} {dec-refl} refl = refl

≟-helper-refl : ∀ {A dec x dec-refl} → ≟-helper {A} dec x x dec-refl ≡ inj₁ refl
≟-helper-refl {A} {dec} {x} {dec-refl} = ≟-helper'-refl {A} {dec} {x} {dec x x} {refl} {dec-refl} (sym (dec-refl x))

postulate
  _≟-ctx_ : dec-eq Context
-- x ≟-ctx y = ≟-helper _≟'-ctx_ x y ≟'-ctx-refl

  _≟-typ_ : ∀ {Γ} → dec-eq (Typ Γ)
-- x ≟-typ y = ≟-helper _≟'-typ_ x y ≟'-typ-refl

  _≟-term_ : ∀ {Γ T} → dec-eq (Term {Γ} T)
-- x ≟-term y = ≟-helper _≟'-term_ x y ≟'-term-refl

  ≟-ctx-refl : ∀ x → (x ≟-ctx x) ≡ inj₁ refl
-- ≟-ctx-refl x = ≟-helper-refl

  ≟-typ-refl : ∀ {Γ} (x : Typ Γ) → (x ≟-typ x) ≡ inj₁ refl
-- ≟-typ-refl x = ≟-helper-refl

  ≟-term-refl : ∀ {Γ T} (x : Term {Γ} T) → (x ≟-term x) ≡ inj₁ refl
-- ≟-term-refl x = ≟-helper-refl

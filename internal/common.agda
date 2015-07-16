module common where

infixr 1 _,_

record Σ {A : Set} (P : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : P proj₁

data Maybe (A : Set) : Set where
  just    : (x : A) → Maybe A
  nothing : Maybe A

infixr 1 _⊎_

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : {A : Set} → {x : A} → {y : A} → x ≡ y → y ≡ x
sym refl = refl

transport : ∀ {A : Set} {x : A} {y : A} → (P : A → Set) → x ≡ y → P x → P y
transport P refl v = v

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

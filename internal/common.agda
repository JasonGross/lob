module common where

infixr 1 _,_

record Σ {A : Set} (P : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : P proj₁

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : {A : Set} → {x : A} → {y : A} → x ≡ y → y ≡ x
sym refl = refl

transport : ∀ {A : Set} {x : A} {y : A} → (P : A → Set) → x ≡ y → P x → P y
transport P refl v = v

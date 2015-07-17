{-# OPTIONS --without-K #-}

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

data ⊥ : Set where

⊥-elim : ⊥ → {A : Set} → A
⊥-elim ()

record ⊤ : Set where
  constructor tt

infixr 1 _⊎_

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

dec-eq-on : {A : Set} → (x : A) → (y : A) → Set
dec-eq-on x y = (x ≡ y) ⊎ (x ≢ y)

dec-eq : Set → Set
dec-eq A = (x : A) → (y : A) → dec-eq-on x y

sym : {A : Set} → {x : A} → {y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

transport : ∀ {A : Set} {x : A} {y : A} → (P : A → Set) → x ≡ y → P x → P y
transport P refl v = v

transport2 : ∀ {A : Set} {B : A → Set} {x x' : A} {y : B x} {y' : B x'} → (P : (x : A) → B x → Set) → (p : x ≡ x') → transport B p y ≡ y' → P x y → P x' y'
transport2 P refl = transport (P _)

transport3 : ∀ {A : Set} {B : A → Set} {C : (x : A) → (y : B x) → Set} {x x' : A} {y : B x} {y' : B x'} {z : C x y} {z' : C x' y'} → (P : (x : A) → (y : B x) → C x y → Set) → (p : x ≡ x') → (q : transport B p y ≡ y') → transport2 C p q z ≡ z' → P x y z → P x' y' z'
transport3 P refl = transport2 (P _)

transport4 : ∀ {A : Set} {B : A → Set} {C : (x : A) → (y : B x) → Set} {D : (x : A) → (y : B x) → (z : C x y) → Set} {x x' : A} {y : B x} {y' : B x'} {z : C x y} {z' : C x' y'} {w : D x y z} {w' : D x' y' z'} → (P : (x : A) → (y : B x) → (z : C x y) → D x y z → Set) → (p : x ≡ x') → (q : transport B p y ≡ y') → (r : transport2 C p q z ≡ z') → transport3 D p q r w ≡ w' → P x y z w → P x' y' z' w'
transport4 P refl = transport3 (P _)


Maybe-code : {A : Set} → Maybe A → Maybe A → Set
Maybe-code (just x) (just x₁) = x ≡ x₁
Maybe-code (just x) nothing = ⊥
Maybe-code nothing (just x) = ⊥
Maybe-code nothing nothing = ⊤

Maybe-encode : ∀ {A} {x y : Maybe A} → x ≡ y → Maybe-code x y
Maybe-encode {A} {just x} refl = refl
Maybe-encode {A} {nothing} refl = tt

Maybe-decode : ∀ {A} {x y : Maybe A} → Maybe-code x y → x ≡ y
Maybe-decode {A} {just .x₁} {just x₁} refl = refl
Maybe-decode {A} {just x} {nothing} ()
Maybe-decode {A} {nothing} {just x} ()
Maybe-decode {A} {nothing} {nothing} tt = refl

Maybe-deencode : ∀ {A} {x y : Maybe A} {p : x ≡ y} → Maybe-decode (Maybe-encode p) ≡ p
Maybe-deencode {A} {just x} {.(just x)} {refl} = refl
Maybe-deencode {A} {nothing} {.nothing} {refl} = refl

Maybe-endecode : ∀ {A} {x y : Maybe A} (p : Maybe-code x y) → Maybe-encode {A} {x} {y} (Maybe-decode p) ≡ p
Maybe-endecode {A} {just .x'} {just x'} refl = refl
Maybe-endecode {A} {just x} {nothing} ()
Maybe-endecode {A} {nothing} {just x} ()
Maybe-endecode {A} {nothing} {nothing} tt = refl


data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

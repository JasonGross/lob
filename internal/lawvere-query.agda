{-# OPTIONS --without-K #-}
module lawvere-query
  {ℓ₀} {ℓ₁} {ℓ₂}
  (C : Set ℓ₀)
  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (ι : ∀ {a} → a [>] a)
  (A : C → Set ℓ₂)
  (_»_ : ∀ {a b} → (a [>] b) → A b → A a)
  (𝟙 : C) (R : C) (S : C)
  (encode : A 𝟙 → (𝟙 [>] R))
  (pack : A S → (𝟙 [>] S))
  (query : ∀ {X} → (X [>] S) → (X [>] S) → (X [>] R))
  (f : A R)
  where

a : A S
a = query {S} ι ι » f

lawvere : A 𝟙
lawvere = pack a » a

module _
  {ℓ₃} (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓ₃)
  {ℓ₄} (_A≈_ : ∀ {a} → A a → A a → Set ℓ₄)
  (query-pack-encode : ∀ {a} {s} → query {𝟙} (pack a) s ≈ encode (s » a))
  (_■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
  (rid : ∀ {a b} {f : a [>] b} → (f ⨾ ι) ≈ f)
  (_■A_     : ∀ {a} {f g h : A a} → f A≈ g → g A≈ h → f A≈ h)
  (assocA   : ∀ {a b c} {f : a [>] b} {g : b [>] c} {h : A c} → (f » (g » h)) A≈ ((f ⨾ g) » h))
  (»-2map   : ∀ {a b} {f g : a [>] b} → f ≈ g → {h : A b} → (f » h) A≈ (g » h))
  (query-natural : ∀ {X Y} {m : Y [>] X} {f : X [>] S} {g : X [>] S} → (m ⨾ query {X} f g) ≈ query {Y} (m ⨾ f) (m ⨾ g))
  (query-2map    : ∀ {X} {f f′ g g′} → f ≈ f′ → g ≈ g′ → query {X} f g ≈ query {X} f′ g′)
  where

  eq : lawvere A≈ ((encode lawvere) » f)
  eq = assocA ■A »-2map (query-natural ■ (query-2map rid rid ■ query-pack-encode))

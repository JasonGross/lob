{-# OPTIONS --without-K #-}
module lawvere-compressed
  {o a}
  (𝒞 : Set o)
  (_~>_ : 𝒞 → 𝒞 → Set a)
  (_∘_ : ∀ {a b c} → b ~> c → a ~> b → a ~> c)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (𝟙 : 𝒞)
  (□ : 𝒞 → 𝒞)
  (id×quot∘dup : ∀ {a} → (□ a ~> □ (a × □ a)))
  (B : 𝒞)
  (inf : 𝒞)
  (ϕ : □ (inf × □ inf) ~> □ B)
  (ϕ⁻¹ : (□ inf ~> B) → (𝟙 ~> □ inf))
  (f : □ B ~> B)
  where

lawvere : (𝟙 ~> B)
lawvere = p ∘ ϕ⁻¹ p
  module lawvere where
    p : □ inf ~> B
    p = f ∘ (ϕ ∘ id×quot∘dup)

lawvere-fix : ∀
  (□-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b))
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (□tt : 𝟙 ~> □ 𝟙)
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h)))
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (_∘-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → g ≈ g‵ → f ≈ f‵ → (g ∘ f) ≈ (g‵ ∘ f‵))
  (ϕ-eq : ∀ {f} → ((ϕ ∘ id×quot∘dup) ∘ ϕ⁻¹ f) ≈ (□-map (f ∘ ϕ⁻¹ f) ∘ □tt))
  → lawvere ≈ (f ∘ (□-map lawvere ∘ □tt))
lawvere-fix □-map _≈_ □tt _■_ assoc 2id _∘-map_ ϕ-eq =
  assoc ■ (2id ∘-map ϕ-eq)

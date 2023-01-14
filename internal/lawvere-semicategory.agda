{-# OPTIONS --without-K #-}
module lawvere-semicategory
  {o a}
  (𝒞 : Set o)
  (□_~>_ : 𝒞 → 𝒞 → Set a)
  (_×□_ : 𝒞 → 𝒞 → 𝒞)
  (_∘□dup∘quote : ∀ {a b} → □ (a ×□ a) ~> b → □ a ~> b)
  (𝟙 : 𝒞)
  (B : 𝒞)
  (inf : 𝒞)
  (_∘□ϕ∘quote : ∀ {a} → □ B ~> a → □ (inf ×□ inf) ~> a)
  (_∘□ϕ⁻¹_∘quote : ∀ {a} → (□ inf ~> a) → (□ inf ~> B) → (□ 𝟙 ~> a))
  (f : □ B ~> B)
  where

lawvere : (□ 𝟙 ~> B)
lawvere = p ∘□ϕ⁻¹ p ∘quote
  module lawvere where
    p : □ inf ~> B
    p = f ∘□ϕ∘quote ∘□dup∘quote


lawvere-fix : ∀
  (_∘□_∘quote : ∀ {a b c} → (□ b ~> c) → (□ a ~> b) → (□ a ~> c))
  {a₂} (_≈_ : ∀ {a b} → (□ a ~> b) → (□ a ~> b) → Set a₂)
  (ϕ-eq : ∀ {a} {f : □ B ~> a} {g : □ inf ~> B} →
    (((f ∘□ϕ∘quote) ∘□dup∘quote) ∘□ϕ⁻¹ g ∘quote)
    ≈
    (f ∘□ (g ∘□ϕ⁻¹ g ∘quote) ∘quote))
  → lawvere ≈ (f ∘□ lawvere ∘quote)
lawvere-fix _∘□_∘quote _≈_ ϕ-eq = ϕ-eq

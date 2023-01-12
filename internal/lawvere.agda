{-# OPTIONS --without-K #-}
open import common
module lawvere
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

-- TODO
{-
lawvere-fix : ∀ {a₂}
  (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (□tt : 𝟙 ~> □ 𝟙)
  → lawvere ≈ (f ∘ ((□-map lawvere) ∘ □tt))
lawvere-fix _≈_ □tt = {!!}
-}

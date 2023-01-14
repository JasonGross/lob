{-# OPTIONS --without-K #-}
open import common
module lawvere-semicomonad
  {o a}
  (𝒞 : Set o)
  (_~>_ : 𝒞 → 𝒞 → Set a)
  (id : ∀ {a} → a ~> a)
  (_⨾_ : ∀ {a b c} → a ~> b → b ~> c → a ~> c)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (dup : ∀ {a} → (a ~> (a × a)))
  (_××_ : ∀ {a b c d} → (a ~> b) → (c ~> d) → ((a × c) ~> (b × d)))
  (𝟙 : 𝒞)
  (□ : 𝒞 → 𝒞)
  (□-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b))
  (□-×-codistr : ∀ {a b} → (□ a × □ b) ~> □ (a × b))
  (quot : ∀ {a} → □ a ~> □ (□ a))
  (B : 𝒞)
  (inf : 𝒞)
  (ϕ : (inf × □ inf) ~> B)
  (ϕ⁻¹ : (□ inf ~> B) → (𝟙 ~> □ inf))
  (f : □ B ~> B)
  where

lawvere : (𝟙 ~> B)
lawvere = ϕ⁻¹ p ⨾ p
  module lawvere where
    p : □ inf ~> B
    p = (dup ⨾ ((id ×× quot) ⨾ (□-×-codistr ⨾ □-map ϕ))) ⨾ f
{-
lawvere-fix : ∀
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (□tt : 𝟙 ~> □ 𝟙)
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → (h ⨾ (g ⨾ f)) ≈ ((h ⨾ g) ⨾ f))
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → g ≈ g‵ → f ≈ f‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (ϕ-eq : ∀ {f} → {!((ϕ ∘ id×quot∘dup) ∘ ϕ⁻¹ f)!} ≈ (□tt ⨾ {!(□-map (f ∘ ϕ⁻¹ f) ∘ □tt)!}))
  → lawvere ≈ ((□tt ⨾ □-map lawvere) ⨾ f)
lawvere-fix _≈_ □tt _■_ assoc 2id _⨾-map_ ϕ-eq =
  assoc ■ (2id ⨾-map {!ϕ-eq!})
-}

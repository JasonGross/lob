{-# OPTIONS --without-K #-}
module lawvere
  {o a}
  (𝒞 : Set o)
  (_~>_ : 𝒞 → 𝒞 → Set a)
  (_⨾_ : ∀ {a b c} → a ~> b → b ~> c → a ~> c)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (dup : ∀ {a} → (a ~> (a × a)))
  (_××_ : ∀ {a b c d} → (a ~> b) → (c ~> d) → ((a × c) ~> (b × d)))
  (𝟙 : 𝒞)
  (B : 𝒞)
  (inf : 𝒞)
  (ϕ : (inf × inf) ~> B)
  (ϕ⁻¹ : (inf ~> B) → (𝟙 ~> inf))
  (f : B ~> B)
  where

lawvere : (𝟙 ~> B)
lawvere = ϕ⁻¹ p ⨾ p
  module lawvere where
    p : inf ~> B
    p = (dup ⨾ ϕ) ⨾ f

lawvere-fix : ∀
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → (h ⨾ (g ⨾ f)) ≈ ((h ⨾ g) ⨾ f))
  (assoc⁻¹ : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((h ⨾ g) ⨾ f) ≈ (h ⨾ (g ⨾ f)))
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (dup-×× : ∀ {a b} {f : a ~> b} → (f ⨾ dup) ≈ (dup ⨾ (f ×× f)))
  (ϕ-eq : ∀ {f g} → (dup ⨾ ((ϕ⁻¹ f ×× g) ⨾ ϕ)) ≈ (g ⨾ f))
  → lawvere ≈ (lawvere ⨾ f)
lawvere-fix _≈_ _■_ assoc assoc⁻¹ 2id _⨾-map_ dup-×× ϕ-eq =
  assoc ■ (((assoc ■ (dup-×× ⨾-map 2id)) ■ (assoc⁻¹ ■ ϕ-eq)) ⨾-map 2id)

{-# OPTIONS --without-K #-}
module lawvere-boxless where
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc; Setω)
module _
  {ℓ₀} {ℓ₁} {ℓ₂}
  (C : Set ℓ₀)
  (_[>]_ : C → C → Set ℓ₁)
  (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓ₂)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (ι : ∀ {a} → a [>] a)
  (QS : C) (QQS : C)
  (𝟙 : C) (T : C) (QT : C)
  (requoteS : QS [>] QQS)
  (quote-T : (𝟙 [>] T) → (𝟙 [>] QT))
  (□-map-QT-ϕ : ∀ {a} → (a [>] QS) → (a [>] QQS) → a [>] QT)
  (□-map-ψ : (QS [>] T) → (𝟙 [>] QS))
  (f : QT [>] T)
  (□-map-ϕ-eq : ∀ {f : QS [>] T} {g : 𝟙 [>] QS} → □-map-QT-ϕ (□-map-ψ f) (g ⨾ requoteS) ≈ quote-T (g ⨾ f))
  where

  pre-unwrap : QS [>] QT
  pre-unwrap = □-map-QT-ϕ ι requoteS

  unwrap : QS [>] T
  unwrap = pre-unwrap ⨾ f

  rewrap : 𝟙 [>] QS
  rewrap = □-map-ψ unwrap

  lawvere : 𝟙 [>] T
  lawvere = rewrap ⨾ unwrap

  module _
    (_■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
    (rid : ∀ {a b} {f : a [>] b} → (f ⨾ ι) ≈ f)
    (assocT : ∀ {a b c} {f : a [>] b} {g : b [>] c} {h : c [>] T} → (f ⨾ (g ⨾ h)) ≈ ((f ⨾ g) ⨾ h))
    (2id : ∀ {a b} {f : a [>] b} → f ≈ f)
    (⨾T-map : ∀ {a b} {f g : a [>] b} {h : b [>] T} → f ≈ g → (f ⨾ h) ≈ (g ⨾ h))
    (□-map-QT-ϕ-distr : ∀ {a b} {f : a [>] b} {g h} → (f ⨾ □-map-QT-ϕ g h) ≈ □-map-QT-ϕ (f ⨾ g) (f ⨾ h))
    (□-map-QT-ϕ-2map : ∀ {a} {f g : a [>] QS} {h i : a [>] QQS} → f ≈ g → h ≈ i → □-map-QT-ϕ f h ≈ □-map-QT-ϕ g i)

    where

    eq : lawvere ≈ (quote-T lawvere ⨾ f)
    eq = assocT ■ ⨾T-map (□-map-QT-ϕ-distr ■ (□-map-QT-ϕ-2map rid 2id ■ □-map-ϕ-eq))

{-# OPTIONS --without-K #-}
module lawvere-yoneda-boxless where
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc; Setω)
module _
  {ℓ₀} {ℓ₁} {ℓ₂}
  (C : Set ℓ₀)
  (_[>]_ : C → C → Set ℓ₁)
  (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓ₂)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (ι : ∀ {a} → a [>] a)
  {t} (T : C → Set t)
  {t₂} (_≈T_ : ∀ {a} → T a → T a → Set t₂)
  (_⨾T_ : ∀ {a b} → a [>] b → T b → T a)
  (S : C) (QS : C) (QQS : C)
  (𝟙 : C)
  (QT : C)
  (cojoinS : QS [>] QQS)
  (□-map-T : T 𝟙 → 𝟙 [>] QT)
  (□-map-QT-ϕ : ∀ {a} → (a [>] QS) → (a [>] QQS) → a [>] QT)
  (□-map-ψ : T QS → (𝟙 [>] QS))
  (f : T QT)
  (□-map-ϕ-eq : ∀ {f : T QS} {g : 𝟙 [>] QS} → □-map-QT-ϕ (□-map-ψ f) (g ⨾ cojoinS) ≈ □-map-T (g ⨾T f))
  where

  pre-unwrap : QS [>] QT
  pre-unwrap = □-map-QT-ϕ ι cojoinS

  unwrap : T QS
  unwrap = pre-unwrap ⨾T f

  rewrap : 𝟙 [>] QS
  rewrap = □-map-ψ unwrap

  lawvere : T 𝟙
  lawvere = rewrap ⨾T unwrap

  module _
    (_■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
    (_■T_   : ∀ {a} {x y z : T a} → x ≈T y → y ≈T z → x ≈T z)
    (rid : ∀ {a b} {f : a [>] b} → (f ⨾ ι) ≈ f)
    (assocT : ∀ {a b c} {f : a [>] b} {g : b [>] c} {h : T c} → (f ⨾T (g ⨾T h)) ≈T ((f ⨾ g) ⨾T h))
    (2id : ∀ {a b} {f : a [>] b} → f ≈ f)
    (⨾T-map : ∀ {a b} {f g : a [>] b} {h : T b} → f ≈ g → (f ⨾T h) ≈T (g ⨾T h))
    (□-map-QT-ϕ-distr : ∀ {a b} {f : a [>] b} {g h} → (f ⨾ □-map-QT-ϕ g h) ≈ □-map-QT-ϕ (f ⨾ g) (f ⨾ h))
    (□-map-QT-ϕ-2map : ∀ {a} {f g : a [>] QS} {h i : a [>] QQS} → f ≈ g → h ≈ i → □-map-QT-ϕ f h ≈ □-map-QT-ϕ g i)

    where

    eq : lawvere ≈T (□-map-T lawvere ⨾T f)
    eq = assocT ■T ⨾T-map (□-map-QT-ϕ-distr ■ (□-map-QT-ϕ-2map rid 2id ■ □-map-ϕ-eq))

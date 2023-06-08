{-# OPTIONS --without-K #-}
module lawvere-yoneda-boxless-from-query
  {ℓ₀} {ℓ₁} {ℓ₂}
  (C : Set ℓ₀)
  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (ι : ∀ {a} → a [>] a)
  {t} (T : C → Set t)
  (_⨾T_ : ∀ {a b} → a [>] b → T b → T a)
  (QS : C) (QQS : C)
  (𝟙 : C)
  (QT : C)
  (cojoinS : QS [>] QQS)
  (□-map-T : T 𝟙 → 𝟙 [>] QT)
  (□-map-QT-ϕ : ∀ {a} → (a [>] QS) → (a [>] QQS) → a [>] QT)
  (□-map-ψ : T QS → (𝟙 [>] QS))
  (f : T QT)
  where

query : ∀ {X} → X [>] QS → X [>] QS → X [>] QT
query f g = □-map-QT-ϕ f (g ⨾ cojoinS)

import lawvere-query C _[>]_ _⨾_ ι T _⨾T_ 𝟙 QT QS □-map-T □-map-ψ query f as lawvere-query

lawvere : T 𝟙
lawvere = lawvere-query.lawvere

module _
  (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓ₂)
  {t₂} (_≈T_ : ∀ {a} → T a → T a → Set t₂)
  (□-map-ϕ-eq : ∀ {f : T QS} {g : 𝟙 [>] QS} → □-map-QT-ϕ (□-map-ψ f) (g ⨾ cojoinS) ≈ □-map-T (g ⨾T f))
  (_■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
  (_■T_   : ∀ {a} {x y z : T a} → x ≈T y → y ≈T z → x ≈T z)
  (rid : ∀ {a b} {f : a [>] b} → (f ⨾ ι) ≈ f)
  (assocT : ∀ {a b c} {f : a [>] b} {g : b [>] c} {h : T c} → (f ⨾T (g ⨾T h)) ≈T ((f ⨾ g) ⨾T h))
  (assoc : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d} → (f ⨾ (g ⨾ h)) ≈ ((f ⨾ g) ⨾ h))
  (2id : ∀ {a b} {f : a [>] b} → f ≈ f)
  (⨾-2map : ∀ {a b c} {f f′ : a [>] b} {g g′ : b [>] c} → f ≈ f′ → g ≈ g′ → (f ⨾ g) ≈ (f′ ⨾ g′))
  (⨾T-map : ∀ {a b} {f g : a [>] b} {h : T b} → f ≈ g → (f ⨾T h) ≈T (g ⨾T h))
  (□-map-QT-ϕ-distr : ∀ {a b} {f : a [>] b} {g h} → (f ⨾ □-map-QT-ϕ g h) ≈ □-map-QT-ϕ (f ⨾ g) (f ⨾ h))
  (□-map-QT-ϕ-2map : ∀ {a} {f g : a [>] QS} {h i : a [>] QQS} → f ≈ g → h ≈ i → □-map-QT-ϕ f h ≈ □-map-QT-ϕ g i)

  where

  eq : lawvere ≈T (□-map-T lawvere ⨾T f)
  eq = lawvere-query.eq
         _≈_ _≈T_
         □-map-ϕ-eq _■_ rid _■T_ assocT (λ p → ⨾T-map p)
         (□-map-QT-ϕ-distr ■ □-map-QT-ϕ-2map 2id assoc)
         λ{ p q → □-map-QT-ϕ-2map p (⨾-2map q 2id) }

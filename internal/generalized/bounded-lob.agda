{-# OPTIONS --without-K --safe #-}
module bounded-lob where
open import loopy public hiding (module setup)
module setup
  {ℓ₀} {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄}
  (C : Set ℓ₀)

  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (id : ∀ {a} → a [>] a)

  {ℓe₀} (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓe₀)
  (_■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
  (2id : ∀ {a b} {f : a [>] b} → f ≈ f)
  (assoc : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d} → (f ⨾ (g ⨾ h)) ≈ ((f ⨾ g) ⨾ h))
  (_⨾-2map_ : ∀ {a b c} {f f′ : a [>] b} {g g′ : b [>] c} → f ≈ f′ → g ≈ g′ → (f ⨾ g) ≈ (f′ ⨾ g′))

  (𝟙 : C)

  (x : C)
  (□ : C → C)
  (Pred : C → Set ℓ₂)
  (Σ* : ∀ c → Pred c → C)
  (is-short : Pred (□ x))
  (is-very-short : 𝟙 [>] x → Set ℓ₃)
  (is-very-very-short : 𝟙 [>] x → Set ℓ₃)
  (is-very-very-very-short : ∀ {a} → (𝟙 [>] a) → Set ℓ₄)
  (reflect : Σ (𝟙 [>] x) is-very-short → 𝟙 [>] Σ* (□ x) is-short)
  (s : C) -- s ~ Σ* (□(s [>] x)) λ{ m → Π[ s₀ : 𝟙 [>] s ] ((s₀ ⨾ m) ⟫ is-short) }
  (pack : Σ (s [>] x) (λ{ f → (s₀ : 𝟙 [>] s) → is-very-very-very-short s₀ → is-very-very-short (s₀ ⨾ f) }) → 𝟙 [>] s)
  (qual : ∀ ((t , p) : Σ (s [>] x) (λ{ t → (s₀ : 𝟙 [>] s) → is-very-very-very-short s₀ → is-very-very-short (s₀ ⨾ t) })) → is-very-short (pack (t , p) ⨾ t))
  (key : s [>] Σ* (□ x) is-short)
  (f : Σ* (□ x) is-short [>] x)
  where

  P : s [>] x → Set (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄)
  P f = ∀ (s₀ : 𝟙 [>] s) → is-very-very-very-short s₀ → is-very-very-short (s₀ ⨾ f)

TODO FIXME
  module loopy-setup = loopy.setup C _[>]_ _⨾_ id _≈_ _■_ 2id assoc _⨾-2map_ 𝟙  -- is-very-short (Σ* (□ x) is-short) reflect s P pack qual key f
  open loopy-setup public using (introspect ; t)
{-
  module inner
    (p : P t)
    where

    module lg-inner = lg.inner p
    open lg-inner public using (fixpt)

    module inner
      {ℓe₀} (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓe₀)
      (2id : ∀ {a b} {f : a [>] b} → f ≈ f)
      (_■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
      (rid : ∀ {a b} {f : a [>] b} → (f ⨾ id) ≈ f)
      (assoc : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d} → (f ⨾ (g ⨾ h)) ≈ ((f ⨾ g) ⨾ h))
      (_⨾-2map_ : ∀ {a b c} {f f′ : a [>] b} {g g′ : b [>] c} → f ≈ f′ → g ≈ g′ → (f ⨾ g) ≈ (f′ ⨾ g′))

      (key-law : ∀ {(t , p) : Σ (s [>] x) P} → (pack (t , p) ⨾ key) ≈ reflect (introspect (t , p)))
      where

      module lg-inner-inner = lg-inner.inner _≈_ _≈_ 2id _■_ _■_ assoc (_⨾-2map 2id) key-law
      open lg-inner-inner public using (proof)
-}

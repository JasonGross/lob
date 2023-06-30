{-# OPTIONS --without-K --safe #-}
module no-presheaf where
open import loopy public hiding (module setup)
module setup
  {ℓ₀} {ℓ₁} {ℓ₂}
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

  (a : C)
  (Q : 𝟙 [>] a → Set ℓ₂)

  where

  module loopy-setup = loopy.setup C _[>]_ _⨾_ id _≈_ _■_ 𝟙 (_[>] a) _⨾_ _≈_ 2id _■_ assoc (_⨾-2map 2id) Q a fst
  open loopy-setup public using (Fixpoint)

  module conditions₁
    (s : C)
    {ℓ₄} (P : s [>] a → Set ℓ₄)

    (pack : Σ (s [>] a) P → 𝟙 [>] s)
    (qual : ∀ ((t , p) : Σ (s [>] a) P) → Q (pack (t , p) ⨾ t))
    where

    module loopy-conditions₁ = loopy-setup.conditions₁ s P pack qual
    open loopy-conditions₁ public using (introspect)

    module conditions₂
      (key : s [>] a)
      (key-law : ∀ {(t , p) : Σ (s [>] a) P} → (pack (t , p) ⨾ key) ≈ fst (introspect (t , p)))

      (f : a [>] a)
      where

      module loopy-conditions₂ = loopy-conditions₁.conditions₂ key key-law f
      open loopy-conditions₂ public using (t)

      module theorem
        (p : P t)
        where

        module loopy-theorem = loopy-conditions₂.theorem p
        open loopy-theorem public using (fixpt)

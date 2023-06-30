{-# OPTIONS --without-K --safe #-}
module singleton where
open import loopy public hiding (module setup)

record ⊤ : Set where
  constructor ∗

module setup
  {ℓ₀} {ℓ₁} {ℓ₂}
  (C : Set ℓ₀)

  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (id : ∀ {a} → a [>] a)

  {ℓe₀} (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓe₀)
  (_■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)

  (𝟙 : C)


  (A : C → Set ℓ₂)
  (_»_ : ∀ {a b} → (a [>] b) → A b → A a)

  {ℓe₁} (_A≈_ : ∀ {a} → A a → A a → Set ℓe₁)
  (2idA : ∀ {a} {f : A a} → f A≈ f)
  (transA : ∀ {a} {f g h : A a} → f A≈ g → g A≈ h → f A≈ h)
  (assocA : ∀ {a b c} {f : a [>] b} {g : b [>] c} {h : A c} → (f » (g » h)) A≈ ((f ⨾ g) » h))
  (»-2map   : ∀ {a b} {f g : a [>] b} → f ≈ g → {h : A b} → (f » h) A≈ (g » h))


  (a : C)
  (reflect : A 𝟙 → 𝟙 [>] a)

  (s : C)

  (pack : A s → 𝟙 [>] s)
  where

  module loopy-setup = loopy.setup C _[>]_ _⨾_ id _≈_ _■_ 𝟙 A _»_ _A≈_ 2idA transA assocA »-2map (λ{ _ → ⊤ }) a (λ{ (x , _) → reflect x })
  open loopy-setup public using (module notations)
  Fixpoint : A a → Set (ℓ₂ ⊔ ℓe₁)
  Fixpoint f = Σ[ x ∈ A 𝟙 ] (x A≈ (reflect x » f))

  module loopy-conditions₁ = loopy-setup.conditions₁ s (λ{ _ → ⊤ }) (λ{ (x , _) → pack x }) (λ{ _ → ∗ })
  introspect : A s → A 𝟙
  introspect t = fst (loopy-conditions₁.introspect (t , ∗))

  module conditions
    (key : s [>] a)
    (key-law : ∀ {t : A s} → (pack t ⨾ key) ≈ reflect (introspect t))

    (f : A a)
    where

    module loopy-conditions₂ = loopy-conditions₁.conditions₂ key key-law f
    open loopy-conditions₂ public using (t)

    module loopy-theorem = loopy-conditions₂.theorem ∗
    fixpt : Fixpoint f
    fixpt = fst (fst loopy-theorem.fixpt) , loopy-theorem.fixpt.proof

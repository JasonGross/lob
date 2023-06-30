{-# OPTIONS --without-K --safe #-}
module lob where
open import singleton as loopy-singleton public hiding (module setup)
module setup
  {ℓ₀} {ℓ₁}
  (C : Set ℓ₀)

  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (id : ∀ {a} → a [>] a)

  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (id : ∀ {a} → a [>] a)

  {ℓe₀} (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓe₀)
  (trans      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
  (2id : ∀ {a b} {f : a [>] b} → f ≈ f)
  (assoc : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d} → (f ⨾ (g ⨾ h)) ≈ ((f ⨾ g) ⨾ h))
  (_⨾-2map_ : ∀ {a b c} {f f′ : a [>] b} {g g′ : b [>] c} → f ≈ f′ → g ≈ g′ → (f ⨾ g) ≈ (f′ ⨾ g′))

  (𝟙 : C)

  (□ : C → C)

  (x : C)

  (quot : (𝟙 [>] x) → (𝟙 [>] □ x))

  (s : C)

  (pack : (s [>] x) → 𝟙 [>] s)

  where

  module loopy-setup = loopy-singleton.setup C _[>]_ _⨾_ id _≈_ trans 𝟙 (_[>] x) _⨾_ _≈_ 2id trans assoc (_⨾-2map 2id) (□ x) quot s pack
  open loopy-setup public using (Fixpoint ; introspect)
  module notations where
    chain : ∀ {a b} {f g : a [>] b} → f ≈ g → f ≈ g
    chain x = x

    infixr 4 _■_
    _■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h
    _■_ = trans

    syntax chain {f = f} pf = f [ pf ]
  open notations

  -- TODO: Do we want to do the version with × or without ×?
  module conditions

    --(σ-point-surjection : ∀ {f g} → (dup ⨾ (((σ⁻¹ f ⨾ σ) [××] g) ⨾ apply)) ≈ (g ⨾ f))
    (f : □ x [>] x)
    where

    key : s [>] □ x
    key = {!dup ⨾ ((σ [××] id) ⨾ apply)!}

    key-law : ∀ {t : s [>] x} → (pack t ⨾ key) ≈ quot (introspect t)
    key-law {t} = {!(σ⁻¹ t ⨾ (dup ⨾ ((σ [××] id) ⨾ apply)))              [ assoc ]
                ■ ((σ⁻¹ t ⨾ dup) ⨾ ((σ [××] id) ⨾ apply))              [ dup-natural ⨾-2map 2id ]
                ■ ((dup ⨾ (σ⁻¹ t [××] σ⁻¹ t)) ⨾ ((σ [××] id) ⨾ apply)) [ assoc⁻¹ ■ 2id ⨾-2map assoc ]
                ■ (dup ⨾ (((σ⁻¹ t [××] σ⁻¹ t) ⨾ (σ [××] id)) ⨾ apply)) [ 2id ⨾-2map ([××]-natural ⨾-2map 2id) ]
                ■ (dup ⨾ (((σ⁻¹ t ⨾ σ) [××] (σ⁻¹ t ⨾ id)) ⨾ apply))    [ 2id ⨾-2map ((2id [××]-2map rid) ⨾-2map 2id) ]
                ■ (dup ⨾ ((((σ⁻¹ t ⨾ σ) [××] σ⁻¹ t)) ⨾ apply))         [ σ-point-surjeection ]
                ■ (σ⁻¹ t ⨾ t)                                          [ 2id ]!}

    module loopy-conditions = loopy-setup.conditions key key-law f
    open loopy-conditions public using (t ; fixpt)

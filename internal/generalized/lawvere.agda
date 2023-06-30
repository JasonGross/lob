{-# OPTIONS --without-K --safe #-}
module lawvere where
open import singleton as loopy-singleton public hiding (module setup)
module setup
  {ℓ₀} {ℓ₁}
  (C : Set ℓ₀)

  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (id : ∀ {a} → a [>] a)

  {ℓe₀} (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓe₀)
  (trans      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
  (2id : ∀ {a b} {f : a [>] b} → f ≈ f)
  (assoc : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d} → (f ⨾ (g ⨾ h)) ≈ ((f ⨾ g) ⨾ h))
  (_⨾-2map_ : ∀ {a b c} {f f′ : a [>] b} {g g′ : b [>] c} → f ≈ f′ → g ≈ g′ → (f ⨾ g) ≈ (f′ ⨾ g′))
  (assoc⁻¹ : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d} → ((f ⨾ g) ⨾ h) ≈ (f ⨾ (g ⨾ h)))
  (rid   : ∀ {a b} {f : a [>] b} → (f ⨾ id) ≈ f)

  (𝟙 : C)

  (_[^]_ : C → C → C)
  (_[×]_ : C → C → C)

  (dup : ∀ {a} → a [>] (a [×] a))
  (_[××]_ : ∀ {a b c d} → (a [>] b) → (c [>] d) → ((a [×] c) [>] (b [×] d)))
  (apply : ∀ {a b} → ((b [^] a) [×] a) [>] b)

  (dup-natural : ∀ {a b} {f : a [>] b} → (f ⨾ dup) ≈ (dup ⨾ (f [××] f)))
  ([××]-natural : ∀ {a b c a′ b′ c′} {f : a [>] b} {g : b [>] c} {f′ : a′ [>] b′} {g′ : b′ [>] c′}
                 → ((f [××] f′) ⨾ (g [××] g′)) ≈ ((f ⨾ g) [××] (f′ ⨾ g′)))
  (_[××]-2map_ : ∀ {a b a′ b′} {f g : a [>] b} {f′ g′ : a′ [>] b′} → f ≈ g → f′ ≈ g′ → (f [××] f′) ≈ (g [××] g′))

  (a : C)

  (s : C)

  (σ : s [>] (a [^] s))
  (σ⁻¹ : (s [>] a) → (𝟙 [>] s))

  (f : a [>] a)
  where

  module loopy-setup = loopy-singleton.setup C _[>]_ _⨾_ id _≈_ trans 𝟙 (_[>] a) _⨾_ _≈_ 2id trans assoc (_⨾-2map 2id) a (λ{ x → x }) s σ⁻¹
  open loopy-setup public using (Fixpoint ; introspect)
  module notations where
    chain : ∀ {a b} {f g : a [>] b} → f ≈ g → f ≈ g
    chain x = x

    infixr 4 _■_
    _■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h
    _■_ = trans

    syntax chain {f = f} pf = f [ pf ]
  open notations

  module conditions
    (σ-point-surjection : ∀ {f g} → (dup ⨾ (((σ⁻¹ f ⨾ σ) [××] g) ⨾ apply)) ≈ (g ⨾ f))
    where

    key : s [>] a
    key = dup ⨾ ((σ [××] id) ⨾ apply)

    key-law : ∀ {t : s [>] a} → (σ⁻¹ t ⨾ (dup ⨾ ((σ [××] id) ⨾ apply))) ≈ (σ⁻¹ t ⨾ t)
    key-law {t} = (σ⁻¹ t ⨾ (dup ⨾ ((σ [××] id) ⨾ apply)))              [ assoc ]
                ■ ((σ⁻¹ t ⨾ dup) ⨾ ((σ [××] id) ⨾ apply))              [ dup-natural ⨾-2map 2id ]
                ■ ((dup ⨾ (σ⁻¹ t [××] σ⁻¹ t)) ⨾ ((σ [××] id) ⨾ apply)) [ assoc⁻¹ ■ 2id ⨾-2map assoc ]
                ■ (dup ⨾ (((σ⁻¹ t [××] σ⁻¹ t) ⨾ (σ [××] id)) ⨾ apply)) [ 2id ⨾-2map ([××]-natural ⨾-2map 2id) ]
                ■ (dup ⨾ (((σ⁻¹ t ⨾ σ) [××] (σ⁻¹ t ⨾ id)) ⨾ apply))    [ 2id ⨾-2map ((2id [××]-2map rid) ⨾-2map 2id) ]
                ■ (dup ⨾ ((((σ⁻¹ t ⨾ σ) [××] σ⁻¹ t)) ⨾ apply))         [ σ-point-surjection ]
                ■ (σ⁻¹ t ⨾ t)                                          [ 2id ]

    module loopy-conditions = loopy-setup.conditions key key-law f
    open loopy-conditions public using (t ; fixpt)

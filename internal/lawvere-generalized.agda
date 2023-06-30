{-# OPTIONS --without-K #-}
open import common using (Σ ; _,_)
open Σ renaming (proj₁ to fst)
module lawvere-generalized
  {ℓ₀} {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄}
  (C : Set ℓ₀)

  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (id : ∀ {a} → a [>] a)

  (𝟙 : C)


  (A : C → Set ℓ₂)
  (_»_ : ∀ {a b} → (a [>] b) → A b → A a)

  (Q : A 𝟙 → Set ℓ₃)

  (a : C)
  (reflect : Σ (A 𝟙) Q → 𝟙 [>] a)

  (s : C)
  (P : A s → Set ℓ₄)

  (pack : Σ (A s) P → 𝟙 [>] s)
  (qual : ∀ ((t , p) : Σ (A s) P) → Q (pack (t , p) » t))

  (key : s [>] a)

  (f : A a)
  where

introspect : Σ (A s) P → Σ (A 𝟙) Q
introspect (t , p) = pack (t , p) » t , qual (t , p)

t : A s
t = key » f

module inner
  (p : P t)
  where

  fixpt : Σ (A 𝟙) Q
  fixpt = introspect (t , p)

  module inner
    {ℓe₀} (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓe₀)
    {ℓe₁} (_A≈_ : ∀ {a} → A a → A a → Set ℓe₁)
    (2idA : ∀ {a} {f : A a} → f A≈ f)
    (transA : ∀ {a} {f g h : A a} → f A≈ g → g A≈ h → f A≈ h)
    (_■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
    (assocA : ∀ {a b c} {f : a [>] b} {g : b [>] c} {h : A c} → (f » (g » h)) A≈ ((f ⨾ g) » h))
    (»-2map   : ∀ {a b} {f g : a [>] b} → f ≈ g → {h : A b} → (f » h) A≈ (g » h))

    (key-law : ∀ {(t , p) : Σ (A s) P} → (pack (t , p) ⨾ key) ≈ reflect (introspect (t , p)))
    where

    chain : ∀ {a} {f g : A a} → f A≈ g → f A≈ g
    chain x = x

    infixr 4 _A■_
    _A■_ : ∀ {a} {f g h : A a} → f A≈ g → g A≈ h → f A≈ h
    _A■_ = transA

    syntax chain {f = f} pf = f [ pf ]A

    proof : fst fixpt A≈ (reflect fixpt » f)
    proof = fst (introspect (t , p))             [ 2idA ]A
        A■ (pack (t , p) » t)                    [ 2idA ]A
        A■ (pack (t , p) » (key » f))            [ assocA ]A
        A■ ((pack (t , p) ⨾ key) » f)            [ »-2map key-law ]A
        A■ ((reflect (introspect (t , p))) » f)  [ 2idA ]A

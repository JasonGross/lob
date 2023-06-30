{-# OPTIONS --without-K --safe #-}
module loopy where
open import Agda.Primitive public
  using    (_⊔_)
infixr 1 _,_

record Σ {ℓ ℓ′} (A : Set ℓ) (P : A → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    fst : A
    snd : P fst

open Σ using (fst) public

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

module setup
  {ℓ₀} {ℓ₁} {ℓ₂} {ℓ₃}
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


  (Q : A 𝟙 → Set ℓ₃)


  (a : C)
  (reflect : Σ (A 𝟙) Q → 𝟙 [>] a)

  where

  module notations where
    chain : ∀ {a} {f g : A a} → f A≈ g → f A≈ g
    chain x = x

    infixr 4 _A■_
    _A■_ : ∀ {a} {f g h : A a} → f A≈ g → g A≈ h → f A≈ h
    _A■_ = transA

    syntax chain {f = f} pf = f [ pf ]A
  open notations

  Fixpoint : A a → Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓe₁)
  Fixpoint f = Σ[ xq ∈ Σ (A 𝟙) Q ] (fst xq A≈ (reflect xq » f))


  module conditions₁
    (s : C)
    {ℓ₄} (P : A s → Set ℓ₄)

    (pack : Σ (A s) P → 𝟙 [>] s)
    (qual : ∀ ((t , p) : Σ (A s) P) → Q (pack (t , p) » t))
    where

    introspect : Σ (A s) P → Σ (A 𝟙) Q
    introspect (t , p) = pack (t , p) » t , qual (t , p)

    module conditions₂
      (key : s [>] a)
      (key-law : ∀ {(t , p) : Σ (A s) P} → (pack (t , p) ⨾ key) ≈ reflect (introspect (t , p)))

      (f : A a)
      where

      t : A s
      t = key » f

      module theorem
        (p : P t)
        where

        fixpt : Fixpoint f
        fixpt = introspect (t , p) , proof
          module fixpt where
          proof : fst (introspect (t , p)) A≈ (reflect (introspect (t , p)) » f)
          proof = fst (introspect (t , p))             [ 2idA ]A
              A■ (pack (t , p) » t)                    [ 2idA ]A
              A■ (pack (t , p) » (key » f))            [ assocA ]A
              A■ ((pack (t , p) ⨾ key) » f)            [ »-2map key-law ]A
              A■ ((reflect (introspect (t , p))) » f)  [ 2idA ]A

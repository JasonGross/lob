{-# OPTIONS --without-K #-}
open import common using (Σ ; _⊔_)
  renaming (_,_ to _▻_)
import lawvere-generalized
module bounded-lob-from-generalized
  {ℓ₀} {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄}
  (C : Set ℓ₀)
  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (id : ∀ {a} → a [>] a)
  (𝟙 : C)

  (X : C)
  (□ : C → C)
  (Pred : C → Set ℓ₂)
  (Σ* : ∀ c → Pred c → C)
  (is-short : Pred (□ X))
  (is-very-short : 𝟙 [>] X → Set ℓ₃)
  (is-very-very-short : ∀ {a} → (𝟙 [>] a) → Set ℓ₄)
  (reflect : Σ (𝟙 [>] X) is-very-short → 𝟙 [>] Σ* (□ X) is-short)
  (s : C) -- s ~ Σ* (□(s [>] X)) λ{ m → Π[ s₀ : 𝟙 [>] s ] ((s₀ ⨾ m) ⟫ is-short) }
  (query : ∀ {x} → (x [>] s) → (x [>] Σ* (□ X) is-short))
  (pack : Σ (s [>] X) (λ f → (s₀ : 𝟙 [>] s) → is-very-very-short s₀ → is-very-short (s₀ ⨾ f)) → 𝟙 [>] s)
  (f : Σ* (□ X) is-short [>] X)
  where

Q : s [>] X → Set (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄)
Q f = ∀ (s₀ : 𝟙 [>] s) → is-very-very-short s₀ → is-very-short (s₀ ⨾ f)

module lg = lawvere-generalized C _[>]_ _⨾_ id (_[>] X) _⨾_ 𝟙 (Σ* (□ X) is-short) is-very-short reflect s query Q pack f
open lg public using (loop ; engine)

module inner
  (q : Q engine)
  (pack-short : ∀ eq → is-very-very-short (pack eq))
  where

  module lg-inner = lg.inner q
  open lg-inner public using (fixpt)

  push : (eq : Σ (s [>] X) Q) → is-very-short (pack eq ⨾ Σ.proj₁ eq)
  push (e ▻ qe) = qe (pack (e ▻ qe)) (pack-short (e ▻ qe))

  module lg-inner-inner = lg-inner.inner push
  open lg-inner-inner public using (p)

  module inner
    {ℓe₀} (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓe₀)
    (2id : ∀ {a b} {f : a [>] b} → f ≈ f)
    (_■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
    (rid : ∀ {a b} {f : a [>] b} → (f ⨾ id) ≈ f)
    (assoc : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d} → (f ⨾ (g ⨾ h)) ≈ ((f ⨾ g) ⨾ h))
    (_⨾-2map_ : ∀ {a b c} {f f′ : a [>] b} {g g′ : b [>] c} → f ≈ f′ → g ≈ g′ → (f ⨾ g) ≈ (f′ ⨾ g′))
    (query-natural : ∀ {X Y} {m : Y [>] X} {f : X [>] s} → (m ⨾ query {X} f) ≈ query {Y} (m ⨾ f))
    (query-2map    : ∀ {X} {f f′} → f ≈ f′ → query {X} f ≈ query {X} f′)
    (query-reflect : ∀ {eq : Σ (s [>] X) Q} → query (pack eq) ≈ reflect (loop eq ▻ push eq))
    where

    module lg-inner-inner-inner = lg-inner-inner.inner _≈_ _≈_ 2id _■_ _■_ rid assoc (_⨾-2map 2id) query-natural query-2map query-reflect
    open lg-inner-inner-inner public using (eq)

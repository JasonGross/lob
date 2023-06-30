{-# OPTIONS --without-K #-}
open import common using (Σ ; _⊔_ ; _,_)
import lawvere-generalized
module spurious-counterfactuals-from-generalized
  {ℓ₀} {ℓ₁} {ℓ₂} {ℓ₃}
  (C : Set ℓ₀)
  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (id : ∀ {a} → a [>] a)
  (𝟙 : C)

  (act : C)
  (□ : C → C)
  (Pred : C → Set ℓ₂)
  (Σ* : ∀ c → Pred c → C)
  (isgood : 𝟙 [>] act → Set ℓ₃)
  (qisgood : Pred (□ act))
  (reflect : Σ (𝟙 [>] act) isgood → 𝟙 [>] Σ* (□ act) qisgood)
  (s : C) -- s ~ Σ* (□(s [>] act)) λ{ m → Π[ s₀ : 𝟙 [>] s ] ((s₀ ⨾ m) ⟫ qisgood) }
  (pack : Σ (s [>] act) (λ f → (s₀ : 𝟙 [>] s) → isgood (s₀ ⨾ f)) → 𝟙 [>] s)
  (key : s [>] Σ* (□ act) qisgood)
  (qual : ∀ ((t , p) : Σ (s [>] act) λ{ f → (s₀ : 𝟙 [>] s) → isgood (s₀ ⨾ f) }) → isgood (pack (t , p) ⨾ t))
  (f : Σ* (□ act) qisgood [>] act)
  where

P : s [>] act → Set (ℓ₁ ⊔ ℓ₃)
P f = ∀ (s₀ : 𝟙 [>] s) → isgood (s₀ ⨾ f)

module lg = lawvere-generalized C _[>]_ _⨾_ id 𝟙 (_[>] act) _⨾_ isgood (Σ* (□ act) qisgood) reflect s P pack qual key f
open lg public using (introspect ; t)

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

    (key-law : ∀ {(t , p) : Σ (s [>] act) P} → (pack (t , p) ⨾ key) ≈ reflect (introspect (t , p)))
    where

    module lg-inner-inner = lg-inner.inner _≈_ _≈_ 2id _■_ _■_ assoc (_⨾-2map 2id) key-law
    open lg-inner-inner public using (proof)

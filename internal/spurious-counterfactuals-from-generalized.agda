{-# OPTIONS --without-K #-}
open import common using (Σ ; _⊔_)
  renaming (_,_ to _▻_)
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
  (query : ∀ {x} → (x [>] s) → (x [>] Σ* (□ act) qisgood))
  (pack : Σ (s [>] act) (λ f → (s₀ : 𝟙 [>] s) → isgood (s₀ ⨾ f)) → 𝟙 [>] s)
  (f : Σ* (□ act) qisgood [>] act)
  where

Q : s [>] act → Set (ℓ₁ ⊔ ℓ₃)
Q f = ∀ (s₀ : 𝟙 [>] s) → isgood (s₀ ⨾ f)

module lg = lawvere-generalized C _[>]_ _⨾_ id (_[>] act) _⨾_ 𝟙 (Σ* (□ act) qisgood) isgood reflect s query Q pack f
open lg public using (loop ; engine)

module inner
  (q : (s₀ : 𝟙 [>] s) → isgood (s₀ ⨾ (query id ⨾ f)))
  where

  module lg-inner = lg.inner q
  open lg-inner public using (fixpt)

  push : (eq : Σ (s [>] act) Q) → isgood (pack eq ⨾ Σ.proj₁ eq)
  push (e ▻ qe) = qe (pack (e ▻ qe))

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
    (query-reflect : ∀ {eq : Σ (s [>] act) Q} → query (pack eq) ≈ reflect (loop eq ▻ push eq))
    where

    module lg-inner-inner-inner = lg-inner-inner.inner _≈_ _≈_ 2id _■_ _■_ rid assoc (_⨾-2map 2id) query-natural query-2map query-reflect
    open lg-inner-inner-inner public using (eq)

{-# OPTIONS --without-K #-}
open import common using (Σ ; _⊔_)
  renaming (_,_ to _▻_)
import lawvere-generalized
module spurious-counterfactuals-from-generalized
  {ℓ₀} {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄}
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
  (quot-is-good : Σ (𝟙 [>] act) isgood → 𝟙 [>] Σ* (□ act) qisgood)
  (s : C) -- s ~ Σ (□(s [>] act)) ...
  (query : ∀ {x} → (x [>] s) → (x [>] Σ* (□ act) qisgood))
  (pack : Σ (s [>] act) (λ f → (s₀ : 𝟙 [>] s) → isgood (s₀ ⨾ f)) → 𝟙 [>] s)
  (f : Σ* (□ act) qisgood [>] act)
  where

Q : s [>] act → Set (ℓ₁ ⊔ ℓ₃)
Q f = ∀ (s₀ : 𝟙 [>] s) → isgood (s₀ ⨾ f)

module lg = lawvere-generalized C _[>]_ _⨾_ id (_[>] act) _⨾_ 𝟙 (Σ* (□ act) qisgood) isgood quot-is-good s query Q pack f
module lg-inner = lg.inner {!!}
{-
  {ℓ₀} {ℓ₁} {ℓ₂} {ℓ₃} {ℓ₄}
  (C : Set ℓ₀)
  (_[>]_ : C → C → Set ℓ₁)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (id : ∀ {a} → a [>] a)
  (A : C → Set ℓ₂)
  (_»_ : ∀ {a b} → (a [>] b) → A b → A a)
  (𝟙 : C)

  (a : C) (P : A 𝟙 → Set ℓ₃)
  (reflect : Σ (A 𝟙) P → 𝟙 [>] a)

  (s : C) (query : ∀ {x} → x [>] s → x [>] a)

  (Q : A s → Set ℓ₄)
  (pack : Σ (A s) Q → 𝟙 [>] s)

  (f : A a)
  where

loop : Σ (A s) Q → A 𝟙
loop (e ▻ q) = pack (e ▻ q) » e

engine : A s
engine = query id » f

module inner
  (q : Q engine)
  where

  fixpt : A 𝟙
  fixpt = loop (engine ▻ q)

  module inner
    (push : ∀ (eq : Σ (A s) Q) → P (loop eq))
    where

    p : P fixpt
    p = push (engine ▻ q)

    module inner
      {ℓe₀} (_≈_ : ∀ {a b} → (f g : a [>] b) → Set ℓe₀)
      {ℓe₁} (_A≈_ : ∀ {a} → A a → A a → Set ℓe₁)
      (2idA : ∀ {a} {f : A a} → f A≈ f)
      (transA : ∀ {a} {f g h : A a} → f A≈ g → g A≈ h → f A≈ h)
      (_■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h)
      (rid : ∀ {a b} {f : a [>] b} → (f ⨾ id) ≈ f)
      (assocA : ∀ {a b c} {f : a [>] b} {g : b [>] c} {h : A c} → (f » (g » h)) A≈ ((f ⨾ g) » h))
      (»-2map   : ∀ {a b} {f g : a [>] b} → f ≈ g → {h : A b} → (f » h) A≈ (g » h))
      (query-natural : ∀ {X Y} {m : Y [>] X} {f : X [>] s} → (m ⨾ query {X} f) ≈ query {Y} (m ⨾ f))
      (query-2map    : ∀ {X} {f f′} → f ≈ f′ → query {X} f ≈ query {X} f′)
      (query-reflect : ∀ {eq : Σ (A s) Q} → query (pack eq) ≈ reflect (loop eq ▻ push eq))
      where

      chain : ∀ {a} {f g : A a} → f A≈ g → f A≈ g
      chain x = x

      infixr 4 _A■_
      _A■_ : ∀ {a} {f g h : A a} → f A≈ g → g A≈ h → f A≈ h
      _A■_ = transA

      syntax chain {f = f} pf = f [ pf ]A


      eq : fixpt A≈ (reflect (fixpt ▻ p) » f)
      eq = fixpt                                                      [ 2idA ]A
        A■ loop (engine ▻ q)                                          [ 2idA ]A
        A■ (pack (engine ▻ q) » engine)                               [ 2idA ]A
        A■ (pack (engine ▻ q) » (query id » f))                       [ assocA ]A
        A■ ((pack (engine ▻ q) ⨾ query id) » f)                       [ »-2map (query-natural ■ query-2map rid) ]A
        A■ ((query (pack (engine ▻ q))) » f)                          [ »-2map query-reflect ]A
        A■ (reflect (loop(engine ▻ q) ▻ push(engine ▻ q)) » f)        [ 2idA ]A
        A■ (reflect (fixpt ▻ p) » f)                                  [ 2idA ]A
-}

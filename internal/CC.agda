{-# OPTIONS --without-K #-}
module CC where
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc; Setω)
record CartesianCat {ℓ₀ ℓ₁ ℓ₂} : Set (lsuc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Obj   : Set ℓ₀
    _[>]_ : Obj → Obj → Set ℓ₁
    _≈_   : ∀ {a b} → (a [>] b) → (a [>] b) → Set ℓ₂
    id    : ∀ {a} → a [>] a
    _⨾_   : ∀ {a b c} → a [>] b → b [>] c → a [>] c
    𝟙     : Obj
    _×_   : Obj → Obj → Obj
    *     : ∀ {a} → (a [>] 𝟙)
    dup   : ∀ {a} → a [>] (a × a)
    _××_  : ∀ {a b c d} → a [>] c → b [>] d → (a × b) [>] (c × d)
    {-getl  : ∀ {a b} → (a × b) [>] a
    getr  : ∀ {a b} → (a × b) [>] b-}

    _■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h
    _⁻¹      : ∀ {a b} {f g : a [>] b} → f ≈ g → g ≈ f
    2id      : ∀ {a b} {f : a [>] b} → f ≈ f
    _⨾-map_ : ∀ {a b c} {f f‵ : a [>] b} {g g‵ : b [>] c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵)

    lid   : ∀ {a b} {f : a [>] b} → (id ⨾ f) ≈ f
    rid   : ∀ {a b} {f : a [>] b} → (f ⨾ id) ≈ f
    assoc : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d}
            → ((f ⨾ g) ⨾ h) ≈ (f ⨾ (g ⨾ h))

    *-law : ∀ {a} {f g : a [>] 𝟙} → f ≈ g
    ××id  : ∀ {a b} → (id {a} ×× id {b}) ≈ id
    {-dup-getl : ∀ {a} → (dup {a} ⨾ getl) ≈ id
    dup-getr : ∀ {a} → (dup {a} ⨾ getr) ≈ id-}
    ××-natural : ∀ {a b c a′ b′ c′} {f : a [>] b} {g : b [>] c} {f′ : a′ [>] b′} {g′ : b′ [>] c′}
                 → ((f ⨾ g) ×× (f′ ⨾ g′)) ≈ ((f ×× f′) ⨾ (g ×× g′))
    dup-natural : ∀ {a b} {f : a [>] b} → (dup ⨾ (f ×× f)) ≈ (f ⨾ dup)
    {-getl-natural : ∀ {a b a′ b′} {f : a [>] b} {f′ : a′ [>] b′}
                   → ((f ×× f′) ⨾ getl) ≈ (getl ⨾ f)
    getr-natural : ∀ {a b a′ b′} {f : a [>] b} {f′ : a′ [>] b′}
                   → ((f ×× f′) ⨾ getr) ≈ (getr ⨾ f′)-}
    _××-2map_ : ∀ {a b a′ b′} {f g : a [>] b} {f′ g′ : a′ [>] b′} → f ≈ g → f′ ≈ g′ → (f ×× f′) ≈ (g ×× g′)

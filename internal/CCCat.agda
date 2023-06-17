{-# OPTIONS --without-K #-}
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc; Setω)
module CCCat {ℓ₀ ℓ₁ ℓ₂} where
record Cat : Set (lsuc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Obj   : Set ℓ₀
    _[>]_ : Obj → Obj → Set ℓ₁
    _≈_   : ∀ {a b} → (a [>] b) → (a [>] b) → Set ℓ₂
    id    : ∀ {a} → a [>] a
    _⨾_   : ∀ {a b c} → a [>] b → b [>] c → a [>] c

    _■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h
    _⁻¹      : ∀ {a b} {f g : a [>] b} → f ≈ g → g ≈ f
    2id      : ∀ {a b} {f : a [>] b} → f ≈ f
    _⨾-map_ : ∀ {a b c} {f f‵ : a [>] b} {g g‵ : b [>] c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵)

    lid   : ∀ {a b} {f : a [>] b} → (id ⨾ f) ≈ f
    rid   : ∀ {a b} {f : a [>] b} → (f ⨾ id) ≈ f
    assoc : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d}
            → ((f ⨾ g) ⨾ h) ≈ (f ⨾ (g ⨾ h))

record IsCartesian (C : Cat) : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂) where
  open Cat C
  field
    𝟙     : Obj
    _×_   : Obj → Obj → Obj
    *     : ∀ {a} → (a [>] 𝟙)
    dup   : ∀ {a} → a [>] (a × a)
    _××_  : ∀ {a b c d} → a [>] c → b [>] d → (a × b) [>] (c × d)
    {-getl  : ∀ {a b} → (a × b) [>] a
    getr  : ∀ {a b} → (a × b) [>] b-}

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

record Functor (A B : Cat) : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂) where
  open Cat
  open Cat A using () renaming (_[>]_ to _A∙[>]_ ; _≈_ to _A∙≈_ ; _⨾_ to _A∙⨾_)
  open Cat B using () renaming (_[>]_ to _B∙[>]_ ; _≈_ to _B∙≈_ ; _⨾_ to _B∙⨾_)
  field
    run : A .Obj → B .Obj
    map : ∀ {a b} → a A∙[>] b → run a B∙[>] run b
    map-id : ∀ {a} → map (A .id {a}) B∙≈ B .id {run a}
    map-⨾  : ∀ {a b c} {f : a A∙[>] b} {g : b A∙[>] c} → map (f A∙⨾ g) B∙≈ (map f B∙⨾ map g)

    2-map : ∀ {a b} {f g : a A∙[>] b} → f A∙≈ g → map f B∙≈ map g
    {-
    _■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h
    _⁻¹      : ∀ {a b} {f g : a [>] b} → f ≈ g → g ≈ f
    2id      : ∀ {a b} {f : a [>] b} → f ≈ f
    _⨾-map_ : ∀ {a b c} {f f‵ : a [>] b} {g g‵ : b [>] c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵)

    lid   : ∀ {a b} {f : a [>] b} → (id ⨾ f) ≈ f
    rid   : ∀ {a b} {f : a [>] b} → (f ⨾ id) ≈ f
    assoc : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d}
            → ((f ⨾ g) ⨾ h) ≈ (f ⨾ (g ⨾ h))


{-
        Obj   : Set ℓ₀
    _[>]_ : Obj → Obj → Set ℓ₁
    _≈_   : ∀ {a b} → (a [>] b) → (a [>] b) → Set ℓ₂
    id    : ∀ {a} → a [>] a
    _⨾_   : ∀ {a b c} → a [>] b → b [>] c → a [>] c

-}
-}

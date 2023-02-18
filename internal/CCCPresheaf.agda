{-# OPTIONS --without-K #-}
module CCCPresheaf where
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc; Setω)
open import CCC

-- some bits of a Presheaf/Family-like object
record Presheaf {ℓ₀ ℓ₁ ℓ₂ ℓp₀ ℓp₁ ℓe₂ ℓp₂} (C : CartesianClosedCat {ℓ₀} {ℓ₁} {ℓ₂}) : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ lsuc (ℓp₀ ⊔ ℓp₁ ⊔ ℓe₂ ⊔ ℓp₂)) where
  open CartesianClosedCat C
  field
    Psh  : Obj → Set ℓp₀
    Π    : ∀ {a} → Psh a → Psh a → Set ℓp₁
  Π_[→]_ : ∀ {a} → Psh a → Psh a → Set ℓp₁
  Π_[→]_ = Π
  Π[_]_[→]_ : ∀ a → Psh a → Psh a → Set ℓp₁
  Π[ a ] x [→] y = Π {a} x y
  field
    _≈ₑ_ : ∀ {a} → Psh a → Psh a → Set ℓp₂ -- equivalence of categories or w/e

    _⨾ₛ_ : ∀ {a b} → (a [>] b) → Psh b → Psh a

    _≈ₚ[_]_ : ∀ {a b x y} {f : a [>] b} {g} → (Π[ a ] x [→] (f ⨾ₛ y)) → f ≈ g → (Π[ a ] x [→] (g ⨾ₛ y)) → Set ℓp₂

    idₚ  : ∀ {a x} → Π[ a ] x [→] (id ⨾ₛ x)
    _⨾ₚ_ : ∀ {a b c x y z} → {f : a [>] b} {g : b [>] c} → Π[ a ] x [→] (f ⨾ₛ y) → Π[ b ] y [→] (g ⨾ₛ z) → Π[ a ] x [→] ((f ⨾ g) ⨾ₛ z)

    _■ₚ_     : ∀ {a b x y} {f g h : a [>] b}
      {p : Π[ a ] x [→] (f ⨾ₛ y)}
      {e : f ≈ g} {q : Π[ a ] x [→] (g ⨾ₛ y)} →
      (p ≈ₚ[ e ] q) →
      {e′ : g ≈ h} {r : Π[ a ] x [→] (h ⨾ₛ y)} →
      (q ≈ₚ[ e′ ] r) →
      (p ≈ₚ[ e ■ e′ ] r)
    _⁻¹ₚ     : ∀ {a b x y} {f g : a [>] b}
      {p : Π[ a ] x [→] (f ⨾ₛ y)} {e : f ≈ g} {q : Π[ a ] x [→] (g ⨾ₛ y)} →
      p ≈ₚ[ e ] q → q ≈ₚ[ e ⁻¹ ] p
    2idₚ     : ∀ {a b x y} {f : a [>] b} {p : Π[ a ] x [→] (f ⨾ₛ y)} → p ≈ₚ[ 2id ] p
    _⨾-mapₚ_ : ∀ {a b c x y z} {f f′ : a [>] b} {g g′ : b [>] c}
      {p : Π[ a ] x [→] (f ⨾ₛ y)}
      {ff : f ≈ f′} {p′ : Π[ a ] x [→] (f′ ⨾ₛ y)} →
      (p ≈ₚ[ ff ] p′) →
      {q : Π[ b ] y [→] (g ⨾ₛ z)}
      {gg : g ≈ g′} {q′ : Π[ b ] y [→] (g′ ⨾ₛ z)} →
      (q ≈ₚ[ gg ] q′) →
      (p ⨾ₚ q) ≈ₚ[ ff ⨾-map gg ] (p′ ⨾ₚ q′)

    lidₚ   : ∀ {a b x y} {f : a [>] b} {p : Π[ a ] x [→] (f ⨾ₛ y)} → (idₚ ⨾ₚ p) ≈ₚ[ lid ] p
    ridₚ   : ∀ {a b x y} {f : a [>] b} {p : Π[ a ] x [→] (f ⨾ₛ y)} → (p ⨾ₚ idₚ) ≈ₚ[ rid ] p
    assocₚ : ∀ {a b c d x y z w} {f : a [>] b} {g : b [>] c} {h : c [>] d}
               {p : Π[ a ] x [→] (f ⨾ₛ y)} {q : Π[ b ] y [→] (g ⨾ₛ z)} {r : Π[ c ] z [→] (h ⨾ₛ w)}
            → ((p ⨾ₚ q) ⨾ₚ r) ≈ₚ[ assoc ] (p ⨾ₚ (q ⨾ₚ r))

    _■ₑ_   : ∀ {a} {x y z : Psh a} → x ≈ₑ y → y ≈ₑ z → x ≈ₑ z
    _⁻¹ₑ   : ∀ {a} {x y : Psh a} → x ≈ₑ y → y ≈ₑ x
    2idₑ   : ∀ {a} {x : Psh a} → x ≈ₑ x

    subst-id  : ∀ {a} {x : Psh a} → (id ⨾ₛ x) ≈ₑ x
    assocₛ    : ∀ {a b c} {f : a [>] b} {g : b [>] c} {x : Psh c} → ((f ⨾ g) ⨾ₛ x) ≈ₑ (f ⨾ₛ (g ⨾ₛ x))
    subst-map : ∀ {a b} {f g : a [>] b} {x : Psh b} → f ≈ g → (f ⨾ₛ x) ≈ₑ (g ⨾ₛ x)


    -- TODO: What's the nice form of this?
    subst-map-Π : ∀ {a b x y} {f g : a [>] b} → f ≈ g → (Π[ a ] x [→] (f ⨾ₛ y)) → (Π[ a ] x [→] (g ⨾ₛ y))
    -- _Π⨾ₑ_ : ∀ {a} {x y x' y' : Psh a} → x' ≈ₑ x → y ≈ₑ y' → (Π[ a ] x [→] y) → (Π[ a ] x' [→] y')
    subst-map-Π-eq : ∀ {a b x y} {f g : a [>] b} {e : f ≈ g} {F : Π[ a ] x [→] (f ⨾ₛ y)} → F ≈ₚ[ e ] subst-map-Π e F

    -- _Π⨾ₛ_ : ∀ {a b x y} → (f : a [>] b) → Π[ b ] x [→] y → Π[ a ] (f ⨾ₛ x) [→] (f ⨾ₛ y)

    -- TODO: interaction of ≈ₑ and ≈ₚ
    -- TODO: id Π⨾ₛ f = f
    -- TODO: f Π⨾ₛ Πid = Πid
    -- TODO: (f ⨾ g) Π⨾ₛ h = f Π⨾ₛ (g ⨾ₛ h)

    --≈ₚ-id : ∀ {a b x y} {f : a [>] b} {g} → (F : Π[ a ] x [→] (f ⨾ₛ y)) → (e : f ≈ g) → (G : Π[ a ] x [→] (g ⨾ₛ y)) → (? ≈


record PresheafHasΣ {ℓ₀ ℓ₁ ℓ₂ ℓp₀ ℓp₁ ℓe₂ ℓp₂} {C : CartesianClosedCat {ℓ₀} {ℓ₁} {ℓ₂}}
                    (T : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓp₀} {ℓp₁} {ℓe₂} {ℓp₂} C)
                    : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓp₀ ⊔ ℓp₁ ⊔ ℓe₂ ⊔ ℓp₂) where
  open CartesianClosedCat C
  open Presheaf T
  field
    𝟙ₚ : ∀ {a} → Psh a
    Σ : ∀ {a : Obj} → Psh a → Obj

    *ₚ : ∀ {a b x} (f : a [>] b) → Π[ a ] x [→] (f ⨾ₛ 𝟙ₚ)
    *ₚ-law : ∀ {a b x} {f g : a [>] b} {p : Π[ a ] x [→] (f ⨾ₛ 𝟙ₚ)} {e : f ≈ g} {q : Π[ a ] x [→] (g ⨾ₛ 𝟙ₚ)} → p ≈ₚ[ e ] q


    dupΣ : ∀ {a} → a [>] Σ {a} 𝟙ₚ
    _ΣΣ_ : ∀ {a b x y} → (f : a [>] b) → (Π[ a ] x [→] (f ⨾ₛ y)) → (Σ {a} x [>] Σ {b} y)
    fst  : ∀ {a x} → Σ {a} x [>] a
    snd  : ∀ {a x} → Π[ Σ {a} x ] 𝟙ₚ [→] (fst ⨾ₛ x)

    dup-fst : ∀ {a} → (dupΣ {a} ⨾ fst) ≈ id
    dup-snd : ∀ {a} → (*ₚ dupΣ ⨾ₚ snd) ≈ₚ[ dup-fst {a} ] idₚ
    dup-fst-snd : ∀ {a x} → (dupΣ {Σ {a} x} ⨾ (fst ΣΣ snd)) ≈ id
    ΣΣ-natural : ∀ {a b c x y z} {f : a [>] b} {g : b [>] c} {F : Π[ a ] x [→] (f ⨾ₛ y)} {G : Π[ b ] y [→] (g ⨾ₛ z)}
                 → ((f ⨾ g) ΣΣ (F ⨾ₚ G)) ≈ ((f ΣΣ F) ⨾ (g ΣΣ G))
    dup-ΣΣ : ∀ {a b} {f : a [>] b} → (dupΣ ⨾ (f ΣΣ *ₚ f)) ≈ (f ⨾ dupΣ)
    _ΣΣ-2map_ : ∀ {a b x y} {f f′ : a [>] b} {g : Π[ a ] x [→] (f ⨾ₛ y)} {g′ : Π[ a ] x [→] (f′ ⨾ₛ y)}
      → (e : f ≈ f′) → g ≈ₚ[ e ] g′ → (f ΣΣ g) ≈ (f′ ΣΣ g′)
    Σ-map-id : ∀ {a x} → (id ΣΣ idₚ) ≈ id {Σ {a} x}
    fst-natural : ∀ {a b x y} {f : a [>] b} {g : Π[ a ] x [→] (f ⨾ₛ y)} → ((f ΣΣ g) ⨾ fst) ≈ (fst ⨾ f)
    snd-natural : ∀ {a b x y} {f : a [>] b} {g : Π[ a ] x [→] (f ⨾ₛ y)} → (*ₚ (f ΣΣ g) ⨾ₚ snd) ≈ₚ[ fst-natural {a} {b} {x} {y} {f} {g} ] (snd ⨾ₚ g)

  pair : ∀ {a b y} → (f : a [>] b) → (Π[ a ] 𝟙ₚ [→] (f ⨾ₛ y)) → (a [>] Σ {b} y)
  pair f g = dupΣ ⨾ (f ΣΣ g)
  pair-fst : ∀ {a b y f g} → (pair {a} {b} {y} f g ⨾ fst) ≈ f
  pair-fst = (2id ⨾-map 2id) ■ (assoc ■ ((2id ⨾-map fst-natural) ■ ((assoc ⁻¹) ■ ((dup-fst ⨾-map 2id) ■ lid))))
  pair-snd : ∀ {a b y f g} → (*ₚ (pair {a} {b} {y} f g) ⨾ₚ snd) ≈ₚ[ pair-fst {a} {b} {y} {f} {g} ] g
  pair-snd = (*ₚ-law ⨾-mapₚ 2idₚ) ■ₚ (assocₚ ■ₚ ((2idₚ ⨾-mapₚ snd-natural) ■ₚ ((assocₚ ⁻¹ₚ) ■ₚ ((dup-snd ⨾-mapₚ 2idₚ) ■ₚ lidₚ))))
  pair-η   : ∀ {a b y} {f : a [>] Σ {b} y} → (pair (f ⨾ fst) (*ₚ f ⨾ₚ snd)) ≈ f
  pair-η = (2id ⨾-map ΣΣ-natural) ■ ((assoc ⁻¹) ■ ((dup-ΣΣ ⨾-map 2id) ■ (assoc ■ ((2id ⨾-map dup-fst-snd) ■ rid))))
  pair-2map : ∀ {a b y f f' g g'} → (e : f ≈ f') → g ≈ₚ[ e ] g' → pair {a} {b} {y} f g ≈ pair {a} {b} {y} f' g'
  pair-2map ff gg = 2id ⨾-map (ff ΣΣ-2map gg)
    {-

    pair-wk : ∀ {a x} → Π[ a ] x [→] (* ⨾ₛ Wk (Σ {a} x))
    𝟙-law   : ∀ {a} → Σ (Wk a) [>] a
    -- TODO: more rules about Σ
    -- ρ₁ : (Σ.μ * ι); ε = id
    -- ρ₂ : ι; (μ ε)[*] = id
    -- μ-natural : μ (p; q) = μ p; μ q
    -- ι-natural : ι; μ (Σ.μ f g) = g; ι[f]
    -- ε-natural : (Σ.μ * (μ p)); ε = ε; p
    -- alt: uncurryΣ : ∀ {a b x} → (Σ {a} x [>] b) → (Π[ a ] x [→] (* ⨾ₛ Wk b))
    uncurryΣ : ∀ {a b x} → (Σ {a} x [>] b) → (Π[ a ] x [→] (* ⨾ₛ Wk b))
-}

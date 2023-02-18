{-# OPTIONS --without-K #-}
module CCCCodistributiveSemicomonad where
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc; Setω)
open import CCC
open import CCCPresheaf

-- a semicomonad that codistributes over 𝟙 and _×_ (since behavior of
-- _~>_ is determined by _×_, we do not need any laws about
-- interaction with _~>_) and Σ
record CodistributiveSemicomonad {ℓ₀ ℓ₁ ℓ₂ ℓp₀ ℓp₁ ℓe₂ ℓp₂} (C : CartesianClosedCat {ℓ₀} {ℓ₁} {ℓ₂})
                                 (T : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓp₀} {ℓp₁} {ℓe₂} {ℓp₂} C)
                                 (TΣ : PresheafHasΣ T)
                                 : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓp₀ ⊔ ℓp₁ ⊔ ℓe₂ ⊔ ℓp₂) where
  open CartesianClosedCat C
  open Presheaf T
  open PresheafHasΣ TΣ
  field
    □     : Obj → Obj
    □-map : ∀ {a b} → a [>] b → □ a [>] □ b

    cojoin : ∀ {a} → □ a [>] □ (□ a)

    □-𝟙-codistr  : 𝟙 [>] □ 𝟙
    □-×-codistr  : ∀ {a b} → (□ a × □ b) [>] □ (a × b)

    □-id    : ∀ {a} → □-map (id {a}) ≈ id
    □-⨾-map : ∀ {a b c} {f : a [>] b} {g : b [>] c} → □-map (f ⨾ g) ≈ (□-map f ⨾ □-map g)

    □-2map  : ∀ {a b} {f f′ : a [>] b} → (f ≈ f′) → (□-map f) ≈ (□-map f′)

    -- points are quoted with `□-𝟙-codistr ⨾ □-map`, quoted terms are
    -- requoted with `cojoin`; these must agree on closed quoted terms
    □-map-cojoin : ∀ {a} {f : 𝟙 [>] □ a} → (f ⨾ cojoin) ≈ (□-𝟙-codistr ⨾ □-map f)

    □-×-codistr-dup  : ∀ {a} → (dup {□ a} ⨾ □-×-codistr) ≈ □-map dup
    □-map-××-codistr : ∀ {a b c d} {f : a [>] b} {g : c [>] d}
                       → ((□-map f ×× □-map g) ⨾ □-×-codistr) ≈ (□-×-codistr ⨾ □-map (f ×× g))

  field
    □ₚ : ∀ {a} → Psh a → Psh (□ a)
    □ₚ-map : ∀ {a b x y} → {f : a [>] b} → (Π[ a ] x [→] (f ⨾ₛ y)) → (Π[ □ a ] (□ₚ x) [→] (□-map f ⨾ₛ □ₚ y))

    cojoinₚ : ∀ {a x} → Π[ □ a ] □ₚ x [→] (cojoin ⨾ₛ □ₚ (□ₚ x))

    □ₚ-id    : ∀ {a x} → □ₚ-map (idₚ {a} {x}) ≈ₚ[ □-id ] idₚ
    □ₚ-⨾-map : ∀ {a b c x y z} {f : a [>] b} {g : b [>] c} {F : Π[ a ] x [→] (f ⨾ₛ y)} → {G : Π[ b ] y [→] (g ⨾ₛ z)}
      → □ₚ-map (F ⨾ₚ G) ≈ₚ[ □-⨾-map ] (□ₚ-map F ⨾ₚ □ₚ-map G)

    □ₚ-2map  : ∀ {a b x y} {f f′ : a [>] b} {F : Π[ a ] x [→] (f ⨾ₛ y)} {ff : f ≈ f′} {F′ : Π[ a ] x [→] (f′ ⨾ₛ y)} → (F ≈ₚ[ ff ] F′) → (□ₚ-map F) ≈ₚ[ □-2map ff ] (□ₚ-map F′)

    □-𝟙ₚ-codistr : ∀ {a} → Π[ □ a ] 𝟙ₚ [→] (id ⨾ₛ □ₚ 𝟙ₚ)
    □-*ₚ-codistr : ∀ {a b} {f : a [>] b} → (*ₚ (□-map f) ⨾ₚ □-𝟙ₚ-codistr) ≈ₚ[ rid ■ (lid ⁻¹) ] (□-𝟙ₚ-codistr ⨾ₚ □ₚ-map (*ₚ f))
    □-Σ-codistr : ∀ {a x} → (Σ {□ a} (□ₚ x)) [>] (□ (Σ {a} x))

    -- TODO: What's up with rid ⁻¹
    □-map-cojoinₚ : ∀ {a x} {f : 𝟙 [>] □ a} {p : Π[ 𝟙 ] 𝟙ₚ [→] (f ⨾ₛ □ₚ x)} → (p ⨾ₚ cojoinₚ) ≈ₚ[ □-map-cojoin ■ ((rid ⁻¹) ⨾-map 2id) ] ((*ₚ □-𝟙-codistr ⨾ₚ □-𝟙ₚ-codistr) ⨾ₚ □ₚ-map p)

    □-map-subst : ∀ {a b x} {f : a [>] b} → (□-map f ⨾ₛ □ₚ x) ≈ₑ □ₚ (f ⨾ₛ x)

    □-Σ-codistr-dup  : ∀ {a} → (dupΣ {□ a} ⨾ ((id ΣΣ □-𝟙ₚ-codistr) ⨾ □-Σ-codistr)) ≈ □-map dupΣ
    □-map-ΣΣ-codistr : ∀ {a b x y} {f : a [>] b} {g : Π[ a ] x [→] (f ⨾ₛ y)} → ((□-map f ΣΣ □ₚ-map g) ⨾ □-Σ-codistr) ≈ (□-Σ-codistr ⨾ □-map (f ΣΣ g))
    -- TODO: What is this next one???
    -- dupΣ-□-𝟙-ΣΣ-codistr : (dupΣ {𝟙} ⨾ ((□-𝟙-codistr ΣΣ □ₚ-𝟙-codistr) ⨾ □-Σ-codistr)) ≈ (□-𝟙-codistr ⨾ □-map (dupΣ {𝟙}))

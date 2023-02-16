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

  open Presheaf T
  open PresheafHasΣ TΣ
  field
    □ₚ : ∀ {a} → Psh a → Psh (□ a)
    □ₚ-map : ∀ {a b x y} → {f : a [>] b} → (Π[ a ] x [→] (f ⨾ₛ y)) → (Π[ □ a ] (□ₚ x) [→] (□-map f ⨾ₛ □ₚ y))

    -- TODO: other fields

    □ₚ-𝟙-codistr  : Π 𝟙ₚ [→] (□-𝟙-codistr ⨾ₛ □ₚ 𝟙ₚ)
    -- □ₚ-𝟙-codistr'  : Π[ □ 𝟙 ] 𝟙ₚ [→] (id ⨾ₛ □ₚ 𝟙ₚ) -- ???
    □-Wk-codistr : ∀ {a} → Π[ 𝟙 ] (Wk (□ a)) [→] (□-𝟙-codistr ⨾ₛ □ₚ (Wk a))
    □-Σ-codistr : ∀ {a x} → (Σ {□ a} (□ₚ x)) [>] (□ (Σ {a} x))

    □-map-subst : ∀ {a b x} {f : a [>] b} → (□-map f ⨾ₛ □ₚ x) ≈ₑ □ₚ (f ⨾ₛ x)

    □-map-ΣΣ-codistr : ∀ {a b x y} {f : a [>] b} {g : Π[ a ] x [→] (f ⨾ₛ y)} → ((□-map f ΣΣ □ₚ-map g) ⨾ □-Σ-codistr) ≈ (□-Σ-codistr ⨾ □-map (f ΣΣ g))
    -- TODO: What is this next one???
    dupΣ-□-𝟙-ΣΣ-codistr : (dupΣ {𝟙} ⨾ ((□-𝟙-codistr ΣΣ □ₚ-𝟙-codistr) ⨾ □-Σ-codistr)) ≈ (□-𝟙-codistr ⨾ □-map (dupΣ {𝟙}))

{-# OPTIONS --without-K --allow-unsolved-metas #-}
module lawvere-factored-alt where
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc; Setω)
open import CCC public
open import CCCPresheaf public
open import CCCCodistributiveSemicomonad public

module generic
  {ℓ₀ ℓ₁ ℓ₂ ℓt₀ ℓt₁ ℓte₂ ℓt₂ ℓty₀ ℓty₁ ℓtye₂ ℓty₂}
  (CCat : CartesianClosedCat {ℓ₀} {ℓ₁} {ℓ₂})
  (TyCat : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓty₀} {ℓty₁} {ℓtye₂} {ℓty₂} CCat)
  (TCat : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓt₀} {ℓt₁} {ℓte₂} {ℓt₂} CCat) -- like (_[>] X)
  (TyΣ : PresheafHasΣ TyCat)
  (□Func : CodistributiveSemicomonad CCat TyCat TyΣ)
  where

  open CartesianClosedCat CCat renaming (Obj to C)
  -- open Presheaf hiding (Π_[→]_ ; Π[_]_[→]_ ; _≈ₑ_ ; _≈ₚ[_]_ ; _⨾ₚ_ ; _⨾ₛ_ ; _Π⨾ₑ_ ; _■ₑ_ ; _⁻¹ₑ ; 2idₑ)
  open Presheaf TyCat renaming (Psh to Ty)
  -- arrows in T are unused
  open Presheaf TCat using () renaming (Psh to T ; _≈ₑ_ to _≈T_ ; _⨾ₛ_ to _⨾T_ ; _■ₑ_ to _■T_ ; _⁻¹ₑ to _⁻¹T ; assocₛ to assocT ; subst-map to subst-mapT)
  open PresheafHasΣ TyΣ
  open CodistributiveSemicomonad □Func

  module inner
    (QT : C) -- (Σ {𝟙} (* ⨾ₛ □ₚT))
    (□-map-QT : ∀ {a} → T a → (□ a [>] QT)) -- not quite sure how this fits with the above, but it captures that QT is □ (T 𝟙) and maps into QT are like maps into □ (T 𝟙) i.e., Wk a ~> T is like T a by substitution
    -- incomplete musing: we need an analogue of (□ₚT : Presheaf □C) and of `_⨾ₛ_ : (Σ R [>] □ (Σ P)) → (□ₚT (□ (Σ P))) → □ₚT (Σ R)`, and ...
    -- incomplete musing: `Wk.uncurry (Σ.ι/dup ⨾ fst)` gives `Π[ a ] 𝟙 [→] (* ⨾ₛ Wk a)`, `pair *` gives `(Π[ a ] (𝟙 [→] (* ⨾ₛ □ₚT))) → (𝟙 [>] Σ a □ₚT)`, `□ₚf : □ₚT (□ (Σ P))`, if we treat `f` as  analogue of □ₚ gives us T a → □T (□a),
    (□-map-QT-subst : ∀ {a b} {f : b [>] a} {g : T a} → (□-map f ⨾ □-map-QT g) ≈ □-map-QT (f ⨾T g))
    (□-map-QT-2map : ∀ {a} {f g : T a} → f ≈T g → □-map-QT f ≈ □-map-QT g)

    (S : C) -- Δ (T (Σ_□S R))
    (P : Ty QT)
    (R : Ty (□ S))

    -- TODO: we can eliminate this assumption by manually supplying R' ≔ Σ R quote-r, and then using wk-map cojoin to quote quote-r or something
    (quote-r : Π[ □ S ] R [→] (cojoin ⨾ₛ □ₚ R))

    --(ϕ : T (S × Σ R))
    (□-map-QT-ϕ : □ (S × Σ R) [>] QT)
    --(ψ : T (Σ R) → (𝟙 [>] S))
    (□-map-ψ : T (Σ R) → (□ 𝟙 [>] □ S))
    (f : T (Σ P))
    --(ϕ-eq : ∀ {f : T (Σ R)} {g : 𝟙 [>] Σ R} → ((dup {𝟙} ⨾ (ψ f ×× g)) ⨾T ϕ) ≈T (g ⨾T f))
    (□-map-ϕ-eq : ∀ {f : T (Σ R)} {g : 𝟙 [>] Σ R} → ((dup {□ 𝟙} ⨾ ((□-map-ψ f ×× □-map g) ⨾ □-×-codistr)) ⨾ □-map-QT-ϕ) ≈ □-map-QT (g ⨾T f))
    where

    {-
    □-map-QT-ϕ : □ (S × Σ R) [>] QT
    □-map-QT-ϕ = □-map-QT ϕ
    □-map-ψ : T (Σ R) → (□ 𝟙 [>] □ S)
    □-map-ψ f = □-map (ψ f)

    □-map-ϕ-eq : ∀ {f : T (Σ R)} {g : 𝟙 [>] Σ R} → ((dup {□ 𝟙} ⨾ ((□-map-ψ f ×× □-map g) ⨾ □-×-codistr)) ⨾ □-map-QT-ϕ) ≈ □-map-QT (g ⨾T f)
    □-map-ϕ-eq = ((eq1 ⨾-map 2id) ■ eq2)
      where
        eq5 = ϕ-eq
        eq4 = (□-⨾-map ⁻¹)
        eq3 = ((assoc ⁻¹) ■ (□-×-codistr-dup ⨾-map 2id)) ■ eq4
        eq2 = □-map-QT-subst ■ □-map-QT-2map eq5
        eq1 = (2id ⨾-map □-map-××-codistr) ■ eq3
    -}

    quote-R : Σ R [>] □ (Σ R)
    quote-R = (cojoin ΣΣ quote-r) ⨾ □-Σ-codistr

    pre-unwrap : Σ R [>] QT
    pre-unwrap = (dup ⨾ ((fst ×× quote-R) ⨾ □-×-codistr)) ⨾ □-map-QT-ϕ

    module inner
      (r2p : Π[ Σ R ] 𝟙ₚ [→] (pre-unwrap ⨾ₛ P))
      where

      unwrap : T (Σ R)
      unwrap = pair pre-unwrap r2p ⨾T f

      rewrap : □ 𝟙 [>] □ S
      rewrap = □-map-ψ unwrap

      module inner
        (r : Π[ 𝟙 ] 𝟙ₚ [→] ((□-𝟙-codistr ⨾ rewrap) ⨾ₛ R))
        -- TODO: figure out what's up with ((rid ⁻¹) ⨾-map 2id) (mirrors cojoinₚ)
        -- This isn't going to hold on-the-nose in general, so we only demand it for r
        --(quote-r-□-map : ∀ {s : 𝟙 [>] S} {r : Π[ 𝟙 ] 𝟙ₚ [→] ((□-𝟙-codistr ⨾ □-map s) ⨾ₛ R)} → (r ⨾ₚ quote-r) ≈ₚ[ □-map-cojoin ■ ((rid ⁻¹) ⨾-map 2id) ] ((*ₚ □-𝟙-codistr ⨾ₚ □-𝟙ₚ-codistr) ⨾ₚ □ₚ-map r))
        (quote-r-□-map : (r ⨾ₚ quote-r) ≈ₚ[ □-map-cojoin ■ ((rid ⁻¹) ⨾-map 2id) ] ((*ₚ □-𝟙-codistr ⨾ₚ □-𝟙ₚ-codistr) ⨾ₚ □ₚ-map r))
        where

        lawvere : T 𝟙
        lawvere = pair (□-𝟙-codistr ⨾ rewrap) r ⨾T unwrap


        -- this one is a bit easier to prove than alternative formulations
        quote-R-□-map-pair : let s = □-𝟙-codistr ⨾ rewrap in (pair s r ⨾ quote-R) ≈ (□-𝟙-codistr ⨾ □-map (pair s r))
        quote-R-□-map-pair =
          let eq13 = assoc ■ (assoc ■ (2id ⨾-map □-Σ-codistr-dup)) in
          let eq12 = (((assoc ⁻¹) ■ (dup-ΣΣ ⨾-map 2id)) ⨾-map 2id) ■ eq13 in
          let eq11 = (□-⨾-map ⁻¹) in
          let eq10 = assoc ■ (2id ⨾-map eq11) in
          let eq9 = assoc ■ ((2id ⨾-map (ΣΣ-natural ⨾-map 2id)) ■ ((assoc ⁻¹) ■ eq12)) in
          let eq8 = □-map-ΣΣ-codistr in
          let eq7 = (assoc ⁻¹) ■ ((assoc ⁻¹) ■ ((eq9 ⨾-map 2id) ■ eq10)) in
          let eq6 = assoc ■ (2id ⨾-map eq8) in
          let eq5 = (2id ⨾-map ΣΣ-natural) in
          let eq4 = (2id ⨾-map ((ΣΣ-natural ⁻¹) ■ ((□-map-cojoin ■ ((rid ⁻¹) ⨾-map 2id)) ΣΣ-2map quote-r-□-map))) ■ eq5 in
          let eq3 = (assoc ■ eq4) in
          let eq2 = assoc ■ ((2id ⨾-map eq6) ■ eq7) in
          let eq1 = (eq3 ⨾-map 2id) ■ eq2 in
          (assoc ⁻¹) ■ eq1

        module lawvere-fix-helper where
          eq : (pair (□-𝟙-codistr ⨾ rewrap) r ⨾ pre-unwrap) ≈ (□-𝟙-codistr ⨾ □-map-QT lawvere)
          eq = (2id ⨾-map 2id) ■ (((assoc ⁻¹) ■ ((eq2 ⨾-map 2id) ■ assoc)) ■ (2id ⨾-map □-map-ϕ-eq))
            module eq where
              eq7 = (assoc ⁻¹) ■ (dup-natural ⨾-map 2id)
              eq6 = (assoc ⁻¹) ■ ((eq7 ⨾-map 2id) ■ assoc)
              eq5 = (assoc ⁻¹) ■ (((××-natural ⁻¹) ■ ((pair-fst ××-2map quote-R-□-map-pair) ■ ××-natural)) ⨾-map 2id)
              eq4 = assoc ■ ((2id ⨾-map eq5) ■ eq6)
              eq3 = dup-natural ⁻¹
              eq2 = ((assoc ⁻¹) ■ ((eq3 ⨾-map 2id) ■ eq4)) ■ assoc

          eq' : ((pair (□-𝟙-codistr ⨾ rewrap) r ⨾ pair pre-unwrap r2p) ⨾ fst) ≈ (□-𝟙-codistr ⨾ □-map-QT lawvere)
          eq' = (2id ⨾-map 2id) ■ (assoc ■ ((2id ⨾-map pair-fst) ■ eq))

        Plawvere : Π[ 𝟙 ] 𝟙ₚ [→] ((□-𝟙-codistr ⨾ □-map-QT lawvere) ⨾ₛ P)
        Plawvere = subst-map-Π lawvere-fix-helper.eq (*ₚ (pair (□-𝟙-codistr ⨾ rewrap) r) ⨾ₚ r2p)

        module lawvere-fix-helperₚ where
          open lawvere-fix-helper
          eqₚ : (*ₚ (pair (□-𝟙-codistr ⨾ rewrap) r) ⨾ₚ r2p) ≈ₚ[ eq ] Plawvere
          eqₚ = subst-map-Π-eq

          eqₚ' : (*ₚ (pair (□-𝟙-codistr ⨾ rewrap) r ⨾ pair pre-unwrap r2p) ⨾ₚ snd) ≈ₚ[ eq' ] Plawvere
          eqₚ' = (*ₚ-law {q = *ₚ _ ⨾ₚ *ₚ _} ⨾-mapₚ 2idₚ) ■ₚ (assocₚ ■ₚ ((2idₚ ⨾-mapₚ pair-snd) ■ₚ eqₚ))


        lawvere-fix : lawvere ≈T (pair (□-𝟙-codistr ⨾ □-map-QT lawvere) Plawvere ⨾T f)
        lawvere-fix = eq0
          module lawvere-fix where
            eq0 = (assocT ⁻¹T) ■T subst-mapT ((pair-η ⁻¹) ■ pair-2map lawvere-fix-helper.eq' lawvere-fix-helperₚ.eqₚ')
      open inner public
    open inner hiding (module inner) public
  open inner hiding (module inner) public

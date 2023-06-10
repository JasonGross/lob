{-# OPTIONS --without-K #-}
module lawvere-factored-alt-from-query where
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc; Setω)
open import CC public
open import CCPresheaf public
open import CCLaxMonoidalSemicomonad public
import lawvere-query-with-properties-full-pointified as lawvere-query-with-properties-full

module generic
  {ℓ₀ ℓ₁ ℓ₂ ℓt₀ ℓt₁ ℓte₂ ℓt₂ ℓty₀ ℓty₁ ℓtye₂ ℓty₂}
  (CCat : CartesianCat {ℓ₀} {ℓ₁} {ℓ₂})
  (TyCat : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓty₀} {ℓty₁} {ℓtye₂} {ℓty₂} CCat)
  (TCat : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓt₀} {ℓt₁} {ℓte₂} {ℓt₂} CCat) -- like (_[>] X)
  (TyΣ : PresheafHasΣ TyCat)
  (□Func : LaxMonoidalSemicomonad CCat TyCat TyΣ)
  where

  open CartesianCat CCat renaming (Obj to C)
  -- open Presheaf hiding (Π_[→]_ ; Π[_]_[→]_ ; _≈ₑ_ ; _≈ₚ[_]_ ; _⨾ₚ_ ; _⨾ₛ_ ; _Π⨾ₑ_ ; _■ₑ_ ; _⁻¹ₑ ; 2idₑ)
  open Presheaf TyCat renaming (Psh to Ty)
  -- arrows in T are unused
  open Presheaf TCat using () renaming (Psh to T ; _≈ₑ_ to _≈T_ ; _⨾ₛ_ to _⨾T_ ; _■ₑ_ to _■T_ ; _⁻¹ₑ to _⁻¹T ; assocₛ to assocT ; subst-map to subst-mapT)
  open PresheafHasΣ TyΣ
  open LaxMonoidalSemicomonad □Func

  module lawvere-query-with-properties-full-0 = lawvere-query-with-properties-full CCat TyCat TCat TyΣ

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

    quote-R : Σ R [>] □ (Σ R)
    quote-R = (cojoin ΣΣ quote-r) ⨾ □-Σ-codistr

    encode : T 𝟙 → 𝟙 [>] QT
    encode f = □-𝟙-codistr ⨾ □-map-QT f

    pack : T (Σ R) → 𝟙 [>] □ S
    pack f = □-𝟙-codistr ⨾ □-map-ψ f

    query : ∀ {X} → X [>] Σ R → X [>] Σ R → X [>] QT
    query f g = (dup ⨾ (((f ⨾ fst) ×× (g ⨾ quote-R)) ⨾ □-×-codistr)) ⨾ □-map-QT-ϕ

    module lawvere-query-with-properties-full-1 = lawvere-query-with-properties-full-0.inner QT (□ S) P R encode pack query f

    pre-unwrap : Σ R [>] QT
    pre-unwrap = lawvere-query-with-properties-full-1.pre-a

    module inner
      (r2p : Π[ Σ R ] 𝟙ₚ [→] (pre-unwrap ⨾ₛ P))
      where

      module lawvere-query-with-properties-full-2 = lawvere-query-with-properties-full-1.inner r2p

      unwrap : T (Σ R)
      unwrap = lawvere-query-with-properties-full-2.a

      module inner
        (r : Π[ 𝟙 ] 𝟙ₚ [→] (pack unwrap ⨾ₛ R))
        -- TODO: figure out what's up with ((rid ⁻¹) ⨾-map 2id) (mirrors cojoinₚ)
        -- This isn't going to hold on-the-nose in general, so we only demand it for r
        --(quote-r-□-map : ∀ {s : 𝟙 [>] S} {r : Π[ 𝟙 ] 𝟙ₚ [→] ((□-𝟙-codistr ⨾ □-map s) ⨾ₛ R)} → (r ⨾ₚ quote-r) ≈ₚ[ □-map-cojoin ■ ((rid ⁻¹) ⨾-map 2id) ] ((*ₚ □-𝟙-codistr ⨾ₚ □-𝟙ₚ-codistr) ⨾ₚ □ₚ-map r))
        (quote-r-□-map : (r ⨾ₚ quote-r) ≈ₚ[ □-map-cojoin ■ ((rid ⁻¹) ⨾-map 2id) ] ((*ₚ □-𝟙-codistr ⨾ₚ □-𝟙ₚ-codistr) ⨾ₚ □ₚ-map r))
        where

        module lawvere-query-with-properties-full-3 = lawvere-query-with-properties-full-2.inner r

        lawvere : T 𝟙
        lawvere = lawvere-query-with-properties-full-3.lawvere

        s = lawvere-query-with-properties-full-3.packed-a

        query-pack-encode : ∀ {a} {pf : Π[ 𝟙 ] 𝟙ₚ [→] (pack a ⨾ₛ R)} → query {𝟙} (pair (pack a) pf) s ≈ encode (s ⨾T a)
        query-pack-encode = ((((((assoc ⁻¹) ■ (((((2id ⨾-map (pair-fst ××-2map 2id)) ■ ((2id ⨾-map (2id ××-2map helper)) ■ (2id ⨾-map ××-natural))) ■ (assoc ⁻¹)) ■ (dup-natural ⨾-map 2id)) ⨾-map 2id)) ■ assoc) ■ assoc) ⨾-map 2id) ■ assoc) ■ (2id ⨾-map □-map-ϕ-eq)
          where
            helper2 : _≈ₚ[_]_ {𝟙} {□ (□ S)} {𝟙ₚ} {□ₚ R} {(s ⨾ fst) ⨾ cojoin} {(□-𝟙-codistr ⨾ id) ⨾ □-map (s ⨾ fst)} ((*ₚ s ⨾ₚ snd) ⨾ₚ quote-r) (□-map-cojoin ■ ((rid ⁻¹) ⨾-map 2id)) ((*ₚ □-𝟙-codistr ⨾ₚ □-𝟙ₚ-codistr) ⨾ₚ □ₚ-map (*ₚ s ⨾ₚ snd))
            helper2 = {!quote-r-□-map!} -- need to fixup to reduce s followed by snd, fst

            helper : (s ⨾ quote-R) ≈ (□-𝟙-codistr ⨾ □-map s) -- (s ⨾ ((cojoin ΣΣ quote-r) ⨾ □-Σ-codistr)) ≈ (□-𝟙-codistr ⨾ □-map s)
            helper = ((((rid ⁻¹) ■ (2id ⨾-map (dup-fst-snd ⁻¹))) ⨾-map 2id) ■ (assoc ■ ((2id ⨾-map (assoc ■ (2id ⨾-map ((assoc ⁻¹) ■ ((ΣΣ-natural ⁻¹) ⨾-map 2id))))) ■ ((assoc ⁻¹) ■ (((dup-ΣΣ ⁻¹) ⨾-map 2id) ■ (assoc ■ ((2id ⨾-map ((assoc ⁻¹) ■ ((ΣΣ-natural ⁻¹) ⨾-map 2id))) ■ ((((((((2id ⨾-map ((((assoc ⁻¹) ■ (□-map-cojoin ■ ((rid ⁻¹) ⨾-map 2id))) ΣΣ-2map ((assocₚ ⁻¹ₚ) ■ₚ helper2)) ⨾-map 2id)) ■ (((2id ⨾-map (ΣΣ-natural ⨾-map 2id)) ■ ((2id ⨾-map (assoc ■ (2id ⨾-map □-map-ΣΣ-codistr))) ■ (((assoc ⁻¹) ■ (((assoc ⁻¹) ■ (((((((2id ⨾-map (2id ■ ΣΣ-natural)) ■ (assoc ⁻¹)) ■ (dup-ΣΣ ⨾-map 2id)) ⨾-map 2id) ■ assoc) ■ assoc) ⨾-map 2id)) ■ assoc)) ■ (2id ⨾-map ((□-Σ-codistr-dup ⨾-map 2id) ■ (□-⨾-map ⁻¹)))))) ■ (2id ⨾-map □-2map ((((2id ⨾-map ΣΣ-natural) ■ (assoc ⁻¹)) ■ (dup-ΣΣ ⨾-map 2id)) ■ assoc)))))))))))))))))
              ■ (2id ⨾-map (□-2map ((2id ⨾-map dup-fst-snd) ■ rid)))

        query-natural : ∀ {X Y} {m : Y [>] X} {f : X [>] Σ R} {g : X [>] Σ R} → (m ⨾ query {X} f g) ≈ query {Y} (m ⨾ f) (m ⨾ g)
        query-natural = (assoc ⁻¹) ■ (((assoc ⁻¹) ■ (((dup-natural ⁻¹) ⨾-map 2id) ■ (assoc ■ (2id ⨾-map ((assoc ⁻¹) ■ (((××-natural ⁻¹) ■ ((assoc ⁻¹) ××-2map (assoc ⁻¹))) ⨾-map 2id)))))) ⨾-map 2id)

        query-2map    : ∀ {X} {f f′ g g′} → f ≈ f′ → g ≈ g′ → query {X} f g ≈ query {X} f′ g′
        query-2map ff gg = (2id ⨾-map (((ff ⨾-map 2id) ××-2map (gg ⨾-map 2id)) ⨾-map 2id)) ⨾-map 2id
        module lawvere-query-with-properties-full-4 = lawvere-query-with-properties-full-3.inner query-pack-encode query-natural query-2map

        Plawvere : Π[ 𝟙 ] 𝟙ₚ [→] ((□-𝟙-codistr ⨾ □-map-QT lawvere) ⨾ₛ P)
        Plawvere = lawvere-query-with-properties-full-4.lawvere-pf

        lawvere-fix : lawvere ≈T (pair (□-𝟙-codistr ⨾ □-map-QT lawvere) Plawvere ⨾T f)
        lawvere-fix = lawvere-query-with-properties-full-4.eq

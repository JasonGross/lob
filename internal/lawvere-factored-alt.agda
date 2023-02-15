{-# OPTIONS --without-K --allow-unsolved-metas #-}
module lawvere-factored-alt where
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc; Setω)
open import CCC public

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

    Πid  : ∀ {a x} → Π[ a ] x [→] x
    -- _⨾ₚ_ : ∀ {a} {x y z : Psh a} → Π x [→] y → Π y [→] z → Π x [→] z

    _⨾ₛ_ : ∀ {a b} → (a [>] b) → Psh b → Psh a

    _≈ₚ[_]_ : ∀ {a b x y} {f : a [>] b} {g} → (Π[ a ] x [→] (f ⨾ₛ y)) → f ≈ g → (Π[ a ] x [→] (g ⨾ₛ y)) → Set ℓp₂
    -- _Π⨾ₛ_ : ∀ {a b x y} → (f : a [>] b) → Π[ b ] x [→] y → Π[ a ] (f ⨾ₛ x) [→] (f ⨾ₛ y)
    _⨾ₚ_ : ∀ {a b c x y z} → {f : a [>] b} {g : b [>] c} → Π[ a ] x [→] (f ⨾ₛ y) → Π[ b ] y [→] (g ⨾ₛ z) → Π[ a ] x [→] ((f ⨾ g) ⨾ₛ z)

    --_■ₚ_   : ∀ {a x y} {f g h : Π[ a ] x [→] b} → f ≈ₚ g → g ≈ₚ h → f ≈ₚ h
    --_⁻¹ₚ   : ∀ {a x y} {f g   : Π[ a ] x [→] b} → f ≈ₚ g → g ≈ₚ f
    --2idₚ   : ∀ {a x y} {f     : Π[ a ] x [→] b} → f ≈ₚ f
    --_⨾-mapₚ_

    --lidₚ   : ∀ {a x y} {f : Π[ a ] x [→] y} → (idₚ ⨾ₚ f) ≈ₚ f
    --ridₚ   : ∀ {a x y} {f : Π[ a ] x [→] y} → (f ⨾ₚ idₚ) ≈ₚ f
    --assocₚ : ∀ {a} {x y z w : Psh a} {f : Π x [→] y} {g : Π y [→] z} {h : Π z [→] w}
    --         → (f ⨾ₚ (g ⨾ₚ h)) ≈ₚ ((f ⨾ₚ g) ⨾ₚ h)

    -- TODO: interaction of ≈ₑ and ≈ₚ
    -- TODO: id Π⨾ₛ f = f
    -- TODO: f Π⨾ₛ Πid = Πid
    -- TODO: (f ⨾ g) Π⨾ₛ h = f Π⨾ₛ (g ⨾ₛ h)

    _■ₑ_   : ∀ {a} {x y z : Psh a} → x ≈ₑ y → y ≈ₑ z → x ≈ₑ z
    _⁻¹ₑ   : ∀ {a} {x y : Psh a} → x ≈ₑ y → y ≈ₑ x
    2idₑ   : ∀ {a} {x : Psh a} → x ≈ₑ x

    subst-id  : ∀ {a} {x : Psh a} → (id ⨾ₛ x) ≈ₑ x
    assocₛ    : ∀ {a b c} {f : a [>] b} {g : b [>] c} {x : Psh c} → ((f ⨾ g) ⨾ₛ x) ≈ₑ (f ⨾ₛ (g ⨾ₛ x))
    subst-map : ∀ {a b} {f g : a [>] b} {x : Psh b} → f ≈ g → (f ⨾ₛ x) ≈ₑ (g ⨾ₛ x)

    _Π⨾ₑ_ : ∀ {a} {x y x' y' : Psh a} → x' ≈ₑ x → y ≈ₑ y' → (Π[ a ] x [→] y) → (Π[ a ] x' [→] y')

record PresheafHasΣ {ℓ₀ ℓ₁ ℓ₂ ℓp₀ ℓp₁ ℓe₂ ℓp₂} {C : CartesianClosedCat {ℓ₀} {ℓ₁} {ℓ₂}}
                    (T : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓp₀} {ℓp₁} {ℓe₂} {ℓp₂} C)
                    : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓp₀ ⊔ ℓp₁ ⊔ ℓe₂ ⊔ ℓp₂) where
  open CartesianClosedCat C
  open Presheaf T
  field
    Wk     : Obj → Psh 𝟙 -- weakening over the terminal context
    Wk-map : ∀ {a b} → a [>] b → Π (Wk a) [→] (Wk b)
    -- TODO: id and ⨾ laws targeting ≈ₚ

  𝟙ₚ : ∀ {a} → Psh a
  𝟙ₚ = * ⨾ₛ Wk 𝟙
  *ₚ : ∀ {a b} (f : a [>] b) → Π[ a ] 𝟙ₚ [→] (f ⨾ₛ 𝟙ₚ)
  *ₚ f = (2idₑ Π⨾ₑ (subst-map *-law ■ₑ assocₛ)) Πid

  field
    Σ : ∀ {a : Obj} → Psh a → Obj

    dupΣ : ∀ {a} → a [>] Σ {a} 𝟙ₚ
    _ΣΣ_ : ∀ {a b x y} → (f : a [>] b) → (Π[ a ] x [→] (f ⨾ₛ y)) → (Σ {a} x [>] Σ {b} y)
    fst  : ∀ {a x} → Σ {a} x [>] a
    snd  : ∀ {a x} → Π[ Σ {a} x ] 𝟙ₚ [→] (fst ⨾ₛ x)

    -- Σ-map-id : ∀ {a x} → (id ΣΣ Πid) ≈ id {Σ {a} x} -- needs x = (id ⨾ₛ x)
    dup-fst : ∀ {a} → (dupΣ {a} ⨾ fst) ≈ id
    dup-snd : ∀ {a x} → (dupΣ {Σ {a} x} ⨾ (fst ΣΣ snd)) ≈ id
    ΣΣ-natural : ∀ {a b c x y z} {f : a [>] b} {g : b [>] c} {F : Π[ a ] x [→] (f ⨾ₛ y)} {G : Π[ b ] y [→] (g ⨾ₛ z)}
                 → ((f ⨾ g) ΣΣ (F ⨾ₚ G)) ≈ ((f ΣΣ F) ⨾ (g ΣΣ G))
    dup-ΣΣ : ∀ {a b} {f : a [>] b} → (dupΣ ⨾ (f ΣΣ *ₚ f)) ≈ (f ⨾ dupΣ)
    _ΣΣ-2map_ : ∀ {a b x y} {f f′ : a [>] b} {g : Π[ a ] x [→] (f ⨾ₛ y)} {g′ : Π[ a ] x [→] (f′ ⨾ₛ y)}
      → (e : f ≈ f′) → g ≈ₚ[ e ] g′ → (f ΣΣ g) ≈ (f′ ΣΣ g′)

    pair : ∀ {a b y} → (f : a [>] b) → (Π[ a ] 𝟙ₚ [→] (f ⨾ₛ y)) → (a [>] Σ {b} y) -- duplicative
    pair-fst : ∀ {a b y f g} → (pair {a} {b} {y} f g ⨾ fst) ≈ f
    -- pair-snd : ∀ {a b y f g} → (pair {a} {b} {y} f g ⨾ₛ snd) ≈ₚ g
    pair-η   : ∀ {a b y} {f : a [>] Σ {b} y} → (pair (f ⨾ fst) (*ₚ f ⨾ₚ snd)) ≈ f
    pair-2map : ∀ {a b y f f' g g'} → (e : f ≈ f') → g ≈ₚ[ e ] g' → pair {a} {b} {y} f g ≈ pair {a} {b} {y} f' g'

    -- should be derivable...
    pair-dup : ∀ {a b y f g} → pair {a} {b} {y} f g ≈ (dupΣ ⨾ (f ΣΣ g))
    -- pair-dup = pair-2map ({!? ■ (2id ⨾-map  !} ■ (assoc ⁻¹)) {!!} ■ pair-η


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

    --dupΣ-□-𝟙-ΣΣ-codistr : (dupΣ {𝟙} ⨾ (□-𝟙-codistr ΣΣ □ₚ-𝟙-codistr)) ≈ (□-𝟙-codistr ⨾ (dupΣ ⨾ (id ΣΣ {!!})))


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

    (S : C) -- Δ (T (Σ_□S R))
    (P : Ty QT)
    (R : Ty (□ S))

    -- TODO: we can eliminate this assumption by manually supplying R' ≔ Σ R quote-r, and then using wk-map cojoin to quote quote-r or something
    (quote-r : Π[ □ S ] R [→] (cojoin ⨾ₛ □ₚ R))
    (quote-r-□-map : ∀ {s : 𝟙 [>] S} {r : Π[ 𝟙 ] 𝟙ₚ [→] ((□-𝟙-codistr ⨾ □-map s) ⨾ₛ R)} → (r ⨾ₚ quote-r) ≈ₚ[ □-map-cojoin ] (□ₚ-𝟙-codistr ⨾ₚ □ₚ-map r))

    (ϕ : T (S × Σ R))
    (ψ : T (Σ R) → (𝟙 [>] S))
    (f : T (Σ P))
    where

    quote-R : Σ R [>] □ (Σ R)
    quote-R = (cojoin ΣΣ quote-r) ⨾ □-Σ-codistr

    pre-unwrap : Σ R [>] QT
    pre-unwrap = (dup ⨾ (fst ×× quote-R)) ⨾ (□-×-codistr ⨾ □-map-QT ϕ)

    module inner
      (r2p : Π[ Σ R ] 𝟙ₚ [→] (pre-unwrap ⨾ₛ P))
      where

      unwrap : T (Σ R)
      unwrap = pair pre-unwrap r2p ⨾T f

      rewrap : 𝟙 [>] S
      rewrap = ψ unwrap

      module inner
        (r : Π[ 𝟙 ] 𝟙ₚ [→] ((□-𝟙-codistr ⨾ □-map rewrap) ⨾ₛ R))
        where

        lawvere : T 𝟙
        lawvere = pair (□-𝟙-codistr ⨾ □-map rewrap) r ⨾T unwrap


        -- this one is a bit easier to prove
        quote-R-□-map-pair : ∀ {f : 𝟙 [>] S} → let s = □-𝟙-codistr ⨾ □-map f in ∀ {r : Π 𝟙ₚ [→] (s ⨾ₛ R)} → (pair s r ⨾ quote-R) ≈ ((□-𝟙-codistr ⨾ pair (□-map s) {!!}) ⨾ □-Σ-codistr) -- □-map (pair (□-𝟙-codistr ⨾ □-map f) r))
        quote-R-□-map-pair = (assoc ⁻¹) ■ ((((pair-dup ⨾-map 2id) ■ (assoc ■ ((2id ⨾-map ((ΣΣ-natural ⁻¹) ■ (□-map-cojoin ΣΣ-2map quote-r-□-map))) ■ ((2id ⨾-map ΣΣ-natural) ■ ((assoc ⁻¹) ■ (({!!} ⨾-map 2id) ■ {!!})) )))) ⨾-map 2id) ■ {!!})
{-
        {-quote-R-□-map : ∀ {f : 𝟙 [>] Σ R} → (f ⨾ quote-R) ≈ (□-𝟙-codistr ⨾ □-map f)
        quote-R-□-map-pair = quote-R-□-map ■ {!!}-}

        Plawvere : Π[ 𝟙 ] 𝟙ₚ [→] ((□-𝟙-codistr ⨾ □-map-QT lawvere) ⨾ₛ P)
        Plawvere = {!? ⨾ₚ snd!}

        lawvere-fix : lawvere ≈T (pair (□-𝟙-codistr ⨾ □-map-QT lawvere) Plawvere ⨾T f)
        lawvere-fix = eq0
          module lawvere-fix where
            eq8 = {!!}
            eq7 = (××-natural ⁻¹) ■ ((pair-fst ××-2map {!!}) ■ {!!})
            eq6 = assoc ■ ((2id ⨾-map eq7) ■ eq8)
            eq5 = dup-natural ⁻¹
            eq4 = {!!}
            eq3 = (assoc ⁻¹) ■ ((eq5 ⨾-map 2id) ■ eq6)
            eq2 = (assoc ⁻¹) ■ ((eq3 ⨾-map 2id) ■ eq4)
            eq1 = assoc ■ ((2id ⨾-map pair-fst) ■ eq2)
            eq0 = (assocT ⁻¹T) ■T subst-mapT ((pair-η ⁻¹) ■ pair-2map eq1 {!!})
      open inner public
    open inner hiding (module inner) public
  open inner hiding (module inner) public
  -- TODO: P lawvere
  -- TODO: fixpoint equation
-}

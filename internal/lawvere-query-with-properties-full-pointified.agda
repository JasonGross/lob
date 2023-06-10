{-# OPTIONS --without-K #-}
open import CC
open import CCPresheaf
--open import CCLaxMonoidalSemicomonad
module lawvere-query-with-properties-full-pointified
  {ℓ₀ ℓ₁ ℓ₂ ℓt₀ ℓt₁ ℓte₂ ℓt₂ ℓty₀ ℓty₁ ℓtye₂ ℓty₂}
  (CCat : CartesianCat {ℓ₀} {ℓ₁} {ℓ₂})
  (TyCat : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓty₀} {ℓty₁} {ℓtye₂} {ℓty₂} CCat)
  (ACat : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓt₀} {ℓt₁} {ℓte₂} {ℓt₂} CCat) -- like (_[>] X)
  (TyΣ : PresheafHasΣ TyCat)
  -- (□Func : LaxMonoidalSemicomonad CCat TyCat TyΣ)
  where

  open CartesianCat CCat renaming (Obj to C ; id to ι)
  -- open Presheaf hiding (Π_[→]_ ; Π[_]_[→]_ ; _≈ₑ_ ; _≈ₚ[_]_ ; _⨾ₚ_ ; _⨾ₛ_ ; _Π⨾ₑ_ ; _■ₑ_ ; _⁻¹ₑ ; 2idₑ)
  open Presheaf TyCat renaming (Psh to Ty)
  -- arrows in T are unused
  open Presheaf ACat using () renaming (Psh to A ; _≈ₑ_ to _≈A_ ; _⨾ₛ_ to _»_ ; subst-map to »-2map ; _■ₑ_ to _■A_ ; _⁻¹ₑ to _⁻¹A ; assocₛ⁻¹ to assocA )
  open PresheafHasΣ TyΣ
--  open LaxMonoidalSemicomonad □Func

  module inner
    (R : C) (S : C)
    (Pᵣ : Ty R) (Pₛ : Ty S)
    (encode : A 𝟙 → (𝟙 [>] R))
    (pack : A (Σ Pₛ) → (𝟙 [>] S))
    (query : ∀ {X} → (X [>] Σ Pₛ) → (X [>] Σ Pₛ) → (X [>] R))
    (f : A (Σ Pᵣ))
    where

    pre-a : Σ Pₛ [>] R
    pre-a = query {Σ Pₛ} ι ι

    module inner
      (s2p : Π[ Σ Pₛ ] 𝟙ₚ [→] (pre-a ⨾ₛ Pᵣ))
      where

      a : A (Σ Pₛ)
      a = pair pre-a s2p » f

      module inner
        (sa : Π[ 𝟙 ] 𝟙ₚ [→] (pack a ⨾ₛ Pₛ))
        where

        packed-a : 𝟙 [>] Σ Pₛ
        packed-a = pair (pack a) sa

        lawvere : A 𝟙
        lawvere = packed-a » a

        module inner
          (query-pack-encode : query {𝟙} packed-a packed-a ≈ encode (packed-a » a))
          (query-natural : ∀ {X Y} {m : Y [>] X} {f : X [>] Σ Pₛ} {g : X [>] Σ Pₛ} → (m ⨾ query {X} f g) ≈ query {Y} (m ⨾ f) (m ⨾ g))
          (query-2map    : ∀ {X} {f f′ g g′} → f ≈ f′ → g ≈ g′ → query {X} f g ≈ query {X} f′ g′)
          where

          module helper where

            eq1 : (packed-a ⨾ pre-a) ≈ encode lawvere
            eq1 = query-natural ■ (query-2map rid rid ■ query-pack-encode)

          open helper

          lawvere-pf : Π[ 𝟙 ] 𝟙ₚ [→] (encode lawvere ⨾ₛ Pᵣ)
          lawvere-pf = subst-map-Π eq1 (*ₚ packed-a ⨾ₚ s2p)

          eq : lawvere ≈A (pair (encode lawvere) lawvere-pf » f)
          eq = assocA ■A »-2map (pair-natural ■ (2id ⨾-map (eq1 ΣΣ-2map subst-map-Π-eq)))

        open inner public
      open inner public hiding (module inner)
    open inner public hiding (module inner)
  open inner public hiding (module inner)

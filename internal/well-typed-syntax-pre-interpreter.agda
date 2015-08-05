{-# OPTIONS --without-K #-}
module well-typed-syntax-pre-interpreter where
open import common public
open import well-typed-syntax
open import well-typed-syntax-helpers

max-level : Level
max-level = lsuc lzero

module inner
  (context-pick-if' : ∀ ℓ (P : Context → Set ℓ)
                          (Γ : Context)
                          (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
                          (val : P Γ) →
                        P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
  (context-pick-if-refl' : ∀ ℓ P dummy val →
                            context-pick-if' ℓ P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’) dummy val ≡ val)
  where

  context-pick-if : ∀ {ℓ} {P : Context → Set ℓ}
                          {Γ : Context}
                          (dummy : P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’))
                          (val : P Γ) →
                        P (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
  context-pick-if {P = P} dummy val = context-pick-if' _ P _ dummy val
  context-pick-if-refl : ∀ {ℓ P dummy val} →
                            context-pick-if {ℓ} {P} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} dummy val ≡ val
  context-pick-if-refl {P = P} = context-pick-if-refl' _ P _ _

  mutual
    Context⇓ : (Γ : Context) → Set (lsuc max-level)
    Typ⇓ : {Γ : Context} → Typ Γ → Context⇓ Γ → Set max-level

    Context⇓ ε = ⊤
    Context⇓ (Γ ▻ T) = Σ (λ (Γ' : Context⇓ Γ) → Typ⇓ T Γ')

    Typ⇓ (T₁ ‘’ x) Γ⇓ = Typ⇓ T₁ (Γ⇓ , Term⇓ x Γ⇓)
    Typ⇓ (T₂ ‘’₁ a) (Γ⇓ , A⇓) = Typ⇓ T₂ ((Γ⇓ , Term⇓ a Γ⇓) , A⇓)
    Typ⇓ (T₃ ‘’₂ a) ((Γ⇓ , A⇓) , B⇓) = Typ⇓ T₃ (((Γ⇓ , Term⇓ a Γ⇓) , A⇓) , B⇓)
    Typ⇓ (T₃ ‘’₃ a) (((Γ⇓ , A⇓) , B⇓) , C⇓) = Typ⇓ T₃ ((((Γ⇓ , Term⇓ a Γ⇓) , A⇓) , B⇓) , C⇓)
    Typ⇓ (W T₁) (Γ⇓ , _) = Typ⇓ T₁ Γ⇓
    Typ⇓ (W1 T₂) ((Γ⇓ , A⇓) , B⇓) = Typ⇓ T₂ (Γ⇓ , B⇓)
    Typ⇓ (W2 T₃) (((Γ⇓ , A⇓) , B⇓) , C⇓) = Typ⇓ T₃ ((Γ⇓ , B⇓) , C⇓)
    Typ⇓ (T ‘→’ T₁) Γ⇓ = (T⇓ : Typ⇓ T Γ⇓) → Typ⇓ T₁ (Γ⇓ , T⇓)
    Typ⇓ ‘Context’ Γ⇓ = Lifted Context
    Typ⇓ ‘Typ’ (Γ⇓ , T⇓) = Lifted (Typ (lower T⇓))
    Typ⇓ ‘Term’ (Γ⇓ , T⇓ , t⇓) = Lifted (Term (lower t⇓))
    Typ⇓ (‘Σ’ T T₁) Γ⇓ = Σ (λ T⇓ → Typ⇓ T₁ (Γ⇓ , T⇓))

    Term⇓ : ∀ {Γ : Context} {T : Typ Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Typ⇓ T Γ⇓
    Term⇓ (w t) (Γ⇓ , A⇓) = Term⇓ t Γ⇓
    Term⇓ (‘λ∙’ t) Γ⇓ T⇓ = Term⇓ t (Γ⇓ , T⇓)
    Term⇓ (t ‘’ₐ t₁) Γ⇓ = Term⇓ t Γ⇓ (Term⇓ t₁ Γ⇓)
    Term⇓ ‘VAR₀’ (Γ⇓ , A⇓) = A⇓
    Term⇓ (⌜ Γ ⌝c) Γ⇓ = lift Γ
    Term⇓ (⌜ T ⌝T) Γ⇓ = lift T
    Term⇓ (⌜ t ⌝t) Γ⇓ = lift t
    Term⇓ ‘quote-term’ Γ⇓ (lift T⇓) = lift ⌜ T⇓ ⌝t
    Term⇓ ‘quote-sigma’ Γ⇓ (lift Γ , lift T) = lift (S₁₀WW (S∀ (‘existT'’ ‘’ₐ ⌜ Γ ⌝c) ‘’ₐ ⌜ T ⌝T))
    Term⇓ ‘substTyp’ Γ⇓ (lift f) (lift x) = lift (f ‘’ x)
    --Term⇓ ‘tProd-nd’ (_ , _ , A⇓ , B⇓) = lift (lower A⇓ ‘→’ W (lower B⇓))
    Term⇓ ‘context-pick-if'’ Γ⇓ (lift dummy) (lift Γ') (lift val) = lift (context-pick-if {P = Typ} {Γ'} dummy val)
    Term⇓ (substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp-substTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
    Term⇓ (substTyp-weakenTyp1-VAR₀ t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
    Term⇓ (weakenTyp-tProd-inv t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
    Term⇓ (weakenTyp-weakenTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
    Term⇓ (substTyp1-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
    Term⇓ (weakenTyp1-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
    Term⇓ (substTyp2-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
    Term⇓ (substTyp1-substTyp-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (substTyp2-substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
    Term⇓ (weakenTyp2-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp1-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp1-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp1-weakenTyp1-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (substTyp1-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp1-substTyp-weakenTyp1-inv t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp1-substTyp-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp-substTyp-substTyp-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp-substTyp-substTyp-weakenTyp1-inv t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (substTyp-weakenTyp1-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (substTyp3-substTyp2-substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (substTyp1-substTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
    Term⇓ (substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (substTyp1-substTyp-weakenTyp2-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (weakenTyp-weakenTyp1-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ (beta-under-subst t) Γ⇓ = Term⇓ t Γ⇓
    Term⇓ ‘proj₁'’ Γ⇓ (x , p) = x
    Term⇓ ‘proj₂'’ (Γ⇓ , (x , p)) = p
    Term⇓ ‘existT'’ Γ⇓ x p = x , p
    Term⇓ (f ‘‘’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ lower (Term⇓ x Γ⇓))
    Term⇓ (f w‘‘’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ lower (Term⇓ x Γ⇓))
    Term⇓ (f ‘‘→'’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘→'’ lower (Term⇓ x Γ⇓))
    Term⇓ (f w‘‘→'’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘→'’ lower (Term⇓ x Γ⇓))

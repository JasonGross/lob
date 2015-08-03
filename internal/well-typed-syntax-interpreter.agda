{-# OPTIONS --without-K #-}
module well-typed-syntax-interpreter where
open import common public
open import well-typed-syntax
open import well-typed-syntax-helpers
open import well-typed-syntax-context-pre-helpers

max-level : Level
max-level = lsuc lzero

{-mutual
  Context-max-level : Context → Level
  Typ-max-level : {Γ : Context} → Typ Γ → Level
  Term-max-level : {Γ : Context} → {T : Typ Γ} → Term T → Level

  Context-max-level ε₀ = lzero
  Context-max-level (Γ ▻ x) = {!!}
  Typ-max-level T = {!!}
  Term-max-level t = {!!}-}

mutual
  Context⇓ : (Γ : Context) → Set (lsuc max-level)
  Typ⇓ : {Γ : Context} → Typ Γ → Context⇓ Γ → Set max-level
  Context⇓-helper₀ : (Γ : Context) → (Γ' : Context⇓ Γ) → (T₁ : Typ Γ) → Typ⇓ T₁ Γ' → Context⇓ (Γ ▻ T₁)

  Context⇓ ε₀ = ⊤
  Context⇓ (Γ ▻ T) = Σ (λ (Γ' : Context⇓ Γ) → Typ⇓ T Γ')

  Context⇓-helper₀ Γ Γ⇓ T₁ T₁⇓ = Γ⇓ , T₁⇓

  Typ⇓ (T₁ ‘’ x) Γ⇓ = Typ⇓ T₁ (Γ⇓ , Term⇓ x Γ⇓)
  Typ⇓ (T₂ ‘’₁ a) (Γ⇓ , A⇓) = Typ⇓ T₂ ((Γ⇓ , Term⇓ a Γ⇓) , A⇓)
  Typ⇓ (T₃ ‘’₂ a) ((Γ⇓ , A⇓) , B⇓) = Typ⇓ T₃ (((Γ⇓ , Term⇓ a Γ⇓) , A⇓) , B⇓)
  Typ⇓ (T₃ ‘’₃ a) (((Γ⇓ , A⇓) , B⇓) , C⇓) = Typ⇓ T₃ ((((Γ⇓ , Term⇓ a Γ⇓) , A⇓) , B⇓) , C⇓)
  Typ⇓ (W T₁) (Γ⇓ , _) = Typ⇓ T₁ Γ⇓
  Typ⇓ (W1 T₂) ((Γ⇓ , A⇓) , B⇓) = Typ⇓ T₂ (Γ⇓ , B⇓)
  Typ⇓ (W2 T₃) (((Γ⇓ , A⇓) , B⇓) , C⇓) = Typ⇓ T₃ ((Γ⇓ , B⇓) , C⇓)
  Typ⇓ (T ‘→’ T₁) Γ⇓ = (T⇓ : Typ⇓ T Γ⇓) → Typ⇓ T₁ (Γ⇓ , T⇓)
  Typ⇓ ‘Set’ Γ⇓ = Set
  Typ⇓ ‘Context’ Γ⇓ = Lifted Context
  Typ⇓ ‘Typ’ (Γ⇓ , lift Γ) = Lifted (Typ Γ)
  Typ⇓ ‘Term’ (Γ⇓ , lift Γ , lift T) = Lifted (Term T)
  Typ⇓ (El T) Γ⇓ = Lifted (Term⇓ T Γ⇓)
  --Typ⇓ (WT₂ T₂) (Γ⇓ , A⇓) = Typ⇓ T₂ ((Γ⇓ , {!!}) , {!!}) -- (((Γ⇓ , A⇓) , B⇓) , C⇓ ) = Typ⇓ T₂ ((Γ⇓ , B⇓) , (C⇓))
  Typ⇓ (‘Σ'’ T T₁) Γ⇓ = Σ (λ T⇓ → Typ⇓ T₁ (Γ⇓ , T⇓))

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
  Term⇓ ‘tProd-nd’ (Γ⇓ , lift Γ , lift A , lift B) = lift (A ‘→’ W B)
  Term⇓ ‘context-pick-if'’ Γ⇓ (lift Γ) (lift dummy) (lift Γ') (lift val) = lift (context-pick-if-gen {P = Typ} {Γ} {Γ'} dummy val)
  Term⇓ (WSet T) Γ⇓ = Term⇓ T Γ⇓
  Term⇓ (WWSet T) Γ⇓ = Term⇓ T Γ⇓
  Term⇓ (WWWSet T) Γ⇓ = Term⇓ T Γ⇓
  Term⇓ (substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp-weakenTyp-substTyp-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp-substTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (substTyp-weakenTyp1-VAR₀ t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (weakenTyp-tProd-inv t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (weakenTyp-weakenTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (substTyp1-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (weakenTyp-substTyp1-tProd-nd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (weakenTyp1-substTyp1-tProd-nd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (weakenTyp1-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (weakenTyp1-tProd-inv t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (weakenTyp2-tProd-nd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (substTyp-tProd-nd-weakenTyp-tProd-weakenTyp1-tProd-nd-weakenTyp t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (weakenTyp-weakenTyp2-tProd-nd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (weakenTyp-weakenTyp-weakenTyp2-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (substTyp2-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (substTyp1-substTyp-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (substTyp2-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (substTyp2-substTyp1-substTyp-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-tProd t) Γ⇓ T⇓ = Term⇓ t Γ⇓ T⇓
  Term⇓ (weakenTyp2-weakenTyp1 t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp2-weakenTyp1-inv t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp-weakenTyp2-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (weakenTyp-weakenTyp2-weakenTyp-inv t) Γ⇓ = Term⇓ t Γ⇓
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
  Term⇓ (weakenTyp-tProd-tProd-tProd-nd-weakenTyp-tProd-weakenTyp1-tProd-nd-weakenTyp t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (beta-under-subst t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ (beta-under-subst-inv t) Γ⇓ = Term⇓ t Γ⇓
  Term⇓ ‘proj₁'’ Γ⇓ (x , p) = x
  Term⇓ ‘proj₂'’ (Γ⇓ , (x , p)) = p
  Term⇓ ‘existT'’ Γ⇓ x p = x , p

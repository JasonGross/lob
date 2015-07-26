module well-typed-syntax-interpreter where
open import common public
open import well-typed-syntax

max-level : Level
max-level = lzero

mutual
  Context⇓ : Context → Set max-level
  Context⇓ ε₀ = ⊤
  Context⇓ (Γ ▻Typ Γ₁) = Σ (λ (Γ' : Context⇓ Γ) → {!!})
  Context⇓ (Γ ▻ T) = Σ (λ (Γ' : Context⇓ Γ) → Typ⇓ T Γ')

  Typ⇓ : {Γ : Context} → Typ Γ → Context⇓ Γ → Set max-level
  Typ⇓ (T₁ ‘’ x) Γ⇓ = Typ⇓ T₁ (Γ⇓ , Term⇓ x Γ⇓)
  Typ⇓ (T₂ ‘’₁ a) (Γ⇓ , A⇓) = Typ⇓ T₂ ((Γ⇓ , Term⇓ a Γ⇓) , A⇓)
  Typ⇓ (T₃ ‘’₂ a) ((Γ⇓ , A⇓) , B⇓) = Typ⇓ T₃ (((Γ⇓ , Term⇓ a Γ⇓) , A⇓) , B⇓)
  Typ⇓ (T₃ ‘’₃ a) (((Γ⇓ , A⇓) , B⇓) , C⇓) = Typ⇓ T₃ ((((Γ⇓ , Term⇓ a Γ⇓) , A⇓) , B⇓) , C⇓)
  Typ⇓ (W T₁) (Γ⇓ , _) = Typ⇓ T₁ Γ⇓
  Typ⇓ (W1 T₂) ((Γ⇓ , A⇓) , B⇓) = Typ⇓ T₂ (Γ⇓ , B⇓)
  Typ⇓ (W2 T₃) (((Γ⇓ , A⇓) , B⇓) , C⇓) = Typ⇓ T₃ ((Γ⇓ , B⇓) , C⇓)
  Typ⇓ (T ‘→’ T₁) Γ⇓ = (T⇓ : Typ⇓ T Γ⇓) → Typ⇓ T₁ (Γ⇓ , T⇓)
  Typ⇓ (WT T) (Γ⇓ , A⇓) = Typ⇓ T Γ⇓
  Typ⇓ (WT₁ T₁) ((Γ⇓ , A⇓) , B⇓) = Typ⇓ T₁ (Γ⇓ , B⇓)
  Typ⇓ (WT₂ T₂) (((Γ⇓ , A⇓) , B⇓) , C⇓ ) = Typ⇓ T₂ ((Γ⇓ , B⇓) , (C⇓))
  Typ⇓ ‘TVAR₀₀’ (Γ⇓ , A⇓) = {!!}
  Typ⇓ ‘TVAR₀₁’ ((Γ⇓ , A⇓) , B⇓) = {!!}
  Typ⇓ ‘TVAR₀₂’ (((Γ⇓ , A⇓) , B⇓) , C⇓) = {!!}
  Typ⇓ (‘Σ'’ T T₁) Γ⇓ = Σ (λ T⇓ → Typ⇓ T₁ (Γ⇓ , T⇓))


  Term⇓ : ∀ {Γ : Context} {T : Typ Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Typ⇓ T Γ⇓
  Term⇓ (w t) (Γ⇓ , A⇓) = Term⇓ t Γ⇓
  Term⇓ (‘λ∙’ t) Γ⇓ T⇓ = Term⇓ t (Γ⇓ , T⇓)
  Term⇓ (t ‘’ₐ t₁) Γ⇓ = Term⇓ t Γ⇓ (Term⇓ t₁ Γ⇓)
  Term⇓ ‘VAR₀’ (Γ⇓ , A⇓) = A⇓
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
  Term⇓ ‘proj₁'’ Γ⇓ (x , p) = x
  Term⇓ ‘proj₂'’ (Γ⇓ , (x , p)) = p
  Term⇓ (‘existT'’ t t₁) Γ⇓ = (Term⇓ t Γ⇓) , (Term⇓ t₁ Γ⇓)

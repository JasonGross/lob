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

  private
    dummy : Typ ε
    dummy = ‘Context’

  cast-helper : ∀ {X T A} {x : Term X} → A ≡ T → Term {ε} (T ‘’ x ‘→'’ A ‘’ x)
  cast-helper refl = ‘λ∙’ ‘VAR₀’

  cast'-proof : ∀ {T} → Term {ε} (context-pick-if {P = Typ} (W dummy) T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T
                ‘→'’ T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T)
  cast'-proof {T} = cast-helper {‘Σ’ ‘Context’ ‘Typ’}
                      {context-pick-if {P = Typ} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} (W dummy) T}
                      {T} (sym (context-pick-if-refl {P = Typ} {dummy = W dummy}))

  cast-proof : ∀ {T} → Term {ε} (T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T
                ‘→'’ context-pick-if {P = Typ} (W dummy) T ‘’ ‘existT’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c ⌜ T ⌝T)
  cast-proof {T} = cast-helper {‘Σ’ ‘Context’ ‘Typ’} {T}
                      {context-pick-if {P = Typ} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} (W dummy) T}
                      (context-pick-if-refl {P = Typ} {dummy = W dummy})

  ‘idfun’ : ∀ {T} → Term {ε} (T ‘→'’ T)
  ‘idfun’ = ‘λ∙’ ‘VAR₀’

  mutual
    Context⇓ : (Γ : Context) → Set (lsuc max-level)
    Typ⇓ : {Γ : Context} → Typ Γ → Context⇓ Γ → Set max-level

    Context⇓ ε = ⊤
    Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (λ Γ' → Typ⇓ T Γ')

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
    Typ⇓ (‘Σ’ T T₁) Γ⇓ = Σ (Typ⇓ T Γ⇓) (λ T⇓ → Typ⇓ T₁ (Γ⇓ , T⇓))

    Term⇓ : ∀ {Γ : Context} {T : Typ Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Typ⇓ T Γ⇓
    Term⇓ (w t) (Γ⇓ , A⇓) = Term⇓ t Γ⇓
    Term⇓ (‘λ∙’ t) Γ⇓ T⇓ = Term⇓ t (Γ⇓ , T⇓)
    Term⇓ (t ‘’ₐ t₁) Γ⇓ = Term⇓ t Γ⇓ (Term⇓ t₁ Γ⇓)
    Term⇓ ‘VAR₀’ (Γ⇓ , A⇓) = A⇓
    Term⇓ (⌜ Γ ⌝c) Γ⇓ = lift Γ
    Term⇓ (⌜ T ⌝T) Γ⇓ = lift T
    Term⇓ (⌜ t ⌝t) Γ⇓ = lift t
    Term⇓ ‘quote-term’ Γ⇓ (lift T⇓) = lift ⌜ T⇓ ⌝t
    Term⇓ (‘quote-sigma’ {Γ₀} {Γ₁}) Γ⇓ (lift Γ , lift T) = lift (‘existT’ {Γ₁} ⌜ Γ ⌝c ⌜ T ⌝T)
    Term⇓ ‘cast’ Γ⇓ T⇓ = lift (context-pick-if
                              {P = Typ}
                              {lower (Σ.proj₁ T⇓)}
                              (W dummy)
                              (lower (Σ.proj₂ T⇓)))
    Term⇓ (SW t) Γ⇓ = Term⇓ t Γ⇓
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
    Term⇓ (‘existT’ x p) Γ⇓ = Term⇓ x Γ⇓ , Term⇓ p Γ⇓
    Term⇓ (f ‘‘’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ lower (Term⇓ x Γ⇓))
    Term⇓ (f w‘‘’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ lower (Term⇓ x Γ⇓))
    Term⇓ (f ‘‘→'’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘→'’ lower (Term⇓ x Γ⇓))
    Term⇓ (f w‘‘→'’’ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘→'’ lower (Term⇓ x Γ⇓))
    Term⇓ (w→ x) Γ⇓ A⇓ = Term⇓ x (Σ.proj₁ Γ⇓) A⇓
    Term⇓ w‘‘→'’’→‘‘→'’’ Γ⇓ T⇓ = T⇓
    Term⇓ ‘‘→'’’→w‘‘→'’’ Γ⇓ T⇓ = T⇓
    Term⇓ ‘tApp-nd’ Γ⇓ f⇓ x⇓ = lift (SW (lower f⇓ ‘’ₐ lower x⇓))
    Term⇓ ⌜←'⌝ Γ⇓ T⇓ = T⇓
    Term⇓ ⌜→'⌝ Γ⇓ T⇓ = T⇓
    Term⇓ (‘‘fcomp-nd’’ {A} {B} {C}) Γ⇓ g⇓ f⇓ = lift (_‘∘’_ {ε} (lower g⇓) (lower f⇓))
    Term⇓ (⌜‘’⌝ {B} {A} {b}) Γ⇓ = lift (‘λ∙’ {ε} (‘VAR₀’ {ε} {_‘’_ {ε} A b}))
    Term⇓ (⌜‘’⌝' {B} {A} {b}) Γ⇓ = lift (‘λ∙’ {ε} (‘VAR₀’ {ε} {_‘’_ {ε} A b}))
    Term⇓ (‘cast-refl’ {T}) Γ⇓ = lift (cast-proof {T})
    Term⇓ (‘cast-refl'’ {T}) Γ⇓ = lift (cast'-proof {T})
    Term⇓ (‘s→→’ {T} {B} {b} {c} {v}) Γ⇓ = lift (‘idfun’ {_‘’_ {ε} (lower (Term⇓ b tt (Term⇓ v Γ⇓))) (lower (Term⇓ c tt (Term⇓ v Γ⇓)))})
    Term⇓ (‘s←←’ {T} {B} {b} {c} {v}) Γ⇓ = lift (‘idfun’ {_‘’_ {ε} (lower (Term⇓ b tt (Term⇓ v Γ⇓))) (lower (Term⇓ c tt (Term⇓ v Γ⇓)))})

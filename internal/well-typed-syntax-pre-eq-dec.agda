{-# OPTIONS --without-K #-}
module well-typed-syntax-pre-eq-dec where
open import well-typed-syntax
open import common
open import common-utilities
open import well-typed-syntax-pre-eq-dec-defs

-- not sure why we need this; everything is structural on the context/type/term argument, respectively
{-# NON_TERMINATING #-}
mutual
  ≟'-ctx-refl : ∀ x → (x ≟'-ctx x) ≡ just refl
  ≟'-ctx-refl ε = refl
  ≟'-ctx-refl (x ▻ x₁) = lift-≟-2-refl _▻_ (_ ≟'-ctx _) (λ p → _ ≟'-typ _) (≟'-ctx-refl x) (≟'-typ-refl _)

  ≟'-typ-refl : ∀ {Γ} (x : Typ Γ) → (x ≟'-typ x) ≡ just refl
  ≟'-typ-refl (_‘’_ {Γ = Γ} {A = A} x₁ x₂) = lift-≟-3-refl (λ A → _‘’_ {A = A}) (_ ≟'-typ _) (λ p → _ ≟'-typ _)
                             (λ p q → _ ≟'-term _) (≟'-typ-refl {Γ} A) (≟'-typ-refl {Γ ▻ A} x₁) (≟'-term-refl x₂)
  ≟'-typ-refl (x₂ ‘’₁ a) = lift-≟-1-refl (λ x → x ‘’₁ a) (_ ≟'-typ _) (≟'-typ-refl x₂)
  ≟'-typ-refl (x₃ ‘’₂ a) = lift-≟-1-refl (λ x → x ‘’₂ a) (_ ≟'-typ _) (≟'-typ-refl x₃)
  ≟'-typ-refl (x₄ ‘’₃ a) = lift-≟-1-refl (λ x → x ‘’₃ a) (_ ≟'-typ _) (≟'-typ-refl x₄)
  ≟'-typ-refl (W x₁) = lift-≟-1-refl W (_ ≟'-typ _) (≟'-typ-refl x₁)
  ≟'-typ-refl (W1 x₂) = lift-≟-1-refl W1 (_ ≟'-typ _) (≟'-typ-refl x₂)
  ≟'-typ-refl (W2 x₃) = lift-≟-1-refl W2 (_ ≟'-typ _) (≟'-typ-refl x₃)
  ≟'-typ-refl ‘Context’ = refl
  ≟'-typ-refl ‘Typ’ = refl
  ≟'-typ-refl ‘Term’ = refl
  ≟'-typ-refl (x ‘→’ x₁) = lift-≟-2-refl _‘→’_ (_ ≟'-typ _) (λ p → _ ≟'-typ _) (≟'-typ-refl x) (≟'-typ-refl x₁)
  ≟'-typ-refl (‘Σ'’ x x₁) = lift-≟-2-refl ‘Σ'’ (_ ≟'-typ _) (λ p → _ ≟'-typ _) (≟'-typ-refl x) (≟'-typ-refl x₁)

  ≟'-term-refl : ∀ {Γ} {T : Typ Γ} (x : Term T) → (x ≟'-term x) ≡ just refl
  ≟'-term-refl (w x) = lift-≟-1-refl w (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (‘λ∙’ x) = lift-≟-1-refl ‘λ∙’ (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (x ‘’ₐ x₁) = lift-≟-1-refl (λ x₂ → x₂ ‘’ₐ x₁) (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl ‘VAR₀’ = refl
  ≟'-term-refl ‘quote-term’ = refl
  ≟'-term-refl ‘quote-sigma’ = refl
  ≟'-term-refl ‘substTyp’ = refl
  ≟'-term-refl ‘tProd-nd’ = refl
  ≟'-term-refl ‘context-pick-if'’ = refl
  ≟'-term-refl (⌜ x ⌝c) = lift-≟-1-refl ⌜_⌝c (_ ≟'-ctx _) (≟'-ctx-refl x)
  ≟'-term-refl (⌜ x ⌝T) = lift-≟-1-refl ⌜_⌝T (_ ≟'-typ _) (≟'-typ-refl x)
  ≟'-term-refl (⌜ x ⌝t) = lift-≟-1-refl ⌜_⌝t (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (substTyp-weakenTyp {A = A} {a = a} x₁) = lift-≟-3-refl (λ A a → substTyp-weakenTyp {A = A} {a = a})
                                           (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _) (≟'-typ-refl A) (≟'-term-refl (transport Term refl a)) (≟'-term-refl x₁)
  ≟'-term-refl (weakenTyp-substTyp-tProd x₁) = lift-≟-1-refl weakenTyp-substTyp-tProd (_ ≟'-term _) (≟'-term-refl x₁)
  ≟'-term-refl (substTyp-weakenTyp1-VAR₀ x) = lift-≟-1-refl substTyp-weakenTyp1-VAR₀ (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (weakenTyp-tProd x) = lift-≟-1-refl weakenTyp-tProd (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (weakenTyp-tProd-inv x) = lift-≟-1-refl weakenTyp-tProd-inv (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (weakenTyp-weakenTyp-tProd x) = lift-≟-1-refl weakenTyp-weakenTyp-tProd (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (substTyp1-tProd x₁) = lift-≟-1-refl substTyp1-tProd (_ ≟'-term _) (≟'-term-refl x₁)
  ≟'-term-refl (weakenTyp1-tProd x) = lift-≟-1-refl weakenTyp1-tProd (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (substTyp2-tProd x₁) = lift-≟-1-refl substTyp2-tProd (_ ≟'-term _) (≟'-term-refl x₁)
  ≟'-term-refl (substTyp1-substTyp-weakenTyp-inv x₂) = lift-≟-1-refl substTyp1-substTyp-weakenTyp-inv (_ ≟'-term _) (≟'-term-refl x₂)
  ≟'-term-refl (substTyp1-substTyp-weakenTyp {T = T} {b = b} x₂) = lift-≟-3-refl
                                                     (λ T b → substTyp1-substTyp-weakenTyp {T = T} {b = b}) (_ ≟'-typ _)
                                                     (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _) (≟'-typ-refl T) (≟'-term-refl b) (≟'-term-refl x₂)
  ≟'-term-refl (weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp {T = T} {b = b} x₂) = lift-≟-3-refl
                                                     (λ T b → weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp {T = T} {b = b}) (_ ≟'-typ _)
                                                     (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _) (≟'-typ-refl T) (≟'-term-refl b) (≟'-term-refl x₂)
  ≟'-term-refl (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv x₃) = lift-≟-1-refl weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv (_ ≟'-term _) (≟'-term-refl x₃)
  ≟'-term-refl (substTyp2-substTyp1-substTyp-weakenTyp {C = C} {c = c} x₃) = lift-≟-3-refl
                                                               (λ C c → substTyp2-substTyp1-substTyp-weakenTyp {C = C} {c = c})
                                                               (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _) (≟'-typ-refl C) (≟'-term-refl c) (≟'-term-refl x₃)
  ≟'-term-refl (weakenTyp-substTyp2-substTyp1-substTyp-tProd x₃) = lift-≟-1-refl weakenTyp-substTyp2-substTyp1-substTyp-tProd (_ ≟'-term _) (≟'-term-refl x₃)
  ≟'-term-refl (weakenTyp2-weakenTyp1 x) = lift-≟-1-refl weakenTyp2-weakenTyp1 (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (weakenTyp1-weakenTyp x) = lift-≟-1-refl weakenTyp1-weakenTyp (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (weakenTyp1-weakenTyp-inv x) = lift-≟-1-refl weakenTyp1-weakenTyp-inv (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (weakenTyp1-weakenTyp1-weakenTyp x) = lift-≟-1-refl weakenTyp1-weakenTyp1-weakenTyp (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (substTyp1-weakenTyp1 {A = A} {a = a} x₁) = lift-≟-3-refl (λ A a → substTyp1-weakenTyp1 {A = A} {a = a})
                                                             (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _) (≟'-typ-refl A) (≟'-term-refl a) (≟'-term-refl x₁)
  ≟'-term-refl (weakenTyp1-substTyp-weakenTyp1-inv x₁) = lift-≟-1-refl weakenTyp1-substTyp-weakenTyp1-inv (_ ≟'-term _) (≟'-term-refl x₁)
  ≟'-term-refl (weakenTyp1-substTyp-weakenTyp1 x₁) = lift-≟-1-refl weakenTyp1-substTyp-weakenTyp1 (_ ≟'-term _) (≟'-term-refl x₁)
  ≟'-term-refl (weakenTyp-substTyp-substTyp-weakenTyp1 x₂) = lift-≟-1-refl weakenTyp-substTyp-substTyp-weakenTyp1 (_ ≟'-term _) (≟'-term-refl x₂)
  ≟'-term-refl (weakenTyp-substTyp-substTyp-weakenTyp1-inv x₂) = lift-≟-1-refl weakenTyp-substTyp-substTyp-weakenTyp1-inv (_ ≟'-term _) (≟'-term-refl x₂)
  ≟'-term-refl (substTyp-weakenTyp1-weakenTyp {B = B} {a = a} x₁) = lift-≟-3-refl
                                                      (λ B a → substTyp-weakenTyp1-weakenTyp {B = B} {a = a})
                                                      (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
                                                      (≟'-typ-refl B) (≟'-term-refl a) (≟'-term-refl x₁)
  ≟'-term-refl (substTyp3-substTyp2-substTyp1-substTyp-weakenTyp {D = D} {d = d} x₄) = lift-≟-3-refl
                                                                         (λ D d →
                                                                            substTyp3-substTyp2-substTyp1-substTyp-weakenTyp {D = D} {d = d})
                                                                         (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
                                                                         (≟'-typ-refl D) (≟'-term-refl d) (≟'-term-refl x₄)
  ≟'-term-refl (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 {B = B} {b = b} x₃) = lift-≟-3-refl
                                                                          (λ B b →
                                                                             weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 {B = B} {b = b})
                                                                          (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
                                                                          (≟'-typ-refl B) (≟'-term-refl b) (≟'-term-refl x₃)
  ≟'-term-refl (substTyp1-substTyp-tProd x₂) = lift-≟-1-refl substTyp1-substTyp-tProd (_ ≟'-term _) (≟'-term-refl x₂)
  ≟'-term-refl (substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp {C = C} {B = B} {b = b} {c = c} x₃)
    = lift-≟-5-refl
        (λ C₁ B₁ b₁ c₁ →
           substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp {C = C₁}
           {B = B₁} {b = b₁} {c = c₁})
        (_ ≟'-typ _) (λ p → _ ≟'-typ _) (λ p q → _ ≟'-term _)
        (λ p q r → _ ≟'-term _) (λ p q r s → _ ≟'-term _) (≟'-typ-refl C)
        (≟'-typ-refl B) (≟'-term-refl b) (≟'-term-refl c) (≟'-term-refl x₃)
  ≟'-term-refl (substTyp1-substTyp-weakenTyp2-weakenTyp {B = B} {b = b} x₂) = lift-≟-3-refl
                                                                (λ B b → substTyp1-substTyp-weakenTyp2-weakenTyp {B = B} {b = b})
                                                                (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
                                                                (≟'-typ-refl B) (≟'-term-refl b) (≟'-term-refl x₂)
  ≟'-term-refl (weakenTyp-weakenTyp1-weakenTyp x) = lift-≟-1-refl weakenTyp-weakenTyp1-weakenTyp (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl (beta-under-subst x) = lift-≟-1-refl beta-under-subst (_ ≟'-term _) (≟'-term-refl x)
  ≟'-term-refl ‘proj₁'’ = refl
  ≟'-term-refl ‘proj₂'’ = refl
  ≟'-term-refl ‘existT'’ = refl
  ≟'-term-refl ‘cast-refl’₀ = refl

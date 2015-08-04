module well-typed-syntax-pre-eq-dec-defs where
open import well-typed-syntax
open import common
open import common-utilities

mutual
  _≟'-ctx_ : (x : Context) → (y : Context) → Maybe (x ≡ y)
  ε ≟'-ctx ε = just refl
  (x ▻ x₁) ≟'-ctx (y ▻ y₁) = lift-≟-2 _▻_ (x ≟'-ctx y) (λ p → _ ≟'-typ _)
  ε ≟'-ctx _ = nothing
  (x ▻ x₁) ≟'-ctx _ = nothing

  _≟'-typ_ : {Γ : Context} → (x : Typ Γ) → (y : Typ Γ) → Maybe (x ≡ y)
  (x₁ ‘’ x₂) ≟'-typ (y₁ ‘’ x) = lift-≟-3 (λ A → _‘’_ {A = A}) (_ ≟'-typ _) (λ p → _ ≟'-typ _) (λ p q → _ ≟'-term _)
  (x₂ ‘’₁ a) ≟'-typ (y ‘’₁ .a) = lift-≟-1 (λ x → x ‘’₁ a) (_ ≟'-typ _)
  (x₃ ‘’₂ a) ≟'-typ (y ‘’₂ .a) = lift-≟-1 (λ x → x ‘’₂ a) (_ ≟'-typ _)
  (x₄ ‘’₃ a) ≟'-typ (y ‘’₃ .a) = lift-≟-1 (λ x → x ‘’₃ a) (_ ≟'-typ _)
  W x₁ ≟'-typ W y = lift-≟-1 W (x₁ ≟'-typ y)
  W1 x₂ ≟'-typ (W1 y) = lift-≟-1 W1 (_ ≟'-typ _)
  W2 x₃ ≟'-typ (W2 y) = lift-≟-1 W2 (_ ≟'-typ _)
  ‘Context’ ≟'-typ ‘Context’ = just refl
  ‘Typ’ ≟'-typ ‘Typ’ = just refl
  ‘Term’ ≟'-typ ‘Term’ = just refl
  (x ‘→’ x₁) ≟'-typ (y ‘→’ y₁) = helper
    where {- work around what is probably https://code.google.com/p/agda/issues/detail?id=891 -}
      helper : Maybe ((x ‘→’ x₁) ≡ (y ‘→’ y₁))
      helper = lift-≟-2 _‘→’_ (_ ≟'-typ _) (λ p → _ ≟'-typ _)
  ‘Σ'’ x x₁ ≟'-typ ‘Σ'’ y y₁ = helper
    where
      helper : Maybe (‘Σ'’ x x₁ ≡ ‘Σ'’ y y₁)
      helper = lift-≟-2 ‘Σ'’ (_ ≟'-typ _) (λ p → _ ≟'-typ _)
  (x₁ ‘’ x₂) ≟'-typ y = nothing
  (x₂ ‘’₁ a) ≟'-typ y = nothing
  (x₃ ‘’₂ a) ≟'-typ y = nothing
  (x₄ ‘’₃ a) ≟'-typ y = nothing
  ‘Context’ ≟'-typ y = nothing
  ‘Typ’ ≟'-typ y = nothing
  ‘Term’ ≟'-typ y = nothing
  W x₁ ≟'-typ y = nothing
  W1 x₂ ≟'-typ y = nothing
  W2 x₃ ≟'-typ y = nothing
  (x ‘→’ x₁) ≟'-typ y = nothing
  ‘Σ'’ x x₁ ≟'-typ y = nothing

  _≟'-term_ : {Γ : Context} → {T : Typ Γ} → (x : Term T) → (y : Term T) → Maybe (x ≡ y)
  w x ≟'-term w y = lift-≟-1 w (_ ≟'-term _)
  ‘λ∙’ x ≟'-term ‘λ∙’ y = lift-≟-1 ‘λ∙’ (_ ≟'-term _)
  (x ‘’ₐ x₁) ≟'-term (y ‘’ₐ .x₁) = lift-≟-1 (λ x₂ → x₂ ‘’ₐ x₁) (_ ≟'-term _)
  ‘VAR₀’ ≟'-term ‘VAR₀’ = just refl
  ⌜ x ⌝c ≟'-term ⌜ y ⌝c = lift-≟-1 ⌜_⌝c (_ ≟'-ctx _)
  ⌜ x ⌝T ≟'-term ⌜ y ⌝T = lift-≟-1 ⌜_⌝T (_ ≟'-typ _)
  ⌜ x ⌝t ≟'-term ⌜ y ⌝t = lift-≟-1 ⌜_⌝t (_ ≟'-term _)
  ‘quote-term’ ≟'-term ‘quote-term’ = just refl
  ‘quote-sigma’ ≟'-term ‘quote-sigma’ = just refl
  ‘substTyp’ ≟'-term ‘substTyp’ = just refl
  ‘tProd-nd’ ≟'-term ‘tProd-nd’ = just refl
  ‘context-pick-if'’ ≟'-term ‘context-pick-if'’ = just refl
  substTyp-weakenTyp x₁ ≟'-term substTyp-weakenTyp y = lift-≟-3 (λ A a → substTyp-weakenTyp {A = A} {a = a}) (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
  weakenTyp-substTyp-tProd x₁ ≟'-term weakenTyp-substTyp-tProd y = lift-≟-1 weakenTyp-substTyp-tProd (_ ≟'-term _)
  substTyp-weakenTyp1-VAR₀ x ≟'-term substTyp-weakenTyp1-VAR₀ y = lift-≟-1 substTyp-weakenTyp1-VAR₀ (_ ≟'-term _)
  weakenTyp-tProd x ≟'-term weakenTyp-tProd y = lift-≟-1 weakenTyp-tProd (_ ≟'-term _)
  weakenTyp-tProd-inv x ≟'-term weakenTyp-tProd-inv y = lift-≟-1 weakenTyp-tProd-inv (_ ≟'-term _)
  weakenTyp-weakenTyp-tProd x ≟'-term weakenTyp-weakenTyp-tProd y = lift-≟-1 weakenTyp-weakenTyp-tProd (_ ≟'-term _)
  substTyp1-tProd x₁ ≟'-term substTyp1-tProd y = lift-≟-1 substTyp1-tProd (_ ≟'-term _)
  weakenTyp1-tProd x ≟'-term weakenTyp1-tProd y = lift-≟-1 weakenTyp1-tProd (_ ≟'-term _)
  substTyp2-tProd x₁ ≟'-term substTyp2-tProd y = lift-≟-1 substTyp2-tProd (_ ≟'-term _)
  substTyp1-substTyp-weakenTyp-inv x₂ ≟'-term substTyp1-substTyp-weakenTyp-inv y = lift-≟-1 substTyp1-substTyp-weakenTyp-inv (_ ≟'-term _)
  substTyp1-substTyp-weakenTyp x₂ ≟'-term substTyp1-substTyp-weakenTyp y = lift-≟-3 (λ T b → substTyp1-substTyp-weakenTyp {T = T} {b = b}) (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
  weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp x₂ ≟'-term weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp y = lift-≟-3 (λ T b → weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp {T = T} {b = b}) (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
  weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv x₃ ≟'-term weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv y = lift-≟-1 weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv (_ ≟'-term _)
  substTyp2-substTyp1-substTyp-weakenTyp x₃ ≟'-term substTyp2-substTyp1-substTyp-weakenTyp y = lift-≟-3 (λ C c → substTyp2-substTyp1-substTyp-weakenTyp {C = C} {c = c}) (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
  weakenTyp-substTyp2-substTyp1-substTyp-tProd x₃ ≟'-term weakenTyp-substTyp2-substTyp1-substTyp-tProd y = lift-≟-1 weakenTyp-substTyp2-substTyp1-substTyp-tProd (_ ≟'-term _)
  weakenTyp2-weakenTyp1 x ≟'-term weakenTyp2-weakenTyp1 y = lift-≟-1 weakenTyp2-weakenTyp1 (_ ≟'-term _)
  weakenTyp1-weakenTyp x ≟'-term weakenTyp1-weakenTyp y = lift-≟-1 weakenTyp1-weakenTyp (_ ≟'-term _)
  weakenTyp1-weakenTyp-inv x ≟'-term weakenTyp1-weakenTyp-inv y = lift-≟-1 weakenTyp1-weakenTyp-inv (_ ≟'-term _)
  weakenTyp1-weakenTyp1-weakenTyp x ≟'-term weakenTyp1-weakenTyp1-weakenTyp y = lift-≟-1 weakenTyp1-weakenTyp1-weakenTyp (_ ≟'-term _)
  substTyp1-weakenTyp1 x₁ ≟'-term substTyp1-weakenTyp1 y = lift-≟-3 (λ A a → substTyp1-weakenTyp1 {A = A} {a = a}) (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
  weakenTyp1-substTyp-weakenTyp1-inv x₁ ≟'-term weakenTyp1-substTyp-weakenTyp1-inv y = lift-≟-1 weakenTyp1-substTyp-weakenTyp1-inv (_ ≟'-term _)
  weakenTyp1-substTyp-weakenTyp1 x₁ ≟'-term weakenTyp1-substTyp-weakenTyp1 y = lift-≟-1 weakenTyp1-substTyp-weakenTyp1 (_ ≟'-term _)
  weakenTyp-substTyp-substTyp-weakenTyp1 x₂ ≟'-term weakenTyp-substTyp-substTyp-weakenTyp1 y = lift-≟-1 weakenTyp-substTyp-substTyp-weakenTyp1 (_ ≟'-term _)
  weakenTyp-substTyp-substTyp-weakenTyp1-inv x₂ ≟'-term weakenTyp-substTyp-substTyp-weakenTyp1-inv y = lift-≟-1 weakenTyp-substTyp-substTyp-weakenTyp1-inv (_ ≟'-term _)
  substTyp-weakenTyp1-weakenTyp x₁ ≟'-term substTyp-weakenTyp1-weakenTyp y = lift-≟-3 (λ B a → substTyp-weakenTyp1-weakenTyp {B = B} {a = a}) (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
  substTyp3-substTyp2-substTyp1-substTyp-weakenTyp x₄ ≟'-term substTyp3-substTyp2-substTyp1-substTyp-weakenTyp y = lift-≟-3 (λ D d → substTyp3-substTyp2-substTyp1-substTyp-weakenTyp {D = D} {d = d}) (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
  weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 x₃ ≟'-term weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 y = lift-≟-3 (λ B b → weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 {B = B} {b = b}) (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
  substTyp1-substTyp-tProd x₂ ≟'-term substTyp1-substTyp-tProd y = lift-≟-1 substTyp1-substTyp-tProd (_ ≟'-term _)
  substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp x₃ ≟'-term substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp y
    = lift-≟-5 (λ C B b c → substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp {C = C} {B = B} {b = b} {c = c}) (_ ≟'-typ _) (λ p → _ ≟'-typ _) (λ p q → _ ≟'-term _) (λ p q r → _ ≟'-term _) (λ p q r s → _ ≟'-term _)
  substTyp1-substTyp-weakenTyp2-weakenTyp x₂ ≟'-term substTyp1-substTyp-weakenTyp2-weakenTyp y = lift-≟-3 (λ B b → substTyp1-substTyp-weakenTyp2-weakenTyp {B = B} {b = b}) (_ ≟'-typ _) (λ p → _ ≟'-term _) (λ p q → _ ≟'-term _)
  weakenTyp-weakenTyp1-weakenTyp x ≟'-term weakenTyp-weakenTyp1-weakenTyp x' = lift-≟-1 weakenTyp-weakenTyp1-weakenTyp (_ ≟'-term _)
  beta-under-subst x ≟'-term beta-under-subst x' = lift-≟-1 beta-under-subst (_ ≟'-term _)
  ‘proj₁'’ ≟'-term ‘proj₁'’ = just refl
  ‘proj₂'’ ≟'-term ‘proj₂'’ = just refl
  ‘existT'’ ≟'-term ‘existT'’ = just refl
  ‘context-pick-if’-refl-inv ≟'-term ‘context-pick-if’-refl-inv = just refl
  ‘context-pick-if’-refl ≟'-term ‘context-pick-if’-refl = just refl
  w x ≟'-term y = nothing
  ‘λ∙’ x ≟'-term y = nothing
  (x ‘’ₐ x₁) ≟'-term y = nothing
  ‘VAR₀’ ≟'-term y = nothing
  ⌜ x ⌝c ≟'-term y = nothing
  ⌜ x ⌝T ≟'-term y = nothing
  ⌜ x ⌝t ≟'-term y = nothing
  ‘quote-term’ ≟'-term y = nothing
  ‘quote-sigma’ ≟'-term y = nothing
  ‘substTyp’ ≟'-term y = nothing
  ‘tProd-nd’ ≟'-term y = nothing
  ‘context-pick-if'’ ≟'-term y = nothing
  substTyp-weakenTyp x₁ ≟'-term y = nothing
  weakenTyp-substTyp-tProd x₁ ≟'-term y = nothing
  substTyp-weakenTyp1-VAR₀ x ≟'-term y = nothing
  weakenTyp-tProd x ≟'-term y = nothing
  weakenTyp-tProd-inv x ≟'-term y = nothing
  weakenTyp-weakenTyp-tProd x ≟'-term y = nothing
  substTyp1-tProd x₁ ≟'-term y = nothing
  weakenTyp1-tProd x ≟'-term y = nothing
  substTyp2-tProd x₁ ≟'-term y = nothing
  substTyp1-substTyp-weakenTyp-inv x₂ ≟'-term y = nothing
  substTyp1-substTyp-weakenTyp x₂ ≟'-term y = nothing
  weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp x₂ ≟'-term y = nothing
  weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv x₃ ≟'-term y = nothing
  substTyp2-substTyp1-substTyp-weakenTyp x₃ ≟'-term y = nothing
  weakenTyp-substTyp2-substTyp1-substTyp-tProd x₃ ≟'-term y = nothing
  weakenTyp2-weakenTyp1 x ≟'-term y = nothing
  weakenTyp1-weakenTyp x ≟'-term y = nothing
  weakenTyp1-weakenTyp-inv x ≟'-term y = nothing
  weakenTyp1-weakenTyp1-weakenTyp x ≟'-term y = nothing
  substTyp1-weakenTyp1 x₁ ≟'-term y = nothing
  weakenTyp1-substTyp-weakenTyp1-inv x₁ ≟'-term y = nothing
  weakenTyp1-substTyp-weakenTyp1 x₁ ≟'-term y = nothing
  weakenTyp-substTyp-substTyp-weakenTyp1 x₂ ≟'-term y = nothing
  weakenTyp-substTyp-substTyp-weakenTyp1-inv x₂ ≟'-term y = nothing
  substTyp-weakenTyp1-weakenTyp x₁ ≟'-term y = nothing
  substTyp3-substTyp2-substTyp1-substTyp-weakenTyp x₄ ≟'-term y = nothing
  weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 x₃ ≟'-term y = nothing
  substTyp1-substTyp-tProd x₂ ≟'-term y = nothing
  substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp x₃ ≟'-term y = nothing
  substTyp1-substTyp-weakenTyp2-weakenTyp x₂ ≟'-term y = nothing
  weakenTyp-weakenTyp1-weakenTyp x ≟'-term y = nothing
  beta-under-subst x ≟'-term y = nothing
  ‘proj₁'’ ≟'-term y = nothing
  ‘proj₂'’ ≟'-term y = nothing
  ‘existT'’ ≟'-term y = nothing
  ‘context-pick-if’-refl-inv ≟'-term y = nothing
  ‘context-pick-if’-refl ≟'-term y = nothing

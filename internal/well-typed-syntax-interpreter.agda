module well-typed-syntax-interpreter where
open import common public
open import well-typed-syntax

max-level : Level
max-level = lzero

Context⇓▻-helper : ∀ Γ⇓
  → Maybe-elim (λ _ → Set _) (λ (Γ⇓ : Set) → Maybe (Γ⇓ → Set)) ⊤ Γ⇓
  → Maybe (Set max-level)
Context⇓▻-helper (just Γ⇓) (just T⇓) = just (Σ (λ (Γ' : Γ⇓) → T⇓ Γ'))
Context⇓▻-helper (just Γ⇓) nothing = nothing
Context⇓▻-helper nothing tt = nothing

mutual
  Typ⇓-type : Maybe (Set max-level) → Set _
  Typ⇓-type Γ⇓ = Maybe-elim (λ _ → Set _) (λ Γ⇓ → Maybe (Γ⇓ → Set max-level)) ⊤ Γ⇓

  Term⇓-type : (Γ : Maybe (Set max-level)) → Typ⇓-type Γ → Set _
  Term⇓-type Γ⇓ T⇓
    = Maybe-elim (λ Γ → Typ⇓-type Γ → Set _)
                 (λ Γ⇓ T⇓ → Maybe-elim (λ _ → Set _) (λ T⇓' → Maybe ((Γ₁ : Γ⇓) → T⇓' Γ₁)) ⊤ T⇓)
                 (λ _ → ⊤)
                 Γ⇓
                 T⇓

  Context⇓ : Context → Maybe (Set max-level)
  Context⇓ ε₀ = just ⊤
  Context⇓ (Γ ▻Typ Γ₁) = {!!}
  Context⇓ (Γ ▻ T) = Context⇓▻-helper (Context⇓ Γ) (Typ⇓ T)

  Typ⇓-Σ-helper-type : Set _
  Typ⇓-Σ-helper-type = (Γ⇓ : Maybe (Set _))
        → (T⇓ : Typ⇓-type Γ⇓)
        → Typ⇓-type (Context⇓▻-helper Γ⇓ T⇓)
        → Typ⇓-type Γ⇓
  Typ⇓-Σ-helper : Typ⇓-Σ-helper-type
  Typ⇓-Σ-helper (just Γ⇓) (just T⇓) (just T₁⇓) = just (λ Γ₁ → Σ (λ T₂ → T₁⇓ (Γ₁ , T₂)))
  Typ⇓-Σ-helper (just Γ⇓) (just T⇓) nothing = nothing
  Typ⇓-Σ-helper (just Γ⇓) nothing _ = nothing
  Typ⇓-Σ-helper nothing _ _ = tt

  Typ⇓-‘’-helper-type : Set _
  Typ⇓-‘’-helper-type = (Γ⇓ : Maybe (Set _))
        → (A⇓ : Typ⇓-type Γ⇓)
        → (T₁⇓ : Typ⇓-type (Context⇓▻-helper Γ⇓ A⇓))
        → (x⇓ : Term⇓-type Γ⇓ A⇓)
        → Typ⇓-type Γ⇓

  Typ⇓-‘’-helper : Typ⇓-‘’-helper-type
  Typ⇓-‘’-helper (just Γ⇓) (just A⇓) (just T⇓) (just x⇓) = just (λ Γ⇓' → T⇓ (Γ⇓' , (x⇓ Γ⇓')))
  Typ⇓-‘’-helper (just _) (just _) _ nothing = nothing
  Typ⇓-‘’-helper (just _) (just _) nothing _ = nothing
  Typ⇓-‘’-helper (just _) nothing _ _ = nothing
  Typ⇓-‘’-helper nothing _ _ _ = tt

  Typ⇓ : {Γ : Context} → Typ Γ → Typ⇓-type (Context⇓ Γ)
  Typ⇓ {Γ} (_‘’_ {.Γ} {A} T₁ x) = Typ⇓-‘’-helper (Context⇓ Γ) (Typ⇓ A) (Typ⇓ T₁) (Term⇓ x)
  Typ⇓ {Γ ▻ B ‘’ .a} (T₂ ‘’₁ a) = {!!}
  Typ⇓ {Γ ▻ B ‘’ .a ▻ C ‘’₁ .a} (T₃ ‘’₂ a) = {!!}
  Typ⇓ {Γ ▻ B ‘’ .a ▻ C ‘’₁ .a ▻ D ‘’₂ .a} (T₄ ‘’₃ a) = {!!}
  Typ⇓ {Γ ▻ A} (W T₁) = {!!}
  Typ⇓ {Γ ▻ A ▻ W B} (W1 T₂) = {!!}
  Typ⇓ {Γ ▻ A ▻ W B ▻ W1 C} (W2 T₃) = {!!}
  Typ⇓ {Γ} (T ‘→’ T₁) = helper (Context⇓ Γ) (Typ⇓ T) (Typ⇓ T₁)
    where
      helper : (Γ⇓ : Maybe Set)
        → (T⇓ : Typ⇓-type Γ⇓)
        → Typ⇓-type (Context⇓▻-helper Γ⇓ T⇓)
        → Typ⇓-type Γ⇓
      helper (just Γ⇓) (just T⇓) (just T₁⇓) = just (λ Γ₁ → (T₂ : T⇓ Γ₁) → T₁⇓ (Γ₁ , T₂))
      helper (just Γ⇓) (just T⇓) nothing = nothing
      helper (just Γ⇓) nothing _ = nothing
      helper nothing _ _ = tt
  Typ⇓ {Γ ▻Typ A} (WT T) = {!!}
  Typ⇓ {Γ ▻Typ A ▻ WT B} (WT₁ T₁) = {!!}
  Typ⇓ {Γ ▻Typ A ▻ WT B ▻ WT₁ C} (WT₂ T₂) = {!!}
  Typ⇓ {Γ ▻Typ .Γ} ‘TVAR₀₀’ = {!!}
  Typ⇓ {Γ ▻Typ (.Γ ▻ .T) ▻ WT T} ‘TVAR₀₁’ = {!!}
  Typ⇓ {Γ ▻Typ (.Γ ▻ .A ▻ .B) ▻ WT A ▻ WT₁ B} ‘TVAR₀₂’ = {!!}
  Typ⇓ {Γ} (‘Σ'’ T T₁) = Typ⇓-Σ-helper (Context⇓ Γ) (Typ⇓ T) (Typ⇓ T₁)


  Term⇓ : ∀ {Γ : Context} {T : Typ Γ} → Term T → Term⇓-type _ (Typ⇓ T)
  Term⇓ (w t) = {!!}
  Term⇓ (‘λ∙’ t) = {!!}
  Term⇓ (t ‘’ₐ t₁) = {!!}
  Term⇓ ‘VAR₀’ = {!!}
  Term⇓ (substTyp-weakenTyp t₁) = {!!}
  Term⇓ (weakenTyp-substTyp-tProd t₁) = {!!}
  Term⇓ (substTyp-weakenTyp1-VAR₀ t) = {!!}
  Term⇓ (weakenTyp-tProd t) = {!!}
  Term⇓ (weakenTyp-tProd-inv t) = {!!}
  Term⇓ (weakenTyp-weakenTyp-tProd t) = {!!}
  Term⇓ (substTyp1-tProd t₁) = {!!}
  Term⇓ (weakenTyp1-tProd t) = {!!}
  Term⇓ (substTyp2-tProd t₁) = {!!}
  Term⇓ (substTyp1-substTyp-weakenTyp-inv t₂) = {!!}
  Term⇓ (substTyp1-substTyp-weakenTyp t₂) = {!!}
  Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv t₃) = {!!}
  Term⇓ (substTyp2-substTyp1-substTyp-weakenTyp t₃) = {!!}
  Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-tProd t₃) = {!!}
  Term⇓ (weakenTyp2-weakenTyp1 t) = {!!}
  Term⇓ (weakenTyp1-weakenTyp t) = {!!}
  Term⇓ (weakenTyp1-weakenTyp-inv t) = {!!}
  Term⇓ (weakenTyp1-weakenTyp1-weakenTyp t) = {!!}
  Term⇓ (substTyp1-weakenTyp1 t₁) = {!!}
  Term⇓ (weakenTyp1-substTyp-weakenTyp1-inv t₁) = {!!}
  Term⇓ (weakenTyp1-substTyp-weakenTyp1 t₁) = {!!}
  Term⇓ (weakenTyp-substTyp-substTyp-weakenTyp1 t₂) = {!!}
  Term⇓ (weakenTyp-substTyp-substTyp-weakenTyp1-inv t₂) = {!!}
  Term⇓ (substTyp-weakenTyp1-weakenTyp t₁) = {!!}
  Term⇓ (substTyp3-substTyp2-substTyp1-substTyp-weakenTyp t₄) = {!!}
  Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 t₃) = {!!}
  Term⇓ (substTyp1-substTyp-tProd t₂) = {!!}
  Term⇓ (substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp t₃) = {!!}
  Term⇓ (substTyp1-substTyp-weakenTyp2-weakenTyp t₂) = {!!}
  Term⇓ (weakenTyp-weakenTyp1-weakenTyp t) = {!!}
  Term⇓ ‘proj₁'’ = {!!}
  Term⇓ ‘proj₂'’ = {!!}
  Term⇓ {Γ} (‘existT'’ {._} {T} {T₁} t t₁) = helper (Context⇓ Γ) (Typ⇓ T) (Term⇓ t) (Typ⇓ T₁) (Term⇓ t₁)
    where
      helper : (Γ⇓ : Maybe (Set _))
        → (T⇓ : Typ⇓-type Γ⇓)
        → (t⇓ : Term⇓-type Γ⇓ T⇓)
        → (T₁⇓ : Typ⇓-type (Context⇓▻-helper Γ⇓ T⇓))
        → Term⇓-type Γ⇓ (Typ⇓-‘’-helper Γ⇓ T⇓ T₁⇓ t⇓)
        → Term⇓-type Γ⇓ (Typ⇓-Σ-helper Γ⇓ T⇓ T₁⇓)
      helper (just Γ⇓) (just T⇓) (just t⇓) (just T₁⇓) (just t₁⇓) = just (λ Γ₁ → (t⇓ Γ₁) , (t₁⇓ Γ₁))
      helper (just Γ⇓) (just T⇓) (just t⇓) (just T₁⇓) nothing = nothing
      helper (just Γ⇓) (just T⇓) nothing (just T₁⇓) t₁⇓ = nothing
      helper (just Γ⇓) (just T⇓) _ nothing _ = tt
      helper (just Γ⇓) nothing _ _ _ = tt
      helper nothing _ _ _ _ = tt
--  Typ⇓ {ε₀} (‘Σ'’ T T₁) = option-bind (Typ⇓ T) (λ T⇓ → option-bind (Typ⇓ (T₁) (λ T₁⇓ → {!!}))
 {-
  Typ⇓ (T₁ ‘’ x) = {!!}
  Typ⇓ (T₂ ‘’₁ a) = {!!}
  Typ⇓ (T₃ ‘’₂ a) = {!!}
  Typ⇓ (T₄ ‘’₃ a) = {!!}
  Typ⇓ (W T₁) = {!!}
  Typ⇓ (W1 T₂) = {!!}
  Typ⇓ (W2 T₃) = {!!}
  Typ⇓ (T ‘→’ T₁) = {!!}
  Typ⇓ (WT T) = {!!}
  Typ⇓ (WT₁ T₁) = {!!}
  Typ⇓ (WT₂ T₂) = {!!}
  Typ⇓ ‘TVAR₀₀’ = {!!}
  Typ⇓ ‘TVAR₀₁’ = {!!}
  Typ⇓ ‘TVAR₀₂’ = {!!}
  Typ⇓ {Γ} (‘Σ'’ T T₁) = {!!}-}

{-  Term⇓ : {Γ : Context} → {T : Typ Γ} → (x : Term T)
    → Maybe-elim (λ _ → Set _) (λ T' → Maybe T') ⊤ (Typ⇓ T)
  Term⇓ (x ‘t’ x₁) = {!!}
  Term⇓ (w x) = {!!}
  Term⇓ (‘λ∙’ x) = {!!}
  Term⇓ (x ‘’ₐ x₁) = {!!}
  Term⇓ ‘VAR₀’ = {!!}
  Term⇓ (substTyp-weakenTyp x₁) = {!!}
  Term⇓ (weakenTyp-substTyp-tProd x₁) = {!!}
  Term⇓ (substTyp-weakenTyp1-VAR₀ x) = {!!}
  Term⇓ (weakenTyp-tProd x) = {!!}
  Term⇓ (weakenTyp-tProd-inv x) = {!!}
  Term⇓ (weakenTyp-weakenTyp-tProd x) = {!!}
  Term⇓ (substTyp1-tProd x₁) = {!!}
  Term⇓ (weakenTyp1-tProd x) = {!!}
  Term⇓ (substTyp2-tProd x₁) = {!!}
  Term⇓ (substTyp1-substTyp-weakenTyp-inv x₂) = {!!}
  Term⇓ (substTyp1-substTyp-weakenTyp x₂) = {!!}
  Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv x₃) = {!!}
  Term⇓ (substTyp2-substTyp1-substTyp-weakenTyp x₃) = {!!}
  Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-tProd x₃) = {!!}
  Term⇓ (weakenTyp2-weakenTyp1 x) = {!!}
  Term⇓ (weakenTyp1-weakenTyp x) = {!!}
  Term⇓ (weakenTyp1-weakenTyp-inv x) = {!!}
  Term⇓ (weakenTyp1-weakenTyp1-weakenTyp x) = {!!}
  Term⇓ (substTyp1-weakenTyp1 x₁) = {!!}
  Term⇓ (weakenTyp1-substTyp-weakenTyp1-inv x₁) = {!!}
  Term⇓ (weakenTyp1-substTyp-weakenTyp1 x₁) = {!!}
  Term⇓ (weakenTyp-substTyp-substTyp-weakenTyp1 x₂) = {!!}
  Term⇓ (weakenTyp-substTyp-substTyp-weakenTyp1-inv x₂) = {!!}
  Term⇓ (substTyp-weakenTyp1-weakenTyp x₁) = {!!}
  Term⇓ (substTyp3-substTyp2-substTyp1-substTyp-weakenTyp x₄) = {!!}
  Term⇓ (weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 x₃) = {!!}
  Term⇓ (substTyp1-substTyp-tProd x₂) = {!!}
  Term⇓ (substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp x₃) = {!!}
  Term⇓ (substTyp1-substTyp-weakenTyp2-weakenTyp x₂) = {!!}
  Term⇓ (weakenTyp-weakenTyp1-weakenTyp x) = {!!}
  Term⇓ ‘proj₁'’ = {!!}
  Term⇓ ‘proj₂'’ = {!!}
  Term⇓ (‘existT'’ x x₁) = {!!}-}
{-
  data Context : Set where
    ε₀ : Context
    _▻Typ_ : (Γ : Context) → Context → Context
    _▻_ : (Γ : Context) → Typ Γ → Context

  data Typ : Context → Set where
    _‘’_ : ∀ {Γ A} → Typ (Γ ▻ A) → Term {Γ = Γ} A → Typ Γ
    _‘’₁_ : ∀ {Γ A B} → (C : Typ (Γ ▻ A ▻ B)) → (a : Term {Γ = Γ} A) → Typ (Γ ▻ B ‘’ a)
    _‘’₂_ : ∀ {Γ A B C} → (D : Typ (Γ ▻ A ▻ B ▻ C)) → (a : Term {Γ = Γ} A) → Typ (Γ ▻ B ‘’ a ▻ C ‘’₁ a)
    _‘’₃_ : ∀ {Γ A B C D} → (E : Typ (Γ ▻ A ▻ B ▻ C ▻ D)) → (a : Term {Γ = Γ} A) → Typ (Γ ▻ B ‘’ a ▻ C ‘’₁ a ▻ D ‘’₂ a)
    W : ∀ {Γ A} → Typ Γ → Typ (Γ ▻ A)
    W1 : ∀ {Γ A B} → Typ (Γ ▻ B) → Typ (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B))
    W2 : ∀ {Γ A B C} → Typ (Γ ▻ B ▻ C) → Typ (Γ ▻ A ▻ W B ▻ W1 C)
    _‘→’_ : ∀ {Γ} (A : Typ Γ) → Typ (Γ ▻ A) → Typ Γ
    WT : ∀ {Γ A} → Typ Γ → Typ (Γ ▻Typ A)
    WT₁ : ∀ {Γ A B} → Typ (Γ ▻ B) → Typ (Γ ▻Typ A ▻ WT B)
    WT₂ : ∀ {Γ A B C} → Typ (Γ ▻ B ▻ C) → Typ (Γ ▻Typ A ▻ WT B ▻ WT₁ C)
    ‘TVAR₀₀’ : ∀ {Γ} → Typ (Γ ▻Typ Γ)
    ‘TVAR₀₁’ : ∀ {Γ T} → Typ (Γ ▻Typ (Γ ▻ T) ▻ WT T)
    ‘TVAR₀₂’ : ∀ {Γ A B} → Typ (Γ ▻Typ (Γ ▻ A ▻ B) ▻ WT A ▻ WT₁ B)
    {-‘cstTVAR₀’ : ∀ {Γ Γ'} → Term {Γ ▻Typ Γ'} ‘TVAR₀’ → Typ Γ'-}
    ‘Σ'’ : ∀ {Γ} (T : Typ Γ) → Typ (Γ ▻ T) → Typ Γ
    {-‘Context’ : Typ ε₀
    ‘Typ’ : Typ (ε₀ ▻ ‘Context’)-}
    {-
-}


  data Term : ∀ {Γ} → Typ Γ → Set where
    _‘t’_ : ∀ {Γ A} {B : Typ (Γ ▻ A)} → (b : Term {Γ = Γ ▻ A} B) → (a : Term {Γ = Γ} A) → Term {Γ = Γ} (B ‘’ a)
    w : ∀ {Γ A B} → Term {Γ = Γ} B → Term {Γ = Γ ▻ A} (W {Γ = Γ} {A = A} B)
    ‘λ∙’ : ∀ {Γ A B} → Term {Γ = (Γ ▻ A)} B → Term {Γ = Γ} (A ‘→’ B)
    _‘’ₐ_ : ∀ {Γ A B} → (f : Term {Γ = Γ} (A ‘→’ B)) → (x : Term {Γ = Γ} A) → Term {Γ = Γ} (B ‘’ x)
    ‘VAR₀’ : ∀ {Γ T} → Term {Γ = Γ ▻ T} (W T)
    substTyp-weakenTyp : ∀ {Γ A B} {a : Term {Γ = Γ} A} → Term {Γ = Γ} (W B ‘’ a) → Term {Γ = Γ} B
    weakenTyp-substTyp-tProd : ∀ {Γ T T' A B} {a : Term {Γ = Γ} T} → Term {Γ = Γ ▻ T'} (W ((A ‘→’ B) ‘’ a)) → Term {Γ ▻ T'} (W ((A ‘’ a) ‘→’ (B ‘’₁ a)))
    substTyp-weakenTyp1-VAR₀ : ∀ {Γ A T} → Term {Γ ▻ A} (W1 T ‘’ ‘VAR₀’) → Term {Γ ▻ A} T
    weakenTyp-tProd : ∀ {Γ A B C} → Term {Γ = Γ ▻ C} (W (A ‘→’ B)) → Term {Γ = Γ ▻ C} (W A ‘→’ W1 B)
    weakenTyp-tProd-inv : ∀ {Γ A B C} → Term {Γ = Γ ▻ C} (W A ‘→’ W1 B) → Term {Γ = Γ ▻ C} (W (A ‘→’ B))
    weakenTyp-weakenTyp-tProd : ∀ {Γ A B C D} → Term {Γ ▻ C ▻ D} (W (W (A ‘→’ B))) → Term {Γ ▻ C ▻ D} (W (W A ‘→’ W1 B))
    substTyp1-tProd : ∀ {Γ T T' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a} ((A ‘→’ B) ‘’₁ a) → Term {Γ ▻ T' ‘’ a} ((A ‘’₁ a) ‘→’ (B ‘’₂ a))
    weakenTyp1-tProd : ∀ {Γ C D A B} → Term {Γ ▻ C ▻ W D} (W1 (A ‘→’ B)) → Term {Γ ▻ C ▻ W D} (W1 A ‘→’ W2 B)
    substTyp2-tProd : ∀ {Γ T T' T'' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a ▻ T'' ‘’₁ a} ((A ‘→’ B) ‘’₂ a) → Term {Γ ▻ T' ‘’ a ▻ T'' ‘’₁ a} ((A ‘’₂ a) ‘→’ (B ‘’₃ a))
    substTyp1-substTyp-weakenTyp-inv : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (A ‘’ a) → Term {Γ} (W A ‘’₁ a ‘’ b)
    substTyp1-substTyp-weakenTyp : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (W A ‘’₁ a ‘’ b) → Term {Γ} (A ‘’ a)
    weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv : ∀ {Γ A B C T T'} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
      → Term {Γ ▻ T'} (W (T ‘’₁ a ‘’ b))
      → Term {Γ ▻ T'} (W (W T ‘’₂ a ‘’₁ b ‘’ c))
    substTyp2-substTyp1-substTyp-weakenTyp : ∀ {Γ A B C T} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
      → Term {Γ} (W T ‘’₂ a ‘’₁ b ‘’ c)
      → Term {Γ} (T ‘’₁ a ‘’ b)
    weakenTyp-substTyp2-substTyp1-substTyp-tProd : ∀ {Γ T T' T'' T''' A B} {a : Term {Γ} T} {b : Term {Γ} (T' ‘’ a)} {c : Term {Γ} (T'' ‘’₁ a ‘’ b)}
      → Term {Γ ▻ T'''} (W ((A ‘→’ B) ‘’₂ a ‘’₁ b ‘’ c))
      → Term {Γ ▻ T'''} ((W (A ‘’₂ a ‘’₁ b ‘’ c)) ‘→’ (W1 (B ‘’₃ a ‘’₂ b ‘’₁ c)))
    weakenTyp2-weakenTyp1 : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ W B ▻ W1 C} (W2 (W D)) → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W1 D))
    weakenTyp1-weakenTyp : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W1 (W C)) → Term {Γ ▻ A ▻ W B} (W (W C))
    weakenTyp1-weakenTyp-inv : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W (W C)) → Term {Γ ▻ A ▻ W B} (W1 (W C))
    weakenTyp1-weakenTyp1-weakenTyp : ∀ {Γ A B C T} → Term {Γ ▻ A ▻ B ▻ W (W C)} (W1 (W1 (W T))) → Term {Γ ▻ A ▻ B ▻ W (W C)} (W1 (W (W T)))
    substTyp1-weakenTyp1 : ∀ {Γ A B C} {a : Term {Γ} A} → Term {Γ ▻ W B ‘’ a} (W1 C ‘’₁ a) → Term {Γ ▻ B} C
    weakenTyp1-substTyp-weakenTyp1-inv : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W (T ‘’ a)))
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W T ‘’₁ a))
    weakenTyp1-substTyp-weakenTyp1 : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W T ‘’₁ a))
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W (T ‘’ a)))
    weakenTyp-substTyp-substTyp-weakenTyp1 : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
      → Term {Γ ▻ T'} (W (T ‘’ (substTyp-weakenTyp (a ‘t’ b))))
    weakenTyp-substTyp-substTyp-weakenTyp1-inv : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (T ‘’ (substTyp-weakenTyp (a ‘t’ b))))
      → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
    substTyp-weakenTyp1-weakenTyp : ∀ {Γ T} {A : Typ Γ} {B : Typ Γ}
      → {a : Term {Γ = Γ ▻ T} (W {Γ = Γ} {A = T} B)}
      → Term {Γ = Γ ▻ T} (W1 (W A) ‘’ a)
      → Term {Γ = Γ ▻ T} (W A)
    substTyp3-substTyp2-substTyp1-substTyp-weakenTyp : ∀ {Γ A B C D T T'} {a : Term {Γ = Γ} A} {b : Term {Γ = Γ} (B ‘’ a)} {c : Term {Γ = Γ} (C ‘’₁ a ‘’ b)}
         {d : Term {Γ = (Γ ▻ T')} (W (D ‘’₂ a ‘’₁ b ‘’ c))}
         → Term {Γ = (Γ ▻ T')} (W1 (W T ‘’₃ a ‘’₂ b ‘’₁ c) ‘’ d)
         → Term {Γ = (Γ ▻ T')} (W (T ‘’₂ a ‘’₁ b ‘’ c))
    weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 : ∀ {Γ A B C T T'} {a : Term {Γ = Γ} A} {b : Term (B ‘’ a)} {c : Term (C ‘’ a)}
      → Term {Γ = (Γ ▻ T')} (W (W1 T ‘’₂ a ‘’₁ b ‘’ substTyp1-substTyp-weakenTyp-inv c))
      → Term {Γ = (Γ ▻ T')} (W (T ‘’₁ a ‘’ c))
    substTyp1-substTyp-tProd : ∀ {Γ T T' A B a b} → Term ((_‘→’_ {Γ = Γ ▻ T ▻ T'} A B) ‘’₁ a ‘’ b) → Term (_‘→’_ {Γ = Γ} (A ‘’₁ a ‘’ b) (B ‘’₂ a ‘’₁ b))
    substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp : ∀ {Γ A} {T : Typ (Γ ▻ A)} {T' C B} {a : Term {Γ = Γ} A} {b : Term {Γ = (Γ ▻ C ‘’ a)} (B ‘’₁ a)}
         {c : Term {Γ = (Γ ▻ T')} (W (C ‘’ a))}
         → Term {Γ = (Γ ▻ T')} (W1 (W (W T) ‘’₂ a ‘’ b) ‘’ c)
         → Term {Γ = (Γ ▻ T')} (W (T ‘’ a))
    substTyp1-substTyp-weakenTyp2-weakenTyp : ∀ {Γ T' A B T} {a : Term {Γ ▻ T'} (W A)} {b : Term {Γ ▻ T'} (W1 B ‘’ a)}
      → Term {Γ ▻ T'} (W2 (W T) ‘’₁ a ‘’ b)
      → Term {Γ ▻ T'} (W1 T ‘’ a)
    weakenTyp-weakenTyp1-weakenTyp : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W1 (W D))) → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W (W D)))
    ‘proj₁'’ : ∀ {Γ} {T : Typ Γ} {P : Typ (Γ ▻ T)} → Term (‘Σ'’ T P ‘→’ W T)
    ‘proj₂'’ : ∀ {Γ} {T : Typ Γ} {P : Typ (Γ ▻ T)} → Term {Γ ▻ ‘Σ'’ T P} (W1 P ‘’ substTyp-weakenTyp (‘λ∙’ (weakenTyp1-weakenTyp (substTyp-weakenTyp1-VAR₀ (weakenTyp-tProd (w (weakenTyp-tProd (w ‘proj₁'’))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’))
    ‘existT'’ : ∀ {Γ T P} (x : Term T) (p : Term (P ‘’ x)) → Term (‘Σ'’ {Γ} T P)

-}

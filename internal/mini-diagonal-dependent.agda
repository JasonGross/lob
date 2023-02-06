{-# OPTIONS --without-K #-}
module mini-diagonal-dependent where
open import common hiding (_~_; eqv; refl~)

infixl 2 _▻_
infixl 3 _‘’_
infixl 3 _‘’w_
infixr 1 _‘→’_
infixl 3 _‘’ₐ_
infixr 1 _~_
infixr 1 _‘~’_

record _~_ (A B : Set) : Set where
  constructor eqv
  field
    fwd : A → B
    bak : B → A
    -- TODO: eq

refl~ : ∀ {A : Set} → A ~ A
refl~ = eqv (λ x → x) (λ x → x)

mutual
  data Context : Set where
    ε : Context
    _▻_ : (Γ : Context) → Type Γ → Context

  data Type : Context → Set where
    _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
    _‘’₁_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term A) → Type (Γ ▻ (B ‘’ a))
    ‘Type’ : ∀ {Γ} → Type Γ
    ‘Term’ : ∀ {Γ} → Type (Γ ▻ ‘Type’)
    _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
    ‘⊤’ : ∀ {Γ} → Type Γ
    ‘⊥’ : ∀ {Γ} → Type Γ
    _‘~’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
    wk₀ : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
    wk₁‘Term’_‘var₀’ : Type (ε ▻ ‘Type’) → Type (ε ▻ ‘Type’)
    wk₂‘Term’‘var₁’‘~’wk₂wk₂_‘’₁⌜var₁⌝‘’var₀ : ∀ {H} → Type (ε ▻ ‘Type’ ▻ H)
      → Type (ε ▻ ‘Type’ ▻ wk₁‘Term’ H ‘var₀’)
    ‘Δ’ : ∀ (H : Type (ε ▻ ‘Type’)) (T : Type (ε ▻ ‘Type’ ▻ H))
          → Term {ε ▻ ‘Type’ ▻ (wk₁‘Term’ H ‘var₀’) ▻ (wk₂‘Term’‘var₁’‘~’wk₂wk₂ T ‘’₁⌜var₁⌝‘’var₀)} (wk₀ (wk₀ H))
          → Type ε

  data Term : {Γ : Context} → Type Γ → Set where
    ⌜_⌝ : Type ε → Term {ε} ‘Type’
    _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
    _‘’w_ : ∀ {Γ A B} → Term {Γ ▻ A} (wk₀ B) → Term A → Term B
    _‘’w₁_ : ∀ {Γ A B C} → Term {Γ ▻ A ▻ B} (wk₀ (wk₀ C)) → (a : Term A) → Term {Γ ▻ B ‘’ a} (wk₀ C)
    _‘’t₂_ : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ B ▻ C} (wk₀ (wk₀ D)) → (a : Term A) → Term {Γ ▻ B ‘’ a ▻ C ‘’₁ a} (wk₀ (wk₀ (D ‘’ a)))
    ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
    ‘eqv’ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term (B ‘→’ A) → Term (A ‘~’ B)
    ‘fwd’ : ∀ {Γ A B} → Term {Γ} (A ‘~’ B) → Term (A ‘→’ B)
    ‘bak’ : ∀ {Γ A B} → Term {Γ} (A ‘~’ B) → Term (B ‘→’ A)
    ‘‘δ-h’’ : ∀ (H : Type (ε ▻ ‘Type’)) (T : Type (ε ▻ ‘Type’ ▻ H))
                (h : Term {ε ▻ ‘Type’ ▻ (wk₁‘Term’ H ‘var₀’) ▻ (wk₂‘Term’‘var₁’‘~’wk₂wk₂ T ‘’₁⌜var₁⌝‘’var₀)} (wk₀ (wk₀ H)))
              → Term (wk₁‘Term’ H ‘var₀’ ‘’ ⌜ ‘Δ’ H T h ⌝)
    ‘‘δ’’ : ∀ (H : Type (ε ▻ ‘Type’)) (T : Type (ε ▻ ‘Type’ ▻ H))
              (h : Term {ε ▻ ‘Type’ ▻ (wk₁‘Term’ H ‘var₀’) ▻ (wk₂‘Term’‘var₁’‘~’wk₂wk₂ T ‘’₁⌜var₁⌝‘’var₀)} (wk₀ (wk₀ H)))
            → Term (wk₂‘Term’‘var₁’‘~’wk₂wk₂ T ‘’₁⌜var₁⌝‘’var₀ ‘’₁ ⌜ ‘Δ’ H T h ⌝ ‘’ (‘‘δ-h’’ H T h))
    ‘δ’ : ∀ H T h → Term {ε} ((‘Δ’ H T h) ‘~’ (T ‘’₁ ⌜ ‘Δ’ H T h ⌝ ‘’ (((h ‘’t₂ ⌜ ‘Δ’ H T h ⌝) ‘’w₁ (‘‘δ-h’’ H T h)) ‘’w (‘‘δ’’ H T h))))

max-level : Level
max-level = lzero

mutual
  Context⇓ : (Γ : Context) → Set (lsuc max-level)
  Context⇓ ε = ⊤
  Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

  Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
  Type⇓ (‘Type’ {Γ}) Γ⇓ = Lifted (Type Γ)
  Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
  Type⇓ (T ‘’₁ x) Γ⇓ = Type⇓ T ((Σ.proj₁ Γ⇓ , Term⇓ x (Σ.proj₁ Γ⇓)) , Σ.proj₂ Γ⇓)
  Type⇓ (‘Term’ {Γ}) Γ⇓ = Lifted (Term {Γ} (lower (Σ.proj₂ Γ⇓)))
  Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
  Type⇓ ‘⊤’ Γ⇓ = ⊤
  Type⇓ ‘⊥’ Γ⇓ = ⊥
  Type⇓ (A ‘~’ B) Γ⇓ = Type⇓ A Γ⇓ ~ Type⇓ B Γ⇓
  Type⇓ (wk₀ T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
  Type⇓ wk₁‘Term’ T ‘var₀’ Γ⇓ = Term (T ‘’ ⌜ lower (Σ.proj₂ Γ⇓) ⌝)
  Type⇓ wk₂‘Term’‘var₁’‘~’wk₂wk₂ T ‘’₁⌜var₁⌝‘’var₀ Γ⇓ =
    Term (lower (Σ.proj₂ (Σ.proj₁ Γ⇓)) ‘~’ (T ‘’₁ ⌜ lower (Σ.proj₂ (Σ.proj₁ Γ⇓)) ⌝ ‘’ Σ.proj₂ Γ⇓))
  Type⇓ (‘Δ’ H T h) Γ⇓ = Type⇓ T ((Γ⇓ , lift (‘Δ’ H T h)) , Term⇓ h (((Γ⇓ , lift (‘Δ’ H T h)) , _) , ‘δ’ H T h))

  Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓
  Term⇓ ⌜ x ⌝ Γ⇓ = lift x
  Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
  Term⇓ ‘tt’ Γ⇓ = tt
  Term⇓ (‘eqv’ f b) Γ⇓ = eqv (Term⇓ f Γ⇓) (Term⇓ b Γ⇓)
  Term⇓ (‘fwd’ e) Γ⇓ = let open _~_ in Term⇓ e Γ⇓ .fwd
  Term⇓ (‘bak’ e) Γ⇓ = let open _~_ in Term⇓ e Γ⇓ .bak
  Term⇓ (f ‘’w x) Γ⇓ = Term⇓ f (Γ⇓ , Term⇓ x Γ⇓)
  Term⇓ (f ‘’w₁ x) Γ⇓ = Term⇓ f ((Σ.proj₁ Γ⇓ , Term⇓ x (Σ.proj₁ Γ⇓)) , Σ.proj₂ Γ⇓)
  Term⇓ (f ‘’t₂ x) Γ⇓ = Term⇓ f (((Σ.proj₁ (Σ.proj₁ Γ⇓) , Term⇓ x (Σ.proj₁ (Σ.proj₁ Γ⇓))) , Σ.proj₂ (Σ.proj₁ Γ⇓)) , Σ.proj₂ Γ⇓)
  Term⇓ (‘‘δ-h’’ H T h) Γ⇓ = (((h ‘’t₂ ⌜ ‘Δ’ H T h ⌝) ‘’w₁ (‘‘δ-h’’ H T h)) ‘’w (‘‘δ’’ H T h))
  Term⇓ (‘‘δ’’ H T h) Γ⇓ = ‘δ’ H T h
  Term⇓ (‘δ’ H T h) Γ⇓ = refl~

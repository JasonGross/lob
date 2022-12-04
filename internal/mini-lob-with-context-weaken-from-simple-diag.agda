{-# OPTIONS --without-K #-}
module mini-lob-with-context-weaken-from-diag where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixl 3 _‘’₁_
infixr 1 _‘→’_
infixl 3 _‘’ₐ_

mutual
  data Context : Set where
    ε : Context
    _▻_ : (Γ : Context) → Type Γ → Context

  data Type : Context → Set where
    _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
    _‘’₁_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
    wkT : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
    ‘Context’ : ∀ {Γ} → Type Γ
    ‘Type’ : ∀ {Γ} → Type (Γ ▻ ‘Context’)
    ‘Term’ : ∀ {Γ} → Type (Γ ▻ ‘Context’ ▻ ‘Type’)
    _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
    ‘⊤’ : ∀ {Γ} → Type Γ
    ‘⊥’ : ∀ {Γ} → Type Γ
    ‘Set’ : ∀ {Γ} → Type Γ
    ‘Δ→Type’ : ∀ {Γ} → Type Γ

  data Term : {Γ : Context} → Type Γ → Set where
    ⌜_⌝c : ∀ {Γ} → Context → Term {Γ} ‘Context’
    ⌜_⌝ : ∀ {Γ C} → Type C → Term {Γ} (‘Type’ ‘’ ⌜ C ⌝c)
    _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
    wk : ∀ {Γ A T} → Term {Γ} T → Term {Γ ▻ A} (wkT T)
    ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
    wrap : ∀ {Γ} → Term {Γ ▻ ‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ ‘Δ→Type’ ⌝} ‘Set’ → Term {Γ} ‘Δ→Type’
    unwrap : ∀ {Γ} → Term {Γ} ‘Δ→Type’ → Term {Γ ▻ ‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ ‘Δ→Type’ ⌝} ‘Set’

Lӧb : ∀ {Γ} {X : Type Γ} → Term {Γ} (‘Term’ ‘’₁ _ ‘’ ⌜ X ⌝ ‘→’ X) → Term {Γ} X
Lӧb {Γ} {X} f = {! !}
  where
    K : Term {Γ} ‘Δ→Type’
    K = {!!}


max-level : Level
max-level = lsuc lzero

Context⇓ : (Γ : Context) → Set max-level
Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level

Context⇓ ε = ⊤
Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓

Type⇓ ‘Context’ Γ⇓ = Lifted Context
Type⇓ ‘Set’ Γ⇓ = Set
Type⇓ (T ‘’ a) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ a Γ⇓)
Type⇓ ‘Type’ Γ⇓ = Lifted (Type (lower (Σ.proj₂ Γ⇓)))
-- Swapping the above two lines causes the following line to error with
{- /home/jgross/Documents/GitHub/lob/internal/mini-lob-with-context.agda:50,67-77
Γ != Γ ▻ A of type Context
when checking that the expression Σ.proj₂ Γ⇓ has type
Type⇓ B (Σ.proj₁ Γ⇓ , Term⇓ a (Σ.proj₁ Γ⇓)) -}
Type⇓ (T ‘’₁ a) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓ , Term⇓ a (Σ.proj₁ Γ⇓) , Σ.proj₂ Γ⇓)
Type⇓ ‘Term’ Γ⇓ = Lifted (Term (lower (Σ.proj₂ Γ⇓)))
Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
Type⇓ ‘⊤’ Γ⇓ = ⊤
Type⇓ ‘⊥’ Γ⇓ = ⊥
Type⇓ (wkT T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
Type⇓ {Γ} ‘Δ→Type’ Γ⇓ = Term {Γ} ‘Δ→Type’ → Set

Term⇓ ⌜ C ⌝c Γ⇓ = lift C
Term⇓ ⌜ T ⌝ Γ⇓ = lift T
Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
--Term⇓ (Lӧb □‘X’→X) Γ⇓ = Term⇓ □‘X’→X Γ⇓ (lift (Lӧb □‘X’→X))
Term⇓ ‘tt’ Γ⇓ = tt
Term⇓ (wk t) Γ⇓ = Term⇓ t (Σ.proj₁ Γ⇓)
Term⇓ (wrap f) Γ⇓ x = Term⇓ f (Γ⇓ , lift x)
Term⇓ (unwrap f) Γ⇓ = Term⇓ f (Σ.proj₁ Γ⇓) (lower (Σ.proj₂ Γ⇓))

⌞_⌟ : Type ε → Set _
⌞ T ⌟ = Type⇓ T tt

‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
‘¬’ T = T ‘→’ ‘⊥’

□ : Type ε → Set _
□ = Term {ε}

‘□’ : ∀ {Γ C} → Type (Γ ▻ ‘Type’ ‘’ C)
‘□’ {Γ} {C} = ‘Term’ ‘’₁ C

lӧb : ∀ {‘X’} → □ (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = Term⇓ (Lӧb f) tt

incompleteness : ¬ □ (‘¬’ (‘□’ ‘’ ⌜ ‘⊥’ {ε} ⌝))
incompleteness pf = ⊥-elim (lӧb pf)

soundness : ¬ □ ‘⊥’
soundness x = ⊥-elim (Term⇓ x tt)

non-emptyness : Σ (Type ε) (λ T → □ T)
non-emptyness = ‘⊤’ , ‘tt’

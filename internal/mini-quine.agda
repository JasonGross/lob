{-# OPTIONS --without-K #-}
module mini-quine where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixr 1 _‘→’_
infixl 3 _‘’ₐ_
infixl 3 _w‘‘’’ₐ_
infixr 2 _‘∘’_

mutual
  data Context : Set where
    ε : Context
    _▻_ : (Γ : Context) → Type Γ → Context

  data Type : Context → Set where
    W : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
    W1 : ∀ {Γ A B} → Type (Γ ▻ B) → Type (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B))
    _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
    ‘Typeε’ : ∀ {Γ} → Type Γ
    ‘□’ : ∀ {Γ} → Type (Γ ▻ ‘Typeε’)
    _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
    Quine : Type (ε ▻ ‘Typeε’) → Type ε
    ‘⊤’ : ∀ {Γ} → Type Γ
    ‘⊥’ : ∀ {Γ} → Type Γ

  data Term : {Γ : Context} → Type Γ → Set where
    ⌜_⌝ : ∀ {Γ} → Type ε → Term {Γ} ‘Typeε’
    ⌜_⌝t : ∀ {Γ T} → Term {ε} T → Term {Γ} (‘□’ ‘’ ⌜ T ⌝)
    ‘⌜‘VAR₀’⌝t’ : ∀ {T} → Term {ε ▻ ‘□’ ‘’ ⌜ T ⌝} (W (‘□’ ‘’ ⌜ ‘□’ ‘’ ⌜ T ⌝ ⌝))
    ‘λ∙’ : ∀ {Γ A B} → Term {Γ ▻ A} (W B) → Term {Γ} (A ‘→’ B)
    ‘VAR₀’ : ∀ {Γ T} → Term {Γ ▻ T} (W T)
    _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
    quine→ : ∀ {φ} → Term {ε} (Quine φ        ‘→’ φ ‘’ ⌜ Quine φ ⌝)
    quine← : ∀ {φ} → Term {ε} (φ ‘’ ⌜ Quine φ ⌝ ‘→’ Quine φ)
    ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
    →SW1SV→W : ∀ {Γ T X A B} {x : Term X}
      → Term {Γ} (T ‘→’ (W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x)
      → Term {Γ} (T ‘→’ A ‘’ x ‘→’ B)
    ←SW1SV→W : ∀ {Γ T X A B} {x : Term X}
      → Term {Γ} ((W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T)
      → Term {Γ} ((A ‘’ x ‘→’ B) ‘→’ T)
    w : ∀ {Γ A T} → Term {Γ} A → Term {Γ ▻ T} (W A)
    w→ : ∀ {Γ A B X} → Term {Γ} (A ‘→’ B) → Term {Γ ▻ X} (W A ‘→’ W B)
    _‘∘’_ : ∀ {Γ A B C} → Term {Γ} (B ‘→’ C) → Term {Γ} (A ‘→’ B) → Term {Γ} (A ‘→’ C)
    _w‘‘’’ₐ_ : ∀ {A B T} → Term {ε ▻ T} (W (‘□’ ‘’ ⌜ A ‘→’ B ⌝)) → Term {ε ▻ T} (W (‘□’ ‘’ ⌜ A ⌝)) → Term {ε ▻ T} (W (‘□’ ‘’ ⌜ B ⌝))


□ : Type ε → Set _
□ = Term {ε}

max-level : Level
max-level = lzero

mutual
  Context⇓ : (Γ : Context) → Set (lsuc max-level)
  Context⇓ ε = ⊤
  Context⇓ (Γ ▻ T) = Σ (Type⇓ {Γ} T)

  Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
  Type⇓ (W T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
  Type⇓ (W1 T) Γ⇓ = Type⇓ T ((Σ.proj₁ (Σ.proj₁ Γ⇓)) , (Σ.proj₂ Γ⇓))
  Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
  Type⇓ ‘Typeε’ Γ⇓ = Lifted (Type ε)
  Type⇓ ‘□’ Γ⇓ = Lifted (Term {ε} (lower (Σ.proj₂ Γ⇓)))
  Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
  Type⇓ ‘⊤’ Γ⇓ = ⊤
  Type⇓ ‘⊥’ Γ⇓ = ⊥
  Type⇓ (Quine φ) Γ⇓ = Type⇓ φ (Γ⇓ , (lift (Quine φ)))

  Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓
  Term⇓ ⌜ x ⌝ Γ⇓ = lift x
  Term⇓ ⌜ x ⌝t Γ⇓ = lift x
  Term⇓ ‘⌜‘VAR₀’⌝t’ Γ⇓ = lift ⌜ (lower (Σ.proj₂ Γ⇓)) ⌝t
  Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
  Term⇓ ‘tt’ Γ⇓ = tt
  Term⇓ (quine→ {φ}) Γ⇓ x = x
  Term⇓ (quine← {φ}) Γ⇓ x = x
  Term⇓ (‘λ∙’ f) Γ⇓ x = Term⇓ f (Γ⇓ , x)
  Term⇓ ‘VAR₀’ Γ⇓ = Σ.proj₂ Γ⇓
  Term⇓ (←SW1SV→W f) = Term⇓ f
  Term⇓ (→SW1SV→W f) = Term⇓ f
  Term⇓ (w x) Γ⇓ = Term⇓ x (Σ.proj₁ Γ⇓)
  Term⇓ (w→ f) Γ⇓ = Term⇓ f (Σ.proj₁ Γ⇓)
  Term⇓ (g ‘∘’ f) Γ⇓ x = Term⇓ g Γ⇓ (Term⇓ f Γ⇓ x)
  Term⇓ (f w‘‘’’ₐ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ₐ lower (Term⇓ x Γ⇓))

module inner (‘X’ : Type ε) (‘f’ : Term {ε} (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’)) where
  ‘H’ : Type ε
  ‘H’ = Quine (W1 ‘□’ ‘’ ‘VAR₀’ ‘→’ W ‘X’)

  ‘toH’ : □ ((‘□’ ‘’ ⌜ ‘H’ ⌝ ‘→’ ‘X’) ‘→’ ‘H’)
  ‘toH’ = ←SW1SV→W quine←

  ‘fromH’ : □ (‘H’ ‘→’ (‘□’ ‘’ ⌜ ‘H’ ⌝ ‘→’ ‘X’))
  ‘fromH’ = →SW1SV→W quine→

  ‘□‘H’→□‘X’’ : □ (‘□’ ‘’ ⌜ ‘H’ ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘X’ ⌝)
  ‘□‘H’→□‘X’’ = ‘λ∙’ (w ⌜ ‘fromH’ ⌝t w‘‘’’ₐ ‘VAR₀’ w‘‘’’ₐ ‘⌜‘VAR₀’⌝t’)

  ‘h’ : Term ‘H’
  ‘h’ = ‘toH’ ‘’ₐ (‘f’ ‘∘’ ‘□‘H’→□‘X’’)

  Lӧb : □ ‘X’
  Lӧb = ‘fromH’ ‘’ₐ ‘h’ ‘’ₐ ⌜ ‘h’ ⌝t

Lӧb : ∀ {X} → Term {ε} (‘□’ ‘’ ⌜ X ⌝ ‘→’ X) → Term {ε} X
Lӧb {X} f = inner.Lӧb X f

⌞_⌟ : Type ε → Set _
⌞ T ⌟ = Type⇓ T tt

‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
‘¬’ T = T ‘→’ ‘⊥’

lӧb : ∀ {‘X’} → □ (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = Term⇓ (Lӧb f) tt

incompleteness : ¬ □ (‘¬’ (‘□’ ‘’ ⌜ ‘⊥’ ⌝))
incompleteness = lӧb

soundness : ¬ □ ‘⊥’
soundness x = Term⇓ x tt

non-emptyness : Σ (λ T → □ T)
non-emptyness = ‘⊤’ , ‘tt’

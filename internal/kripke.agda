-- {-# OPTIONS --without-K #-}
module kripke where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixr 1 _‘→’_
infixr 1 _‘‘→’’_
infixr 1 _ww‘‘‘→’’’_
infixl 3 _‘’ₐ_
infixl 3 _w‘‘’’ₐ_
infixr 2 _‘∘’_
infixr 2 _‘×’_
infixr 2 _‘‘×’’_
infixr 2 _w‘‘×’’_

mutual
  data Context : Set where
    ε : Context
    _▻_ : (Γ : Context) → Type Γ → Context

  data Type : Context → Set where
    W : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
    W1 : ∀ {Γ A B} → Type (Γ ▻ B) → Type (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B))
    _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
    ‘Type’ : ∀ Γ → Type Γ
    ‘Term’ : ∀ {Γ} → Type (Γ ▻ ‘Type’ Γ)
    _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
    _‘×’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
    Quine : ∀ {Γ} → Type (Γ ▻ ‘Type’ Γ) → Type Γ
    ‘⊤’ : ∀ {Γ} → Type Γ
    ‘⊥’ : ∀ {Γ} → Type Γ

  data Term : {Γ : Context} → Type Γ → Set where
    ⌜_⌝ : ∀ {Γ} → Type Γ → Term {Γ} (‘Type’ Γ)
    ⌜_⌝t : ∀ {Γ T} → Term {Γ} T → Term {Γ} (‘Term’ ‘’ ⌜ T ⌝)
    ‘⌜‘VAR₀’⌝t’ : ∀ {Γ T} → Term {Γ ▻ ‘Term’ ‘’ ⌜ T ⌝} (W (‘Term’ ‘’ ⌜ ‘Term’ ‘’ ⌜ T ⌝ ⌝))
    ‘⌜‘VAR₀’⌝’ : ∀ {Γ} → Term {Γ ▻ ‘Type’ Γ} (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))
    ‘λ∙’ : ∀ {Γ A B} → Term {Γ ▻ A} (W B) → Term {Γ} (A ‘→’ B)
    ‘VAR₀’ : ∀ {Γ T} → Term {Γ ▻ T} (W T)
    _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
    ‘‘×'’’ : ∀ {Γ} → Term {Γ} (‘Type’ Γ ‘→’ ‘Type’ Γ ‘→’ ‘Type’ Γ)
    quine→ : ∀ {Γ φ} → Term {Γ} (Quine φ        ‘→’ φ ‘’ ⌜ Quine φ ⌝)
    quine← : ∀ {Γ φ} → Term {Γ} (φ ‘’ ⌜ Quine φ ⌝ ‘→’ Quine φ)
    ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
    SW : ∀ {Γ X A} {a : Term A} → Term {Γ} (W X ‘’ a) → Term X
    →SW1SV→W : ∀ {Γ T X A B} {x : Term X}
      → Term {Γ} (T ‘→’ (W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x)
      → Term {Γ} (T ‘→’ A ‘’ x ‘→’ B)
    ←SW1SV→W : ∀ {Γ T X A B} {x : Term X}
      → Term {Γ} ((W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T)
      → Term {Γ} ((A ‘’ x ‘→’ B) ‘→’ T)
    →SW1SV→SW1SV→W : ∀ {Γ T X A B} {x : Term X}
      → Term {Γ} (T ‘→’ (W1 A ‘’ ‘VAR₀’ ‘→’ W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x)
      → Term {Γ} (T ‘→’ A ‘’ x ‘→’ A ‘’ x ‘→’ B)
    ←SW1SV→SW1SV→W : ∀ {Γ T X A B} {x : Term X}
      → Term {Γ} ((W1 A ‘’ ‘VAR₀’ ‘→’ W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T)
      → Term {Γ} ((A ‘’ x ‘→’ A ‘’ x ‘→’ B) ‘→’ T)
    w : ∀ {Γ A T} → Term {Γ} A → Term {Γ ▻ T} (W A)
    w→ : ∀ {Γ A B X} → Term {Γ ▻ X} (W (A ‘→’ B)) → Term {Γ ▻ X} (W A ‘→’ W B)
    →w : ∀ {Γ A B X} → Term {Γ ▻ X} (W A ‘→’ W B) → Term {Γ ▻ X} (W (A ‘→’ B))
    ww→ : ∀ {Γ A B X Y} → Term {Γ ▻ X ▻ Y} (W (W (A ‘→’ B))) → Term {Γ ▻ X ▻ Y} (W (W A) ‘→’ W (W B))
    →ww : ∀ {Γ A B X Y} → Term {Γ ▻ X ▻ Y} (W (W A) ‘→’ W (W B)) → Term {Γ ▻ X ▻ Y} (W (W (A ‘→’ B)))
    _‘∘’_ : ∀ {Γ A B C} → Term {Γ} (B ‘→’ C) → Term {Γ} (A ‘→’ B) → Term {Γ} (A ‘→’ C)
    _w‘‘’’ₐ_ : ∀ {Γ A B T} → Term {Γ ▻ T} (W (‘Term’ ‘’ ⌜ A ‘→’ B ⌝)) → Term {Γ ▻ T} (W (‘Term’ ‘’ ⌜ A ⌝)) → Term {Γ ▻ T} (W (‘Term’ ‘’ ⌜ B ⌝))
    ‘‘’ₐ’ : ∀ {Γ A B} → Term {Γ} (‘Term’ ‘’ ⌜ A ‘→’ B ⌝ ‘→’ ‘Term’ ‘’ ⌜ A ⌝ ‘→’ ‘Term’ ‘’ ⌜ B ⌝)
    -- _w‘‘’’_ : ∀ {Γ A B T} → Term {Γ ▻ T} (‘Type’ (Γ ▻ T)) → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ T ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Type’ Γ)))
    ‘‘□’’ : ∀ {Γ A B} → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Type’ Γ)))
    -- ‘‘’’' : ∀ {Γ A} → Term {Γ ▻ A} (‘Type’ (Γ ▻ A) ‘→’ W (‘Term’ ‘’ ⌜ A ⌝) ‘→’ W (‘Type’ Γ))
    _‘‘→’’_ : ∀ {Γ} → Term {Γ} (‘Type’ Γ) → Term {Γ} (‘Type’ Γ) → Term {Γ} (‘Type’ Γ)
    _ww‘‘‘→’’’_ : ∀ {Γ A B} → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝)))
    _ww‘‘‘×’’’_ : ∀ {Γ A B} → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝)))

□ : Type ε → Set _
□ = Term {ε}

‘□’ : ∀ {Γ} → Type Γ → Type Γ
‘□’ T = ‘Term’ ‘’ ⌜ T ⌝

_‘‘×’’_ : ∀ {Γ} → Term {Γ} (‘Type’ Γ) → Term {Γ} (‘Type’ Γ) → Term {Γ} (‘Type’ Γ)
A ‘‘×’’ B = ‘‘×'’’ ‘’ₐ A ‘’ₐ B

max-level : Level
max-level = lzero

Context⇓ : (Γ : Context) → Set (lsuc max-level)
Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓

Context⇓ ε = ⊤
Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

Type⇓-‘Term’ : ∀ {Γ} → Context⇓ (Γ ▻ ‘Type’ Γ) → Set max-level
Type⇓-Quine : ∀ {Γ} (ϕ : Type (Γ ▻ ‘Type’ Γ)) → Context⇓ Γ → Set max-level

Type⇓ (W T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
Type⇓ (W1 T) Γ⇓ = Type⇓ T ((Σ.proj₁ (Σ.proj₁ Γ⇓)) , (Σ.proj₂ Γ⇓))
Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
Type⇓ (‘Type’ Γ) Γ⇓ = Lifted (Type Γ)
Type⇓ ‘Term’ Γ⇓ = Type⇓-‘Term’ Γ⇓
Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
Type⇓ (A ‘×’ B) Γ⇓ = Type⇓ A Γ⇓ × Type⇓ B Γ⇓
Type⇓ ‘⊤’ Γ⇓ = ⊤
Type⇓ ‘⊥’ Γ⇓ = ⊥
Type⇓ (Quine φ) Γ⇓ = Type⇓-Quine φ Γ⇓

Type⇓-‘Term’ Γ⇓ = Lifted (Term ((lower (Σ.proj₂ Γ⇓))))
Type⇓-Quine φ Γ⇓ = Type⇓ φ (Γ⇓ , lift (Quine φ))

Term⇓-→SW1SV→W : ∀ {Γ T X A B} {x : Term X}
      → (f : Term {Γ} (T ‘→’ (W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x))
      → ∀ Γ⇓ → Type⇓ (T ‘→’ A ‘’ x ‘→’ B) Γ⇓
Term⇓-←SW1SV→W : ∀ {Γ T X A B} {x : Term X}
      → (f : Term {Γ} ((W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T))
      → ∀ Γ⇓ → Type⇓ ((A ‘’ x ‘→’ B) ‘→’ T) Γ⇓
Term⇓-→SW1SV→SW1SV→W : ∀ {Γ T X A B} {x : Term X}
      → (f : Term {Γ} (T ‘→’ (W1 A ‘’ ‘VAR₀’ ‘→’ W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x))
      → ∀ Γ⇓ → Type⇓ (T ‘→’ A ‘’ x ‘→’ A ‘’ x ‘→’ B) Γ⇓
Term⇓-←SW1SV→SW1SV→W : ∀ {Γ T X A B} {x : Term X}
      → (f : Term {Γ} ((W1 A ‘’ ‘VAR₀’ ‘→’ W1 A ‘’ ‘VAR₀’ ‘→’ W B) ‘’ x ‘→’ T))
      → ∀ Γ⇓ → Type⇓ ((A ‘’ x ‘→’ A ‘’ x ‘→’ B) ‘→’ T) Γ⇓


Term⇓ ⌜ x ⌝ Γ⇓ = lift x
Term⇓ ⌜ x ⌝t Γ⇓ = lift x
Term⇓ ‘⌜‘VAR₀’⌝t’ Γ⇓ = lift ⌜ (lower (Σ.proj₂ Γ⇓)) ⌝t
Term⇓ ‘⌜‘VAR₀’⌝’ Γ⇓ = lift ⌜ (lower (Σ.proj₂ Γ⇓)) ⌝
Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
Term⇓ ‘tt’ Γ⇓ = tt
Term⇓ (quine→ {φ}) Γ⇓ x = x
Term⇓ (quine← {φ}) Γ⇓ x = x
Term⇓ (‘λ∙’ f) Γ⇓ x = Term⇓ f (Γ⇓ , x)
Term⇓ ‘VAR₀’ Γ⇓ = Σ.proj₂ Γ⇓
Term⇓ (SW t) = Term⇓ t
Term⇓ (w x) Γ⇓ = Term⇓ x (Σ.proj₁ Γ⇓)
Term⇓ (w→ f) Γ⇓ = Term⇓ f Γ⇓
Term⇓ (→w f) Γ⇓ = Term⇓ f Γ⇓
Term⇓ (ww→ f) Γ⇓ = Term⇓ f Γ⇓
Term⇓ (→ww f) Γ⇓ = Term⇓ f Γ⇓
Term⇓ ‘‘×'’’ Γ⇓ A B = lift (lower A ‘×’ lower B)
Term⇓ (g ‘∘’ f) Γ⇓ x = Term⇓ g Γ⇓ (Term⇓ f Γ⇓ x)
Term⇓ (f w‘‘’’ₐ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ₐ lower (Term⇓ x Γ⇓))
Term⇓ ‘‘’ₐ’ Γ⇓ f x = lift (lower f ‘’ₐ lower x)
-- Term⇓ (f w‘‘’’ x) Γ⇓ = lift {!!} --(lower (Term⇓ f Γ⇓) ‘’ lower (Term⇓ x Γ⇓))
Term⇓ (‘‘□’’ {Γ} T) Γ⇓ = lift (‘Term’ ‘’ lower (Term⇓ T Γ⇓))
Term⇓ (A ‘‘→’’ B) Γ⇓ = lift ((lower (Term⇓ A Γ⇓)) ‘→’ (lower (Term⇓ B Γ⇓)))
Term⇓ (A ww‘‘‘→’’’ B) Γ⇓ = lift ((lower (Term⇓ A Γ⇓)) ‘‘→’’ (lower (Term⇓ B Γ⇓)))
Term⇓ (A ww‘‘‘×’’’ B) Γ⇓ = lift ((lower (Term⇓ A Γ⇓)) ‘‘×’’ (lower (Term⇓ B Γ⇓)))
Term⇓ (←SW1SV→W f) = Term⇓-←SW1SV→W f
Term⇓ (→SW1SV→W f) = Term⇓-→SW1SV→W f
Term⇓ (←SW1SV→SW1SV→W f) = Term⇓-←SW1SV→SW1SV→W f
Term⇓ (→SW1SV→SW1SV→W f) = Term⇓-→SW1SV→SW1SV→W f

Term⇓-←SW1SV→W f = Term⇓ f
Term⇓-→SW1SV→W f = Term⇓ f
Term⇓-←SW1SV→SW1SV→W f = Term⇓ f
Term⇓-→SW1SV→SW1SV→W f = Term⇓ f


module inner (‘X’ : Type ε) (‘f’ : Term {ε} (‘□’ ‘X’ ‘→’ ‘X’)) where
  ‘H’ : Type ε
  ‘H’ = Quine (W1 ‘Term’ ‘’ ‘VAR₀’ ‘→’ W ‘X’)

  ‘toH’ : □ ((‘□’ ‘H’ ‘→’ ‘X’) ‘→’ ‘H’)
  ‘toH’ = ←SW1SV→W quine←

  ‘fromH’ : □ (‘H’ ‘→’ (‘□’ ‘H’ ‘→’ ‘X’))
  ‘fromH’ = →SW1SV→W quine→

  ‘□‘H’→□‘X’’ : □ (‘□’ ‘H’ ‘→’ ‘□’ ‘X’)
  ‘□‘H’→□‘X’’ = ‘λ∙’ (w ⌜ ‘fromH’ ⌝t w‘‘’’ₐ ‘VAR₀’ w‘‘’’ₐ ‘⌜‘VAR₀’⌝t’)

  ‘h’ : Term ‘H’
  ‘h’ = ‘toH’ ‘’ₐ (‘f’ ‘∘’ ‘□‘H’→□‘X’’)

  Lӧb : □ ‘X’
  Lӧb = ‘fromH’ ‘’ₐ ‘h’ ‘’ₐ ⌜ ‘h’ ⌝t

Lӧb : ∀ {X} → Term {ε} (‘□’ X ‘→’ X) → Term {ε} X
Lӧb {X} f = inner.Lӧb X f

⌞_⌟ : Type ε → Set _
⌞ T ⌟ = Type⇓ T tt

‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
‘¬’ T = T ‘→’ ‘⊥’

_w‘‘×’’_ : ∀ {Γ X} → Term {Γ ▻ X} (W (‘Type’ Γ)) → Term {Γ ▻ X} (W (‘Type’ Γ)) → Term {Γ ▻ X} (W (‘Type’ Γ))
A w‘‘×’’ B = w→ (w→ (w ‘‘×'’’) ‘’ₐ A) ‘’ₐ B

lӧb : ∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = Term⇓ (Lӧb f) tt

incompleteness : ¬ □ (‘¬’ (‘□’ ‘⊥’))
incompleteness = lӧb

soundness : ¬ □ ‘⊥’
soundness x = Term⇓ x tt

non-emptyness : Σ (Type ε) (λ T → □ T)
non-emptyness = ‘⊤’ , ‘tt’

module helpers where
  Wₕ : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
  Wₕ ‘⊤’ = ‘⊤’
  Wₕ ‘⊥’ = ‘⊥’
  Wₕ (T ‘→’ T₂) = Wₕ T ‘→’ Wₕ T₂
  Wₕ (T ‘×’ T₂) = Wₕ T ‘×’ Wₕ T₂
  Wₕ (W T₂) = W (Wₕ T₂)
  Wₕ T = W T

  _‘’ₕ_ : ∀ {Γ A} → Type (Γ ▻ A) → Term A → Type Γ
  ‘⊤’ ‘’ₕ x₁ = ‘⊤’
  ‘⊥’ ‘’ₕ x₁ = ‘⊥’
  W f ‘’ₕ x₁ = f
  ‘Term’ ‘’ₕ ⌜ ‘⊤’ ⌝ = ‘⊤’
  (f ‘→’ f₁) ‘’ₕ x₁ = (f ‘’ₕ x₁) ‘→’ (f₁ ‘’ₕ x₁)
  (f ‘×’ f₁) ‘’ₕ x₁ = (f ‘’ₕ x₁) ‘×’ (f₁ ‘’ₕ x₁)
  f ‘’ₕ x = f ‘’ x

  _‘→’ₕ_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  ‘⊤’ ‘→’ₕ B = B
  ‘⊥’ ‘→’ₕ B = ‘⊤’
  A ‘→’ₕ ‘⊤’ = ‘⊤’
  A ‘→’ₕ B = A ‘→’ B

  _‘×’ₕ_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  ‘⊤’ ‘×’ₕ B = B
  ‘⊥’ ‘×’ₕ B = ‘⊥’
  A ‘×’ₕ ‘⊤’ = A
  A ‘×’ₕ ‘⊥’ = ‘⊥’
  A ‘×’ₕ B = A ‘×’ B

open helpers

mutual
  simplify-type : ∀ {Γ} → Type Γ → Type Γ
  simplify-type ‘⊤’ = ‘⊤’
  simplify-type ‘⊥’ = ‘⊥’
  simplify-type (T ‘→’ T₁) = simplify-type T ‘→’ₕ simplify-type T₁
  simplify-type (T ‘×’ T₁) = simplify-type T ‘×’ₕ simplify-type T₁
  simplify-type (T₁ ‘’ x) = simplify-type T₁ ‘’ₕ simplify-term x
  simplify-type (W T₁) = Wₕ (simplify-type T₁)
  simplify-type (W1 T₂) = W1ₕ (simplify-type T₂)
    where W1ₕ : ∀ {Γ A B} → Type (Γ ▻ A) → Type (Γ ▻ B ▻ W A)
          W1ₕ ‘⊤’ = ‘⊤’
          W1ₕ ‘⊥’ = ‘⊥’
          W1ₕ (T ‘→’ T₂) = W1ₕ T ‘→’ W1ₕ T₂
          W1ₕ (T ‘×’ T₂) = W1ₕ T ‘×’ W1ₕ T₂
          W1ₕ (W T₂) = W (Wₕ T₂)
          W1ₕ (W1 T₂) = W1 (W1ₕ T₂)
          W1ₕ T = W1 T
  simplify-type (‘Type’ Γ) = ‘Type’ Γ
  simplify-type ‘Term’ = ‘Term’
  simplify-type (Quine T) = Quine (simplify-type T)

  simplify-term : ∀ {Γ T} → Term {Γ} T → Term T
  simplify-term ⌜ x ⌝ = ⌜ simplify-type x ⌝
  simplify-term ⌜ t ⌝t = ⌜ simplify-term t ⌝t
  simplify-term ‘⌜‘VAR₀’⌝t’ = ‘⌜‘VAR₀’⌝t’
  simplify-term ‘⌜‘VAR₀’⌝’ = ‘⌜‘VAR₀’⌝’
  simplify-term (‘λ∙’ t) = ‘λ∙’ (simplify-term t)
  simplify-term ‘VAR₀’ = ‘VAR₀’
  simplify-term (t ‘’ₐ t₁) = simplify-term t ‘’ₐₕ simplify-term t₁
    where _‘’ₐₕ_ : ∀ {Γ A T} → Term {Γ} (A ‘→’ T) → Term A → Term T
          ‘λ∙’ ‘⌜‘VAR₀’⌝t’ ‘’ₐₕ x = ⌜ x ⌝t
          ‘λ∙’ ‘⌜‘VAR₀’⌝’ ‘’ₐₕ x = ⌜ x ⌝t
          ‘λ∙’ ‘VAR₀’ ‘’ₐₕ x = x
          ‘λ∙’ (f ‘’ₐ f₁) ‘’ₐₕ x = ‘λ∙’ (f ‘’ₐₕ f₁) ‘’ₐ x
          ‘λ∙’ (w f) ‘’ₐₕ x = f
          (f ‘’ₐ f₁) ‘’ₐₕ x = (f ‘’ₐₕ f₁) ‘’ₐ x
          (f ‘∘’ f₁) ‘’ₐₕ x = f ‘’ₐₕ (f₁ ‘’ₐₕ x)
          f ‘’ₐₕ x = f ‘’ₐ x
  simplify-term ‘‘×'’’ = ‘‘×'’’
  simplify-term quine→ = quine→
  simplify-term quine← = quine←
  simplify-term ‘tt’ = ‘tt’
  simplify-term (SW t₁) = SW (simplify-term t₁)
  simplify-term (→SW1SV→W t₁) = →SW1SV→W (simplify-term t₁)
  simplify-term (←SW1SV→W t₁) = ←SW1SV→W (simplify-term t₁)
  simplify-term (→SW1SV→SW1SV→W t₁) = →SW1SV→SW1SV→W (simplify-term t₁)
  simplify-term (←SW1SV→SW1SV→W t₁) = ←SW1SV→SW1SV→W (simplify-term t₁)
  simplify-term (w t) = w (simplify-term t)
  simplify-term (w→ t) = w→ (simplify-term t)
  simplify-term (→w t) = →w (simplify-term t)
  simplify-term (ww→ t) = ww→ (simplify-term t)
  simplify-term (→ww t) = →ww (simplify-term t)
  simplify-term (t ‘∘’ t₁) = simplify-term t ‘∘’ simplify-term t₁
  simplify-term (t w‘‘’’ₐ t₁) = simplify-term t w‘‘’’ₐ simplify-term t₁
  simplify-term ‘‘’ₐ’ = ‘‘’ₐ’
  simplify-term (‘‘□’’ t) = ‘‘□’’ (simplify-term t)
  simplify-term (t ‘‘→’’ t₁) = simplify-term t ‘‘→’’ simplify-term t₁
  simplify-term (t ww‘‘‘→’’’ t₁) = simplify-term t ww‘‘‘→’’’ simplify-term t₁
  simplify-term (t ww‘‘‘×’’’ t₁) = simplify-term t ww‘‘‘×’’’ simplify-term t₁
{-
mutual
  simplify-type⇓→ : ∀ {Γ T Γ⇓} → Type⇓ {Γ} T Γ⇓ → Type⇓ {Γ} (simplify-type T) Γ⇓
  simplify-type⇓→ {T = T ‘→’ T₁} T⇓ = {!!}
  simplify-type⇓→ {T = W T₁} T⇓ = {!!}
  simplify-type⇓→ {T = W1 T₂} T⇓ = {!!}
  simplify-type⇓→ {T = T₁ ‘’ x} T⇓ = {!!}
  simplify-type⇓→ {T = ‘Type’ ._} T⇓ = {!!}
  simplify-type⇓→ {T = ‘Term’} T⇓ = {!!}
  simplify-type⇓→ {T = T ‘×’ T₁} T⇓ = {!!}
  simplify-type⇓→ {T = Quine T} T⇓ = {!!}
  simplify-type⇓→ {T = ‘⊤’} T⇓ = tt
  simplify-type⇓→ {T = ‘⊥’} T⇓ = T⇓

  simplify-type⇓← : ∀ {Γ T Γ⇓} → Type⇓ {Γ} (simplify-type T) Γ⇓ → Type⇓ {Γ} T Γ⇓
  simplify-type⇓← {T = W T₁} T⇓ = {!!}
  simplify-type⇓← {T = W1 T₂} T⇓ = {!!}
  simplify-type⇓← {T = T₁ ‘’ x} T⇓ = {!!}
  simplify-type⇓← {T = ‘Type’ ._} T⇓ = {!!}
  simplify-type⇓← {T = ‘Term’} T⇓ = {!!}
  simplify-type⇓← {T = T ‘→’ T₁} T⇓ x = {!!}
  simplify-type⇓← {Γ} {T ‘×’ T₁} {Γ⇓} T⇓ = helper {Γ} {simplify-type T} {simplify-type T₁} {T} {T₁} {Γ⇓} (simplify-type⇓← {T = T}) (simplify-type⇓← {T = T₁}) T⇓
    where helper : ∀ {Γ A B A' B'} {Γ⇓ : Context⇓ Γ}
                 → (Type⇓ A Γ⇓ → Type⇓ A' Γ⇓)
                 → (Type⇓ B Γ⇓ → Type⇓ B' Γ⇓)
                 → Type⇓ (A ‘×’ₕ B) Γ⇓
                 → Type⇓ (A' ‘×’ B') Γ⇓
          helper {A = ‘⊤’} f g x = f tt , g x
          helper {A = ‘⊥’} f g ()
          helper {A = W A₁} {‘⊤’} f g x = f x , g tt
          helper {A = W1 A₂} {‘⊤’} f g x = f x , g tt
          helper {A = A₁ ‘’ x} {‘⊤’} f g x₁ = f x₁ , g tt
          helper {A = ‘Type’ ._} {‘⊤’} f g x = f x , g tt
          helper {A = ‘Term’} {‘⊤’} f g x = f x , g tt
          helper {A = A ‘→’ A₁} {‘⊤’} f g x = f x , g tt
          helper {A = A ‘×’ A₁} {‘⊤’} f g x = f x , g tt
          helper {A = Quine A} {‘⊤’} f g x = f x , g tt
          helper {A = W A₁} {‘⊥’} {Γ⇓ = proj₁ , proj₂} f g ()
          helper {A = W1 A₂} {‘⊥’} {Γ⇓ = proj₁ , proj₂ , proj₃} f g ()
          helper {A = A₁ ‘’ x} {‘⊥’} f g ()
          helper {A = ‘Type’ ._} {‘⊥’} f g ()
          helper {A = ‘Term’} {‘⊥’} {Γ⇓ = proj₁ , proj₂} f g ()
          helper {A = A ‘→’ A₁} {‘⊥’} f g ()
          helper {A = A ‘×’ A₁} {‘⊥’} f g ()
          helper {A = Quine A} {‘⊥’} f g ()
          helper {A = W A₁} {W B₁} {Γ⇓ = proj₁ , proj₂} f g x = f (Σ.proj₁ x) , g (Σ.proj₂ x)
          helper {A = W1 A₂} {W B₁} {Γ⇓ = proj₁ , proj₂} f g x = f (Σ.proj₁ x) , g (Σ.proj₂ x)
          helper {A = A₂ ‘’ _} {W B₁} {Γ⇓ = proj₁ , proj₂} f g x = {!f (Σ.proj₁ x) , g (Σ.proj₂ x)!}
          helper {A = ‘Type’ ._} {W B₁} {Γ⇓ = proj₁ , proj₂} f g x = f (Σ.proj₁ x) , g (Σ.proj₂ x)
          helper {A = ‘Term’} {W B₁} {Γ⇓ = proj₁ , proj₂} f g x = f (Σ.proj₁ x) , g (Σ.proj₂ x)
          helper {A = A₁ ‘→’ A₂} {W B₁} {Γ⇓ = proj₁ , proj₂} f g x = f (Σ.proj₁ x) , g (Σ.proj₂ x)
          helper {A = A₁ ‘×’ A₂} {W B₁} {Γ⇓ = proj₁ , proj₂} f g x = f (Σ.proj₁ x) , g (Σ.proj₂ x)
          helper {A = Quine A₁} {W B₁} {Γ⇓ = proj₁ , proj₂} f g x = f (Σ.proj₁ x) , g (Σ.proj₂ x)
          helper {B = W1 B₂} f g x = {!!}
          helper {B = B₁ ‘’ x} f g x₁ = {!!}
          helper {B = ‘Type’ ._} f g x = {!!}
          helper {B = ‘Term’} f g x = {!!}
          helper {B = B ‘→’ B₁} f g x = {!!}
          helper {B = B ‘×’ B₁} f g x = {!!}
          helper {B = Quine B} f g x = {!!} {-
          helper {A = W A₁} f g x = {!!}
          helper {A = W1 A₂} f g x = {!!}
          helper {A = A₁ ‘’ x} f g x₁ = {!!}
          helper {A = ‘Type’ ._} f g x = {!!}
          helper {A = ‘Term’} f g x = {!!}
          helper {A = A ‘→’ A₁} f g x = {!!}
          helper {A = A ‘×’ A₁} f g x = {!!}
          helper {A = Quine A} f g x = {!!} -}
  simplify-type⇓← {T = Quine T} T⇓ = {!!}
  simplify-type⇓← {T = ‘⊤’} T⇓ = tt
  simplify-type⇓← {T = ‘⊥’} T⇓ = T⇓
-}

module modal-fixpoint where
  context-to-term : Context → Set
  context-to-term ε = ⊤
  context-to-term (Γ ▻ x) = Σ (context-to-term Γ) (λ _ → Term x)

  context-to-term⇓ : ∀ {Γ} → context-to-term Γ → Context⇓ Γ
  context-to-term⇓ {ε} v = tt
  context-to-term⇓ {Γ ▻ x} v = (context-to-term⇓ (Σ.proj₁ v)) , (Term⇓ (Σ.proj₂ v) (context-to-term⇓ (Σ.proj₁ v)))

  Type-in : ∀ {Γ} → Type Γ → context-to-term Γ → Type ε
  Type-in {ε} T v = T
  Type-in (T ‘→’ T₁) v = (Type-in T v) ‘→’ (Type-in T₁ v)
  Type-in ‘⊤’ v = ‘⊤’
  Type-in ‘⊥’ v = ‘⊥’
  Type-in {Γ ▻ x} T v = Type-in (T ‘’ Σ.proj₂ v) (Σ.proj₁ v)

  postulate hold : ∀ {Γ} → ℕ → Type Γ → Type Γ
  postulate hold-t : ∀ {Γ T} → ℕ → Term {Γ} T → Term T

  helper-ikf : ∀ {Γ A} world (T₁ : Type (Γ ▻ A)) (x : Term A) → Type Γ
  helper-ikf zero ‘Term’ x₁ = ‘⊤’
  helper-ikf world f (x₁ ‘‘→’’ x₂) = helper-ikf world f x₁ ‘→’ helper-ikf world f x₂
  helper-ikf (suc world) ‘Term’ ⌜ x₁ ⌝ = x₁
  helper-ikf (suc world) ‘Term’ (x₁ ‘’ₐ x₂) = hold (suc world) (‘Term’ ‘’ (x₁ ‘’ₐ x₂))
  helper-ikf (suc world) ‘Term’ (SW x₂) = hold (suc world) (‘Term’ ‘’ SW x₂)
  helper-ikf world (W T₂) x₁ = T₂
  helper-ikf world (W1 T₄) x₁ = hold world (W1 T₄ ‘’ x₁)
  helper-ikf world (T₃ ‘’ x₁) x₂ = hold world (T₃ ‘’ x₁ ‘’ x₂)
  helper-ikf world (‘Type’ ._) x₁ = hold world (‘Type’ _ ‘’ x₁)
  helper-ikf world (T₂ ‘→’ T₃) x₁ = helper-ikf world T₂ x₁ ‘→’ helper-ikf world T₃ x₁
  helper-ikf world (T₂ ‘×’ T₃) x₁ = helper-ikf world T₂ x₁ ‘×’ helper-ikf world T₃ x₁
  helper-ikf world (Quine T₂) x₁ = hold world (Quine T₂ ‘’ x₁)
  helper-ikf world ‘⊤’ x₁ = ‘⊤’
  helper-ikf world ‘⊥’ x₁ = ‘⊥’

  mutual
{-    _‘’ₐₕ_ : ∀ {Γ A B} {world} (f : Term {Γ} (A ‘→’ B)) (x : Term A) → Term B
    ‘λ∙’ ‘⌜‘VAR₀’⌝t’ ‘’ₐₕ x₂ = ⌜ x₂ ⌝t
    ‘λ∙’ ‘⌜‘VAR₀’⌝’ ‘’ₐₕ x₂ = ⌜ x₂ ⌝t
    ‘λ∙’ ‘VAR₀’ ‘’ₐₕ x₂ = x₂
    ‘λ∙’ (f ‘’ₐ f₁) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (SW f₁) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (w f) ‘’ₐₕ x₂ = f
    ‘λ∙’ (→w (‘λ∙’ ‘VAR₀’)) ‘’ₐₕ x₂ = ‘λ∙’ ‘VAR₀’
    ‘λ∙’ (→w (‘λ∙’ (f ‘’ₐ f₁))) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→w (‘λ∙’ (SW f₁))) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→w (‘λ∙’ (w f))) ‘’ₐₕ x₂ = ‘λ∙’ (w (‘λ∙’ f ‘’ₐₕ x₂))
    ‘λ∙’ (→w (‘λ∙’ (→ww f))) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→w (‘λ∙’ (‘‘□’’ f))) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→w (‘λ∙’ (f ww‘‘‘→’’’ f₁))) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→w (‘λ∙’ (f ww‘‘‘×’’’ f₁))) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→w (f ‘’ₐ f₁)) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→w (SW f₁)) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→w (w→ f)) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→w (ww→ f)) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→w (f ‘∘’ f₁)) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (→ww f) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (f w‘‘’’ₐ f₁) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (‘‘□’’ f) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (f ww‘‘‘→’’’ f₁) ‘’ₐₕ x₂ = {!!}
    ‘λ∙’ (f ww‘‘‘×’’’ f₁) ‘’ₐₕ x₂ = {!!}
    _‘’ₐₕ_ {world = world} (f ‘’ₐ f₁) x₂ = hold-t world ((_‘’ₐₕ_ {world = world} f f₁) ‘’ₐ x₂)
    _‘’ₐₕ_ {world = world} ‘‘×'’’ x₂ = {!!}
    _‘’ₐₕ_ {world = world} quine→ x₂ = {!!}
    _‘’ₐₕ_ {world = world} quine← x₂ = {!!}
    _‘’ₐₕ_ {world = world} (SW f₁) x₂ = {!!}
    _‘’ₐₕ_ {world = world} (→SW1SV→W f₁) x₂ = {!!}
    _‘’ₐₕ_ {world = world} (←SW1SV→W f₁) x₂ = {!!}
    →SW1SV→SW1SV→W (‘λ∙’ f₁) ‘’ₐₕ x₂ = {!!}
    →SW1SV→SW1SV→W (f₁ ‘’ₐ f₂) ‘’ₐₕ x₂ = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ⌜ x ⌝) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ⌜ x₃ ⌝t) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘⌜‘VAR₀’⌝t’) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘⌜‘VAR₀’⌝’) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ ‘⌜‘VAR₀’⌝t’) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ ‘⌜‘VAR₀’⌝’) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ ‘VAR₀’) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (x₃ ‘’ₐ x₄)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (SW x₄)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (w x₃)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ ‘VAR₀’))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (x₃ ‘’ₐ x₄)))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (SW x₄)))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w ‘⌜‘VAR₀’⌝t’)))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w ‘⌜‘VAR₀’⌝’)))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w ‘VAR₀’)))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (x₃ ‘’ₐ x₄))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (SW x₄))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (‘λ∙’ x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ x₃ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (SW x₃ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (←SW1SV→W (‘λ∙’ x₃) ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x₁ ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (←SW1SV→W (x₃ ‘’ₐ x₄) ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x₁ ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (←SW1SV→W (SW x₄) ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x₁ ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (←SW1SV→W (x₃ ‘∘’ x₄) ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x₁ ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (←SW1SV→SW1SV→W (‘λ∙’ x₃) ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x₁ ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (←SW1SV→SW1SV→W (x₃ ‘’ₐ x₄) ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x₁ ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (←SW1SV→SW1SV→W quine← ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x ⌝))))) = ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x ⌝))))
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (←SW1SV→SW1SV→W (SW x₄) ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x₁ ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (←SW1SV→SW1SV→W (x₃ ‘∘’ x₄) ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x₁ ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ ((x₂ ‘∘’ x₃) ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x ⌝))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ⌜ x₃ ⌝t))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ‘⌜‘VAR₀’⌝t’))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ‘⌜‘VAR₀’⌝’))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (‘λ∙’ x₃)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ‘VAR₀’))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (x₃ ‘’ₐ x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ‘‘×'’’))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w quine→))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w quine←))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ‘tt’))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (SW x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (→SW1SV→W x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (←SW1SV→W x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (→SW1SV→SW1SV→W x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (←SW1SV→SW1SV→W x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (w x₃)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (w→ x₃)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (→w x₃)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (ww→ x₃)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (→ww x₃)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (x₃ ‘∘’ x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (x₃ w‘‘’’ₐ x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w ‘‘’ₐ’))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (‘‘□’’ x₃)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (x₃ ‘‘→’’ x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (x₃ ww‘‘‘→’’’ x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (w (x₃ ww‘‘‘×’’’ x₄)))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (→w x₃))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (→ww x₃))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (x₃ w‘‘’’ₐ x₄))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (‘‘□’’ x₃))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (x₃ ww‘‘‘→’’’ x₄))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (w (x₃ ww‘‘‘×’’’ x₄))))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (→ww x₃)))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (‘‘□’’ x₃)))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (x₃ ww‘‘‘→’’’ x₄)))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (‘λ∙’ (x₃ ww‘‘‘×’’’ x₄)))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (x₃ ‘’ₐ x₄))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (SW x₄))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (w→ x₃))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (ww→ x₃))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→w (x₃ ‘∘’ x₄))) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (→ww x₃)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (x₃ w‘‘’’ₐ x₄)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (‘‘□’’ x₃)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (x₃ ww‘‘‘→’’’ x₄)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘λ∙’ (x₃ ww‘‘‘×’’’ x₄)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘VAR₀’) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ (x₃ ‘’ₐ x₄)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘‘×'’’) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ quine→) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ quine←) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘tt’) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ SW x₄) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ →SW1SV→W x₄) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ←SW1SV→W x₄) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ →SW1SV→SW1SV→W x₄) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ←SW1SV→SW1SV→W x₄) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ w x₃) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ w→ x₃) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ →w x₃) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ww→ x₃) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ →ww x₃) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ (x₃ ‘∘’ x₄)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ (x₃ w‘‘’’ₐ x₄)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘‘’ₐ’) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ ‘‘□’’ x₃) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ (x₃ ‘‘→’’ x₄)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ (x₃ ww‘‘‘→’’’ x₄)) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (x₂ ‘’ₐ x₃ ww‘‘‘×’’’ x₄) = {!!}
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ SW x₃ = {!!}
    →SW1SV→SW1SV→W (SW f₂) ‘’ₐₕ x₂ = {!!}
    →SW1SV→SW1SV→W (←SW1SV→W f₂) ‘’ₐₕ x₂ = {!!}
    →SW1SV→SW1SV→W (←SW1SV→SW1SV→W f₂) ‘’ₐₕ x₂ = {!!}
    →SW1SV→SW1SV→W (f₁ ‘∘’ f₂) ‘’ₐₕ x₂ = {!!}
    ←SW1SV→SW1SV→W (‘λ∙’ f₁) ‘’ₐₕ x₂ = {!!}
    ←SW1SV→SW1SV→W (f₁ ‘’ₐ f₂) ‘’ₐₕ x₂ = {!!}
    ←SW1SV→SW1SV→W quine← ‘’ₐₕ x₂ = {!!} -- ←SW1SV→SW1SV→W quine← ‘’ₐ x₂
    ←SW1SV→SW1SV→W (SW f₂) ‘’ₐₕ x₂ = {!!}
    ←SW1SV→SW1SV→W (→SW1SV→W f₂) ‘’ₐₕ x₂ = {!!}
    ←SW1SV→SW1SV→W (→SW1SV→SW1SV→W f₂) ‘’ₐₕ x₂ = {!!}
    ←SW1SV→SW1SV→W (f₁ ‘∘’ f₂) ‘’ₐₕ x₂ = {!!}
    _‘’ₐₕ_ {world = world} (w→ f) x₂ = w→ f ‘’ₐ x₂
    _‘’ₐₕ_ {world = world} (ww→ f) x₂ = {!!}
    _‘’ₐₕ_ {world = world} (f ‘∘’ f₁) x₂ = _‘’ₐₕ_ {world = world} f (_‘’ₐₕ_ {world = world} f₁ x₂)
    _‘’ₐₕ_ {world = world} ‘‘’ₐ’ x₂ = {!!}

    ‘‘□’’ₕ : ∀ {Γ A B} → Term {Γ ▻ A ▻ B} (W (W (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝))) → Term {Γ ▻ A ▻ B} (W (W (‘Type’ Γ)))
    ‘‘□’’ₕ t = ‘‘□’’ t

    _‘∘’ₕ_ : ∀ {Γ A B C} {world} (g : Term {Γ} (B ‘→’ C)) (f : Term (A ‘→’ B)) → Term (A ‘→’ C)
    f ‘∘’ₕ g = f ‘∘’ g-}

    in-kripke-frame-c : ∀ (world : ℕ) → Context → Context
    in-kripke-frame : ∀ {Γ} (world : ℕ) → Type Γ → Type (in-kripke-frame-c world Γ)
    in-kripke-frame-t : ∀ {Γ} (world : ℕ) {T : Type Γ} → Term T → Term (in-kripke-frame world T)

    in-kripke-frame-c world ε = ε
    in-kripke-frame-c world (Γ ▻ x) = in-kripke-frame-c world Γ ▻ in-kripke-frame world x

    _‘’ₐₕ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
    (f₁ ‘’ₐ f₂) ‘’ₐₕ x₁ = (f₁ ‘’ₐₕ f₂) ‘’ₐ x₁
    →SW1SV→SW1SV→W quine→ ‘’ₐₕ (←SW1SV→SW1SV→W quine← ‘’ₐ f) = f
    f ‘’ₐₕ x = {!!}


    in-kripke-frame world (T ‘→’ T₁) = (in-kripke-frame world T) ‘→’ (in-kripke-frame world T₁)
    in-kripke-frame world (‘Type’ Γ) = ‘Type’ (in-kripke-frame-c world Γ)
    in-kripke-frame world (W T₁) = W (in-kripke-frame world T₁)
    in-kripke-frame world (W1 T₂) = W1 (in-kripke-frame world T₂)
    in-kripke-frame zero (‘Term’ ‘’ x) = ‘⊤’
    in-kripke-frame {Γ = Γ} (suc world) (‘Term’ ‘’ (f ‘’ₐ x)) = helper helper'
      where helper' : Term (in-kripke-frame world (‘Type’ Γ))
            helper' = simplify-term (in-kripke-frame-t world f) ‘’ₐₕ simplify-term (in-kripke-frame-t world x)

            helper : ∀ {Γ} → Term (in-kripke-frame world (‘Type’ Γ)) → Type (in-kripke-frame-c (suc world) Γ)
            helper x = {!!}
    in-kripke-frame (suc world) (‘Term’ ‘’ x) = {!in-kripke-frame world x!}
    in-kripke-frame world (T₁ ‘’ x) = {!!}
    in-kripke-frame world ‘Term’ = {!!}
    in-kripke-frame world (T ‘×’ T₁) = {!!}
    in-kripke-frame world (Quine T) = {!!}
    in-kripke-frame world ‘⊤’ = ‘⊤’
    in-kripke-frame world ‘⊥’ = ‘⊥’

    in-kripke-frame-t world ⌜ x ⌝ = ⌜ (in-kripke-frame world x) ⌝
    in-kripke-frame-t zero ⌜ t ⌝t = ‘tt’
    in-kripke-frame-t (suc world) ⌜ t ⌝t = {!!}
    in-kripke-frame-t world ‘⌜‘VAR₀’⌝t’ = {!!}
    in-kripke-frame-t world ‘⌜‘VAR₀’⌝’ = {!!}
    in-kripke-frame-t world (‘λ∙’ t) = ‘λ∙’ (in-kripke-frame-t world t)
    in-kripke-frame-t world ‘VAR₀’ = ‘VAR₀’
    in-kripke-frame-t world (t ‘’ₐ t₁) = in-kripke-frame-t world t ‘’ₐₕ in-kripke-frame-t world t₁
    in-kripke-frame-t world ‘‘×'’’ = {!!}
    in-kripke-frame-t world quine→ = {!!}
    in-kripke-frame-t world quine← = {!!}
    in-kripke-frame-t world ‘tt’ = ‘tt’
    in-kripke-frame-t world (SW t₁) = {!!}
    in-kripke-frame-t world (→SW1SV→W t₁) = {!!}
    in-kripke-frame-t world (←SW1SV→W t₁) = {!!}
    in-kripke-frame-t world (→SW1SV→SW1SV→W t₁) = {!!}
    in-kripke-frame-t world (←SW1SV→SW1SV→W t₁) = {!!}
    in-kripke-frame-t world (w t) = w (in-kripke-frame-t world t)
    in-kripke-frame-t world (w→ t) = w→ (in-kripke-frame-t world t)
    in-kripke-frame-t world (→w t) = →w (in-kripke-frame-t world t)
    in-kripke-frame-t world (ww→ t) = ww→ (in-kripke-frame-t world t)
    in-kripke-frame-t world (→ww t) = →ww (in-kripke-frame-t world t)
    in-kripke-frame-t world (t ‘∘’ t₁) = {!!}
    in-kripke-frame-t world (t w‘‘’’ₐ t₁) = {!!}
    in-kripke-frame-t world ‘‘’ₐ’ = {!!}
    in-kripke-frame-t zero (‘‘□’’ t) = w (w ⌜ ‘⊤’ ⌝)
    in-kripke-frame-t {Γ = Γ ▻ A ▻ B} (suc world) (‘‘□’’ t) = helper {lzero} (‘‘□’’ₕ (in-kripke-frame-t world t))
      where ‘‘□’’ₕ : ∀ {Γ A B} → Term {in-kripke-frame-c world Γ ▻ A ▻ B} (W (W (in-kripke-frame world (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝)))) → Term {in-kripke-frame-c world Γ ▻ A ▻ B} (W (W (‘Type’ (in-kripke-frame-c world Γ))))
            ‘‘□’’ₕ T = {!!}

            helper : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → A → B
            helper t = {!!}
    in-kripke-frame-t world (t ‘‘→’’ t₁) = {!!}
    in-kripke-frame-t world (t ww‘‘‘→’’’ t₁) = {!!}
    in-kripke-frame-t world (t ww‘‘‘×’’’ t₁) = {!!}
{-
    in-kripke-frame zero ‘Term’ = ‘⊤’
    in-kripke-frame {Γ} world (T ‘→’ T₁) = simplify-type (in-kripke-frame world T ‘→’ in-kripke-frame world T₁)
    in-kripke-frame {Γ} world (T ‘×’ T₁) = simplify-type (in-kripke-frame world T ‘×’ in-kripke-frame world T₁)
    in-kripke-frame world (W T) = simplify-type (W (in-kripke-frame world T))
    in-kripke-frame world (W1 T) = simplify-type (W1 (in-kripke-frame world T))
    in-kripke-frame world (T₁ ‘’ x) = simplify-type (helper-ikf world (simplify-type (in-kripke-frame world T₁)) (simplify-term (in-kripke-frame-t world x)))
    in-kripke-frame world ‘⊤’ = ‘⊤’
    in-kripke-frame world ‘⊥’ = ‘⊥’
    in-kripke-frame world (‘Type’ Γ) = hold world (‘Type’ Γ)
    in-kripke-frame world (Quine T) = hold world (Quine T)
    in-kripke-frame {Γ ▻ .(‘Type’ Γ)} (suc world) ‘Term’ = ‘Term’  {-helper (in-kripke-frame-t world T v) v
      where
        helper : ∀ {Γ} → Term (‘Type’ Γ) → context-to-term Γ → Type ε
        helper ⌜ x ⌝ v = Type-in x v
        helper (t ‘‘→’’ t₁) v = helper t v ‘→’ helper t₁ v
        helper (t ‘’ₐ t₁) v = {!!}
        helper (SW t₁) v = {!!}-}

    in-kripke-frame-t : ∀ {Γ} (world : ℕ) → {T : Type Γ} → Term T → Term (in-kripke-frame world T)
    in-kripke-frame-t world ⌜ x ⌝ = ⌜ in-kripke-frame world x ⌝
    in-kripke-frame-t world ⌜ x ⌝t = ⌜ in-kripke-frame-t world x ⌝t
    in-kripke-frame-t world ‘⌜‘VAR₀’⌝t’ = ‘⌜‘VAR₀’⌝t’
    in-kripke-frame-t world ‘⌜‘VAR₀’⌝’ = ‘⌜‘VAR₀’⌝’
    in-kripke-frame-t world (‘λ∙’ x) = ‘λ∙’ (in-kripke-frame-t world x)
    in-kripke-frame-t world ‘VAR₀’ = ‘VAR₀’
    in-kripke-frame-t world (x ‘’ₐ x₁) = _‘’ₐₕ_ {world = world} (simplify-term (in-kripke-frame-t world x)) (simplify-term (in-kripke-frame-t world x₁))
    in-kripke-frame-t world ‘‘×'’’ = ‘‘×'’’
    in-kripke-frame-t world quine→ = quine→
    in-kripke-frame-t world quine← = quine←
    in-kripke-frame-t world ‘tt’ = ‘tt’
    in-kripke-frame-t world (SW x₁) = SW (in-kripke-frame-t world x₁)
    in-kripke-frame-t world (→SW1SV→W x₁) = →SW1SV→W (in-kripke-frame-t world x₁)
    in-kripke-frame-t world (←SW1SV→W x₁) = ←SW1SV→W (in-kripke-frame-t world x₁)
    in-kripke-frame-t world (→SW1SV→SW1SV→W x₁) = →SW1SV→SW1SV→W (in-kripke-frame-t world x₁)
    in-kripke-frame-t world (←SW1SV→SW1SV→W x₁) = ←SW1SV→SW1SV→W (in-kripke-frame-t world x₁)
    in-kripke-frame-t world (w x) = w (in-kripke-frame-t world x)
    in-kripke-frame-t world (w→ x) = w→ (in-kripke-frame-t world x)
    in-kripke-frame-t world (→w x) = →w (in-kripke-frame-t world x)
    in-kripke-frame-t world (ww→ x) = ww→ (in-kripke-frame-t world x)
    in-kripke-frame-t world (→ww x) = →ww (in-kripke-frame-t world x)
    in-kripke-frame-t world (x ‘∘’ x₁) = _‘∘’ₕ_ {world = world} (simplify-term (in-kripke-frame-t world x)) (simplify-term (in-kripke-frame-t world x₁))
    in-kripke-frame-t world (x w‘‘’’ₐ x₁) = simplify-term (in-kripke-frame-t world x) w‘‘’’ₐ simplify-term (in-kripke-frame-t world x₁)
    in-kripke-frame-t world ‘‘’ₐ’ = ‘‘’ₐ’
    in-kripke-frame-t zero (‘‘□’’ x) = w (w ⌜ ‘⊤’ ⌝)
    in-kripke-frame-t (suc world) (‘‘□’’ x) = ‘‘□’’ₕ (simplify-term (in-kripke-frame-t world x))
    in-kripke-frame-t world (x ‘‘→’’ x₁) = {!!}
    in-kripke-frame-t world (x ww‘‘‘→’’’ x₁) = {!!}
    in-kripke-frame-t world (x ww‘‘‘×’’’ x₁) = {!!}
-}
  kripke-reduce : ∀ {Γ} → Type Γ → context-to-term Γ → Type ε
  kripke-reduce (W x₁) v = kripke-reduce x₁ (Σ.proj₁ v)
  kripke-reduce (W1 x₂) v = kripke-reduce x₂ ((Σ.proj₁ (Σ.proj₁ v)) , (‘λ∙’ (Σ.proj₂ v) ‘’ₐ Σ.proj₂ (Σ.proj₁ v)))
  kripke-reduce (T₁ ‘’ x) v = kripke-reduce T₁ (v , x)
  kripke-reduce (‘Type’ Γ) v = Type-in (‘Type’ Γ) v
  -- kripke-reduce ‘TVAR₀’ v = {!!}
  kripke-reduce ‘Term’ (v , T) = {!!} {- Type-in (lower (Term⇓ (Σ.proj₂ v) (context-to-term⇓ (Σ.proj₁ v)))) (Σ.proj₁ v) -}
  kripke-reduce (T ‘→’ T₁) v = kripke-reduce T v ‘→’ kripke-reduce T₁ v
  kripke-reduce (T ‘×’ T₁) v = kripke-reduce T v ‘×’ kripke-reduce T₁ v
  kripke-reduce (Quine x) v = {!!}
  kripke-reduce ‘⊤’ v = ‘⊤’
  kripke-reduce ‘⊥’ v = ‘⊥’


  kripke-eval' : ∀ {Γ} → ℕ → Type Γ → context-to-term Γ → Type ε
  kripke-eval' 0 T v = Type-in T v
  kripke-eval' (suc n) T v = kripke-eval' n (kripke-reduce T v) tt

  kripke-finalize : ∀ {Γ} → Type Γ → context-to-term Γ → Type ε
  kripke-finalize (W x₁) v = kripke-finalize x₁ (Σ.proj₁ v)
  kripke-finalize (W1 x₂) v = kripke-finalize x₂ ((Σ.proj₁ (Σ.proj₁ v)) , (‘λ∙’ (Σ.proj₂ v) ‘’ₐ Σ.proj₂ (Σ.proj₁ v)))
  kripke-finalize (T₁ ‘’ x) v = kripke-finalize T₁ (v , x)
  kripke-finalize (‘Type’ Γ) v = Type-in (‘Type’ Γ) v
  -- kripke-finalize ‘TVAR₀’ v = {!!}
  kripke-finalize ‘Term’ v = ‘⊤’
  kripke-finalize (T ‘→’ T₁) v = kripke-finalize T v ‘→’ kripke-finalize T₁ v
  kripke-finalize (T ‘×’ T₁) v = kripke-finalize T v ‘×’ kripke-finalize T₁ v
  kripke-finalize (Quine x) v = {!!}
  kripke-finalize ‘⊤’ v = ‘⊤’
  kripke-finalize ‘⊥’ v = ‘⊥’

  mutual
    kripke-count : ∀ {Γ} → Type Γ → ℕ
    kripke-count (W T₁) = kripke-count T₁
    kripke-count (W1 T₂) = kripke-count T₂
    kripke-count (T₁ ‘’ x) = kripke-count T₁ + kripke-count-t x
    kripke-count (‘Type’ Γ) = 0
    -- kripke-count ‘TVAR₀’ = 0
    kripke-count ‘Term’ = 1
    kripke-count (T ‘→’ T₁) = kripke-count T + kripke-count T₁
    kripke-count (T ‘×’ T₁) = kripke-count T + kripke-count T₁
    kripke-count (Quine T) = kripke-count T
    kripke-count ‘⊤’ = 0
    kripke-count ‘⊥’ = 0

    kripke-count-t : ∀ {Γ T} → Term {Γ} T → ℕ
    kripke-count-t ⌜ x ⌝ = kripke-count x
    kripke-count-t (x ‘’ₐ x₁) = kripke-count-t x + kripke-count-t x₁
    kripke-count-t ⌜ x ⌝t = kripke-count-t x
    kripke-count-t ‘⌜‘VAR₀’⌝t’ = 0
    kripke-count-t ‘⌜‘VAR₀’⌝’ = 0
    kripke-count-t (‘λ∙’ x) = kripke-count-t x
    kripke-count-t ‘VAR₀’ = 0
    kripke-count-t quine→ = 0
    kripke-count-t quine← = 0
    kripke-count-t ‘tt’ = 0
    kripke-count-t (SW x₁) = kripke-count-t x₁
    kripke-count-t (→SW1SV→W x₁) = kripke-count-t x₁
    kripke-count-t (←SW1SV→W x₁) = kripke-count-t x₁
    kripke-count-t (→SW1SV→SW1SV→W x₁) = kripke-count-t x₁
    kripke-count-t (←SW1SV→SW1SV→W x₁) = kripke-count-t x₁
    kripke-count-t (w x) = kripke-count-t x
    kripke-count-t (w→ x) = kripke-count-t x
    kripke-count-t (→w x) = kripke-count-t x
    kripke-count-t (ww→ x) = kripke-count-t x
    kripke-count-t (→ww x) = kripke-count-t x
    kripke-count-t ‘‘×'’’ = 0
    kripke-count-t (x ‘∘’ x₁) = kripke-count-t x + kripke-count-t x₁
    kripke-count-t (x w‘‘’’ₐ x₁) = kripke-count-t x + kripke-count-t x₁
    kripke-count-t ‘‘’ₐ’ = 0
    -- kripke-count-t (f w‘‘’’ x) = kripke-count-t f + kripke-count-t x
    kripke-count-t (‘‘□’’ T) = 1 + kripke-count-t T
    kripke-count-t (x ‘‘→’’ x₁) = kripke-count-t x + kripke-count-t x₁
    kripke-count-t (x ww‘‘‘→’’’ x₁) = kripke-count-t x + kripke-count-t x₁
    kripke-count-t (x ww‘‘‘×’’’ x₁) = kripke-count-t x + kripke-count-t x₁

  kripke-normalize' : ∀ {Γ} → Type Γ → context-to-term Γ → Type ε
  kripke-normalize' T v = kripke-eval' (kripke-count T) T v

  kripke-normalize'' : ∀ {Γ} → (T : Type Γ) → Type (in-kripke-frame-c (kripke-count T) Γ)
  kripke-normalize'' T = in-kripke-frame (kripke-count T) T

open modal-fixpoint

‘Bot’ : ∀ {Γ} → Type Γ
‘Bot’ {Γ} = Quine (W1 ‘Term’ ‘’ ‘VAR₀’ ‘→’ W1 ‘Term’ ‘’ ‘VAR₀’ ‘→’ W (‘Type’ Γ)) {- a bot takes in the source code for itself, for another bot, and spits out the assertion that it cooperates with this bot -}

_cooperates-with_ : □ ‘Bot’ → □ ‘Bot’ → Type ε
b1 cooperates-with b2 = lower (Term⇓ b1 tt (lift b1) (lift b2))

‘eval-bot'’ : ∀ {Γ} → Term {Γ} (‘Bot’ ‘→’ (‘□’ ‘Bot’ ‘→’ ‘□’ ‘Bot’ ‘→’ ‘Type’ Γ))
‘eval-bot'’ = →SW1SV→SW1SV→W quine→

‘‘eval-bot'’’ : ∀ {Γ} → Term {Γ} (‘□’ ‘Bot’ ‘→’ ‘□’ ({- other -} ‘□’ ‘Bot’ ‘→’ ‘Type’ Γ))
‘‘eval-bot'’’ = ‘λ∙’ (w ⌜ ‘eval-bot'’ ⌝t w‘‘’’ₐ ‘VAR₀’ w‘‘’’ₐ ‘⌜‘VAR₀’⌝t’)

‘other-cooperates-with’ : ∀ {Γ} → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ ‘Bot’)) ‘→’ W (W (‘□’ (‘Type’ Γ))))
‘other-cooperates-with’ {Γ} = ‘eval-other'’ ‘∘’ w→ (w (w→ (w (‘λ∙’ ‘⌜‘VAR₀’⌝t’))))
  where
    ‘eval-other’ : Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ (‘□’ ‘Bot’ ‘→’ ‘Type’ Γ))))
    ‘eval-other’ = w→ (w (w→ (w ‘‘eval-bot'’’))) ‘’ₐ ‘VAR₀’

    ‘eval-other'’ : Term (W (W (‘□’ (‘□’ ‘Bot’))) ‘→’ W (W (‘□’ (‘Type’ Γ))))
    ‘eval-other'’ = ww→ (w→ (w (w→ (w ‘‘’ₐ’))) ‘’ₐ ‘eval-other’)

‘self’ : ∀ {Γ} → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ ‘Bot’)))
‘self’ = w ‘VAR₀’

‘other’ : ∀ {Γ} → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ ‘Bot’)))
‘other’ = ‘VAR₀’

make-bot : ∀ {Γ} → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘Type’ Γ))) → Term {Γ} ‘Bot’
make-bot t = ←SW1SV→SW1SV→W quine← ‘’ₐ ‘λ∙’ (→w (‘λ∙’ t))

ww‘‘‘¬’’’_ : ∀ {Γ A B}
  → Term {Γ ▻ A ▻ B} (W (W (‘□’ (‘Type’ Γ))))
  → Term {Γ ▻ A ▻ B} (W (W (‘□’ (‘Type’ Γ))))
ww‘‘‘¬’’’ T = T ww‘‘‘→’’’ w (w ⌜ ⌜ ‘⊥’ ⌝ ⌝t)

‘DefectBot’ : □ ‘Bot’
‘CooperateBot’ : □ ‘Bot’
‘FairBot’ : □ ‘Bot’
‘PrudentBot’ : □ ‘Bot’

‘DefectBot’ = make-bot (w (w ⌜ ‘⊥’ ⌝))
‘CooperateBot’ = make-bot (w (w ⌜ ‘⊤’ ⌝))
‘FairBot’ = make-bot (‘‘□’’ (‘other-cooperates-with’ ‘’ₐ ‘self’))
‘PrudentBot’ = make-bot (‘‘□’’ (φ₀ ww‘‘‘×’’’ (¬□⊥ ww‘‘‘→’’’ other-defects-against-DefectBot)))
  where
    φ₀ : ∀ {Γ} → Term {Γ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ (‘Type’ Γ))))
    φ₀ = ‘other-cooperates-with’ ‘’ₐ ‘self’

    other-defects-against-DefectBot : Term {_ ▻ ‘□’ ‘Bot’ ▻ W (‘□’ ‘Bot’)} (W (W (‘□’ (‘Type’ _))))
    other-defects-against-DefectBot = ww‘‘‘¬’’’ (‘other-cooperates-with’ ‘’ₐ w (w ⌜ ‘DefectBot’ ⌝t))

    ¬□⊥ : ∀ {Γ A B} → Term {Γ ▻ A ▻ B} (W (W (‘□’ (‘Type’ Γ))))
    ¬□⊥ = w (w ⌜ ⌜ ‘¬’ (‘□’ ‘⊥’) ⌝ ⌝t)

data KnownBot : Set where
  DefectBot : KnownBot
  CooperateBot : KnownBot
  FairBot : KnownBot
  PrudentBot : KnownBot

KnownBot⇓ : KnownBot → □ ‘Bot’
KnownBot⇓ DefectBot = ‘DefectBot’
KnownBot⇓ CooperateBot = ‘CooperateBot’
KnownBot⇓ FairBot = ‘FairBot’
KnownBot⇓ PrudentBot = ‘PrudentBot’

DB-defects : ∀ {b} → □ (‘¬’ (‘DefectBot’ cooperates-with b))
CB-cooperates : ∀ {b} → □ (‘CooperateBot’ cooperates-with b)

FB-spec : KnownBot → □ ‘Bot’ → Type ε
FB-spec DefectBot b = ‘¬’ (‘FairBot’ cooperates-with b)
FB-spec CooperateBot b = ‘FairBot’ cooperates-with b
FB-spec FairBot b = ‘FairBot’ cooperates-with b
FB-spec PrudentBot b = ‘FairBot’ cooperates-with b

FB-good : ∀ {b} → □ (FB-spec b (KnownBot⇓ b))

DB-defects {b} = ‘λ∙’ ‘VAR₀’
CB-cooperates {b} = ‘tt’
FB-good {DefectBot} = {!!}
FB-good {CooperateBot} = {!!}
FB-good {FairBot} = {!!}
FB-good {PrudentBot} = {!!}


{-
data Bot : Set where
  DefectBot : Bot
  CooperateBot : Bot
  FairBot : Bot
  PrudentBot : Bot

data Opponent : Set where
  Self : Opponent
  Other : Type ε → Opponent

_cooperates-with-me : ∀ {Γ} → Term {Γ} (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ ‘→’ ‘Type’ Γ) → Term {Γ ▻ ‘Type’ Γ} (W ‘Type’ Γ)
x cooperates-with-me = w→ (w x) ‘’ₐ ‘⌜‘VAR₀’⌝’

{-
‘cooperates-with'’ : □ (‘Bot’ ‘→’ ‘Bot’ ‘→’ ‘Type’ Γ)
‘cooperates-with'’ = ‘λ∙’ (→w ((‘eval-bot’ ‘VAR₀’) ‘∘’ (w→ (w {!!}))))
  where ‘eval-bot'’ : Term (‘Bot’ ‘→’ (‘□’ ‘Bot’ ‘→’ ‘Type’ Γ))
        ‘eval-bot'’ = →SW1SV→W quine→

        ‘eval-bot’_ : Term {ε ▻ ‘Bot’} (W ‘Bot’) → Term (W (‘□’ ‘Bot’) ‘→’ W ‘Type’ Γ)
        ‘eval-bot’ b = w→ (w→ (w ‘eval-bot'’) ‘’ₐ b)

        get-bot-source : Term {ε} (‘Bot’ ‘→’ ‘□’ ‘Bot’)
        get-bot-source = {!!}-}

_‘cooperates’ : Bot → Term {ε} (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ ‘→’ ‘Type’ Γ)
DefectBot ‘cooperates’ = ‘λ∙’ (w ⌜ ‘⊥’ ⌝)
CooperateBot ‘cooperates’ = ‘λ∙’ (w ⌜ ‘⊤’ ⌝)
FairBot ‘cooperates’ = ‘λ∙’ {!!}
PrudentBot ‘cooperates’ = {!!}

_‘cooperates-with'’_ : Bot → Term {ε} (‘Term’ ‘’ ⌜ ‘Type’ Γ ⌝ ‘→’ ‘Type’ Γ) → Type ε
FairBot ‘cooperates-with'’ x = Quine (W1 ‘Term’ ‘’ (x cooperates-with-me))
DefectBot ‘cooperates-with'’ b2 = ‘⊥’
CooperateBot ‘cooperates-with'’ b2 = ‘⊤’
PrudentBot ‘cooperates-with'’ x = Quine (W1 ‘Term’ ‘’ (x cooperates-with-me w‘‘×’’ w ⌜ (‘¬’ (‘Term’ ‘’ ⌜ ‘⊥’ ⌝) ‘→’ ‘¬’ {!!}) ⌝))
-}

   {-

  box-free? : ∀ {Γ} → Type Γ → context-to-term Γ → Set
  box-free? (T₁ ‘’ x) v = box-free? T₁ (v , x)
  box-free? ‘Type’ Γ v = ⊤
  box-free? ‘Term’ v = ⊥
  box-free? (T ‘→’ T₁) v = box-free? T v × box-free? T₁ v
  box-free? ‘⊤’ v = ⊤
  box-free? ‘⊥’ v = ⊤

  mutual
    kripke-lift→ : ∀ (n : ℕ) (T : Type ε) → box-free? (kripke-eval' n T) tt
      → Term (kripke-eval' n T ‘→’ T)
    kripke-lift→ zero T H = ‘λx∙x’
    kripke-lift→ (suc n) (T₁ ‘’ x) H = {!!}
    kripke-lift→ (suc n) (T ‘→’ T₁) H = {!!} ‘∘’ (kripke-lift→ n (kripke-reduce (T ‘→’ T₁) tt) H)
    kripke-lift→ (suc n) ‘Type’ Γ H = kripke-lift→ n _ H
    kripke-lift→ (suc n) ‘⊤’ H = kripke-lift→ n _ H
    kripke-lift→ (suc n) ‘⊥’ H = kripke-lift→ n _ H

    kripke-lift← : ∀ (n : ℕ) (T : Type ε) → box-free? (kripke-eval' n T) tt
      → Term (kripke-eval' n T)
      → Term T
    kripke-lift← n T H t = {!!}
{-    kripke-lift : ∀ {Γ} (T : Type Γ) v → Term (kripke-reduce T v ‘→’ Type-in T v)
    kripke-lift (T₁ ‘’ x) = {!!}
    kripke-lift ‘Type’ Γ v = {!!}
    kripke-lift ‘Term’ v = {!!}
    kripke-lift {ε} (T ‘→’ T₁) v = {!!}
  kripke-lift {Γ ▻ x} (T ‘→’ T₁) v = {!!}
  kripke-lift ‘⊤’ v = {!!}
  kripke-lift ‘⊥’ v = {!!}-}

  Quine : Type (ε ▻ ‘Type’ Γ) → Type ε
  Quine φ = {!!}

  quine→ : ∀ {φ} → Term {ε} (Quine φ        ‘→’ φ ‘’ ⌜ Quine φ ⌝)
  quine← : ∀ {φ} → Term {ε} (φ ‘’ ⌜ Quine φ ⌝ ‘→’ Quine φ)

  quine→ = {!!}
  quine← = {!!}
-}

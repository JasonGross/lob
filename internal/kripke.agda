{-# OPTIONS --without-K #-}
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

mutual
  Context⇓ : (Γ : Context) → Set (lsuc max-level)
  Context⇓ ε = ⊤
  Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

  Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
  Type⇓ (W T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
  Type⇓ (W1 T) Γ⇓ = Type⇓ T ((Σ.proj₁ (Σ.proj₁ Γ⇓)) , (Σ.proj₂ Γ⇓))
  Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
  Type⇓ (‘Type’ Γ) Γ⇓ = Lifted (Type Γ)
  Type⇓ ‘Term’ Γ⇓ = Lifted (Term (lower (Σ.proj₂ Γ⇓)))
  Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
  Type⇓ (A ‘×’ B) Γ⇓ = Type⇓ A Γ⇓ × Type⇓ B Γ⇓
  Type⇓ ‘⊤’ Γ⇓ = ⊤
  Type⇓ ‘⊥’ Γ⇓ = ⊥
  Type⇓ (Quine φ) Γ⇓ = Type⇓ φ (Γ⇓ , (lift (Quine φ)))

  Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓
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
  Term⇓ (←SW1SV→W f) = Term⇓ f
  Term⇓ (→SW1SV→W f) = Term⇓ f
  Term⇓ (←SW1SV→SW1SV→W f) = Term⇓ f
  Term⇓ (→SW1SV→SW1SV→W f) = Term⇓ f
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

  kripke-reduce : ∀ {Γ} → Type Γ → context-to-term Γ → Type ε
  kripke-reduce (W x₁) v = kripke-reduce x₁ (Σ.proj₁ v)
  kripke-reduce (W1 x₂) v = kripke-reduce x₂ ((Σ.proj₁ (Σ.proj₁ v)) , (‘λ∙’ (Σ.proj₂ v) ‘’ₐ Σ.proj₂ (Σ.proj₁ v)))
  kripke-reduce (T₁ ‘’ x) v = kripke-reduce T₁ (v , x)
  kripke-reduce (‘Type’ Γ) v = Type-in (‘Type’ Γ) v
  -- kripke-reduce ‘TVAR₀’ v = {!!}
  kripke-reduce ‘Term’ v = Type-in (lower (Term⇓ (Σ.proj₂ v) (context-to-term⇓ (Σ.proj₁ v)))) (Σ.proj₁ v)
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

{-# OPTIONS --without-K #-}
module mini-lob-full-dependent where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixl 3 _‘’₁_
infixr 1 _‘→’_
infixl 3 _‘’ₐ_

data Context : Set
data Type : Context → Set
data Context where
  ε : Context
  _▻_ : (Γ : Context) → Type Γ → Context

data Term : {Γ : Context} → Type Γ → Set
data Type where
  ‘Context’ : ∀ {Γ} → Type Γ
  ‘Type’ : ∀ {Γ} → Term {Γ} ‘Context’ → Type Γ
  ‘Term’ : ∀ {Γ} → (C : Term {Γ} ‘Context’) → Term {Γ} (‘Type’ C) → Type Γ
  _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  ‘⊤’ : ∀ {Γ} → Type Γ
  ‘⊥’ : ∀ {Γ} → Type Γ
  -- not strictly necessary, but allows for nicer reduction
  wkT₀ : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
  -- I'm not sure how to make this one from scratch
  Δ→Type : ∀ {Γ} → Type Γ

_‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
_‘’ₜ_ : ∀ {Γ A B} → Term {Γ ▻ A} B → (a : Term A) → Term {Γ} (B ‘’ a)


‘Context’ ‘’ x = ‘Context’
‘Type’ C ‘’ x = ‘Type’ (C ‘’ₜ x)
‘Term’ C T ‘’ x = ‘Term’ (C ‘’ₜ x) (T ‘’ₜ x)
(A ‘→’ B) ‘’ x = (A ‘’ x) ‘→’ (B ‘’ x)
‘⊤’ ‘’ x = ‘⊤’
‘⊥’ ‘’ x = ‘⊥’
wkT₀ T ‘’ x = T
Δ→Type ‘’ x = Δ→Type

data ContextOver : Context → Set
_++_ : (Γ : Context) → ContextOver Γ → Context

data ContextOver where
  ε' : ∀ {Γ} → ContextOver Γ
  _▻'_ : ∀ {Γ} → (Γ' : ContextOver Γ) → Type (Γ ++ Γ') → ContextOver Γ

Γ ++ ε' = Γ
Γ ++ (Γ' ▻' T) = (Γ ++ Γ') ▻ T

_‘’c_ : ∀ {Γ A} → ContextOver (Γ ▻ A) → Term A → ContextOver Γ
_‘’ₙ_ : ∀ {Γ A Γ'} → Type ((Γ ▻ A) ++ Γ') → (a : Term A) → Type (Γ ++ (Γ' ‘’c a))

ε' ‘’c x = ε'
(Γ' ▻' T) ‘’c x = (Γ' ‘’c x) ▻' (T ‘’ₙ x)

_‘’ₜₙ_ : ∀ {Γ A Γ' B} → Term {(Γ ▻ A) ++ Γ'} B → (a : Term A) → Term {Γ ++ (Γ' ‘’c a)} (B ‘’ₙ a)

_‘’ₙ_ {Γ} {A} {ε'} T a = T ‘’ a
_‘’ₙ_ {Γ' = Γ' ▻' U} ‘Context’ x = ‘Context’
_‘’ₙ_ {Γ' = Γ' ▻' U} (‘Type’ C) x = ‘Type’ (C ‘’ₜₙ x)
_‘’ₙ_ {Γ' = Γ' ▻' U} (‘Term’ C T) x = ‘Term’ (C ‘’ₜₙ x) (T ‘’ₜₙ x)
_‘’ₙ_ {Γ' = Γ' ▻' U} (A ‘→’ B) x = (A ‘’ₙ x) ‘→’ (B ‘’ₙ x)
_‘’ₙ_ {Γ' = Γ' ▻' U} ‘⊤’ x = ‘⊤’
_‘’ₙ_ {Γ' = Γ' ▻' U} ‘⊥’ x = ‘⊥’
_‘’ₙ_ {Γ' = Γ' ▻' U} (wkT₀ T) x = wkT₀ (T ‘’ₙ x)
_‘’ₙ_ {Γ' = Γ' ▻' U} Δ→Type x = Δ→Type

_‘’₁_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
wkT : ∀ {Γ Γ'} → Type Γ → Type (Γ ++ Γ')

wkT {Γ} {ε'} T = T
wkT {Γ} {Γ' ▻' A} T = wkT₀ (wkT T)

wkC : ∀ {Γ Γ'} → ContextOver Γ → ContextOver (Γ ++ Γ')
wkT' : ∀ {Γ₁ Γ₂ Γ₃} → Type (Γ₁ ++ Γ₃) → Type ((Γ₁ ++ Γ₂) ++ wkC Γ₃)

wkC ε' = ε'
wkC {Γ} {Γ'} (Δ ▻' T) = wkC Δ ▻' wkT' {Γ} {Γ'} {Δ} T

wk' : ∀ {Γ₁ Γ₂ Γ₃ A} → Term {Γ₁ ++ Γ₃} A → Term {(Γ₁ ++ Γ₂) ++ wkC Γ₃} (wkT' {Γ₁} {Γ₂} {Γ₃} A)

wkT' {Γ₁} {Γ₂} {ε'} T = wkT T
wkT' {Γ₁} {Γ₂} {Γ₃ ▻' U} ‘Context’ = ‘Context’
wkT' {Γ₁} {Γ₂} {Γ₃ ▻' U} (‘Type’ C) = ‘Type’ (wk' {Γ₁} {Γ₂} {_} C)
wkT' {Γ₁} {Γ₂} {Γ₃ ▻' U} (‘Term’ C T) = ‘Term’ (wk' {Γ₁} {Γ₂} {_} C) (wk' {Γ₁} {Γ₂} {_} T)
wkT' {Γ₁} {Γ₂} {Γ₃ ▻' U} (A ‘→’ B) = (wkT' {Γ₁} {Γ₂} {_} A) ‘→’ (wkT' {Γ₁} {Γ₂} {_} B)
wkT' {Γ₁} {Γ₂} {Γ₃ ▻' U} ‘⊤’ = ‘⊤’
wkT' {Γ₁} {Γ₂} {Γ₃ ▻' U} ‘⊥’ = ‘⊥’
wkT' {Γ₁} {Γ₂} {Γ₃ ▻' U} (wkT₀ T) = wkT₀ (wkT' {Γ₁} {Γ₂} {_} T)
wkT' {Γ₁} {Γ₂} {Γ₃ ▻' U} Δ→Type = Δ→Type

_‘’₁_ = _‘’ₙ_

data Term where
  ⌜_⌝c : ∀ {Γ} → Context → Term {Γ} ‘Context’
  ⌜_⌝ : ∀ {Γ C} → Type C → Term {Γ} (‘Type’ ⌜ C ⌝c)
  ⌜_⌝ₜ : ∀ {Γ C T} → Term {C} T → Term {Γ} (‘Term’ ⌜ C ⌝c ⌜ T ⌝)
  -- _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
  -- _‘’ₜw_ : ∀ {Γ A B} → Term {Γ ▻ A} (wkT B) → (a : Term {Γ} A) → Term {Γ} B
  ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
  var₀ : ∀ {Γ A} → Term {Γ ▻ A} (wkT₀ A)
  -- only strictly necessary for var
  wk : ∀ {Γ A T} → Term {Γ} T → Term {Γ ▻ A} (wkT₀ T)
  -- cast-wkT‘’ : ∀ {Γ A B} {a : Term A} → Term (wkT B ‘’ a) → Term {Γ} B
{-
‘Δ’₀ : ∀ {Γ}
-}

⌜ C ⌝c ‘’ₜ x = ⌜ C ⌝c
⌜ T ⌝ ‘’ₜ x = ⌜ T ⌝
⌜ t ⌝ₜ ‘’ₜ x = ⌜ t ⌝ₜ
‘tt’ ‘’ₜ x = ‘tt’
var₀ ‘’ₜ x = x
wk t ‘’ₜ x = t

Δ : ∀ {Γ} → Type (ε ▻ ‘Type’ ⌜ ε ⌝c) → Type (ε ++ Γ)
Δ {Γ} T = let K = wkT' {ε} {ε' ▻' ‘Type’ ⌜ ε ⌝c} {ε' ▻' ‘Type’ ⌜ ε ⌝c} T ‘’ {!var₀ ‘’ₜ {!!}!} in
              wkT {ε} {Γ} (K ‘’ {!!})


lӧb-helper : ∀ {Γ X} → Term {Γ ▻ ‘Term’ ⌜ Γ ⌝c ⌜ X ⌝} (wkT₀ X) → Term {Γ} X
lӧb-helper f = let K = var₀ ‘’ₜ ⌜ var₀ ⌝ₜ in f ‘’ₜ {!K ‘’ₜ ⌜ K ⌝ₜ!}


⌞_⌟ : Type ε → Set _
⌞ T ⌟ = {!Type⇓ T tt!}

□ : Type ε → Set _
□ = Term {ε}
{-
‘□’ : ∀ {Γ C} → Type (Γ ▻ ‘Type’ C)
‘□’ {Γ} {C} = ‘Term’ C

lӧb : ∀ {‘X’} → □ (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = {!Term⇓ (Lӧb f) tt!}

-}

{-
max-level : Level
max-level = lzero

Context⇓ : (Γ : Context) → Set max-level
Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level

Context⇓ ε = ⊤
Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓

Type⇓ ‘Context’ Γ⇓ = Lifted Context
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

Term⇓ ⌜ C ⌝c Γ⇓ = lift C
Term⇓ ⌜ T ⌝ Γ⇓ = lift T
Term⇓ ⌜ t ⌝ₜ Γ⇓ = lift t
Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
Term⇓ ‘tt’ Γ⇓ = tt
Term⇓ (wk t) Γ⇓ = Term⇓ t (Σ.proj₁ Γ⇓)

⌞_⌟ : Type ε → Set _
⌞ T ⌟ = Type⇓ T tt

‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
‘¬’ T = T ‘→’ ‘⊥’

□ : Type ε → Set _
□ = Term {ε}

‘□’ : ∀ {Γ C} → Type (Γ ▻ ‘Type’ ‘’ C)
‘□’ {Γ} {C} = ‘Term’ ‘’₁ C

lӧb : ∀ {‘X’} → □ (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = {!Term⇓ (Lӧb f) tt!}

incompleteness : ¬ □ (‘¬’ (‘□’ ‘’ ⌜ ‘⊥’ {ε} ⌝))
incompleteness = lӧb

soundness : ¬ □ ‘⊥’
soundness x = Term⇓ x tt

non-emptyness : Σ (Type ε) (λ T → □ T)
non-emptyness = ‘⊤’ , ‘tt’
-}

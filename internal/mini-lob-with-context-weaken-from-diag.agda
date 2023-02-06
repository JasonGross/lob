{-# OPTIONS --without-K --allow-unsolved-metas #-}
module mini-lob-with-context-weaken-from-diag where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixl 3 _‘’₁_
infixr 1 _‘→’_
infixl 3 _‘’ₐ_

module Bias where
  data Bias : Set where
    None : Bias
    Left : Bias → Bias
    Right : Bias → Bias
    Both : Bias → Bias → Bias

  left : Bias → Bias
  left (Left b) = b
  left (Both l r) = l
  left (Right _) = None
  left None = None

  right : Bias → Bias
  right (Right b) = b
  right (Both l r) = r
  right (Left _) = None
  right None = None

open Bias using (Bias)

data Context : Set

data Type : Context → Set
data Context where
  ε : Context
  _▻_ : (Γ : Context) → Type Γ → Context

data Term : {Γ : Context} → Type Γ → Set
data Type where
  _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
  _‘’₁_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
  wkT : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
  ‘Context’ : ∀ {Γ} → Type Γ
  ‘Type’⌜_⌝ : ∀ {Γ} → Context → Type Γ
  ‘Term’ : ∀ {Γ} {C : Context} → Type (Γ ▻ ‘Type’⌜ C ⌝)
  _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  ‘⊤’ : ∀ {Γ} → Type Γ
  ‘⊥’ : ∀ {Γ} → Type Γ
  ‘Set’ : ∀ {Γ} → Type Γ
  ‘Δ’ : ∀ {Γ} → Type (Γ ▻ ‘Type’⌜ Γ ⌝) → Type Γ

red1T : ∀ {Γ} → Bias → Type Γ → Type Γ
red1T' : ∀ {Γ} → Bias → Type Γ → Type Γ

data Term where
  ⌜_⌝c : ∀ {Γ} → Context → Term {Γ} ‘Context’
  ⌜_⌝ : ∀ {Γ C} → Type C → Term {Γ} (‘Type’⌜ C ⌝)
  ⌜_⌝t : ∀ {Γ C T} → Term {C} T → Term {Γ} (‘Term’ ‘’ ⌜ T ⌝)
  _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
  _‘‘’’ₐ_ : ∀ {Γ C A B} → Term {Γ} (‘Term’ {Γ} {C} ‘’ ⌜ A ‘→’ B ⌝) → Term {Γ} (‘Term’ ‘’ ⌜ A ⌝) → Term {Γ} (‘Term’ ‘’ ⌜ B ⌝)
  ‘λ’ : ∀ {Γ A B} → Term {Γ ▻ A} (wkT B) → Term {Γ} (A ‘→’ B)
  var₀ : ∀ {Γ A} → Term {Γ ▻ A} (wkT A)
  wk : ∀ {Γ A T} → Term {Γ} T → Term {Γ ▻ A} (wkT T)
  ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
  wrap : ∀ {Γ F} → Term ((F ‘’ ⌜ ‘Δ’ {Γ} F ⌝) ‘→’ (‘Δ’ {Γ} F))
  unwrap : ∀ {Γ F} → Term ((‘Δ’ {Γ} F) ‘→’ (F ‘’ ⌜ ‘Δ’ {Γ} F ⌝))
  red1 : ∀ {Γ T} → (b : Bias) → Term {Γ} T → Term {Γ} (red1T b T)
  unred1 : ∀ {Γ T} (b : Bias) → Term {Γ} (red1T b T) → Term {Γ} T

_‘’T[_]v_ : ∀ {Γ A} → Type (Γ ▻ A) → Bias -> Term {Γ} A → Type Γ
_‘’₁T[_]v_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → Bias -> (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
wkTv : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
red1t : ∀ {Γ T} → (b : Bias) → Term {Γ} T → Term {Γ} T
(T ‘’ a) ‘’T[ b ]v x = (T ‘’T[ b ]v a) ‘’ x
(T ‘’₁ a) ‘’T[ b ]v x = (T ‘’₁T[ b ]v a) ‘’ x
wkT T ‘’T[ b ]v x = T
‘Context’ ‘’T[ b ]v x = ‘Context’
‘Type’⌜ C ⌝ ‘’T[ b ]v x = ‘Type’⌜ C ⌝
‘Term’ ‘’T[ b ]v T = ‘Term’ ‘’ (red1t b T)
(A ‘→’ B) ‘’T[ b ]v x = (A ‘’ x) ‘→’ (B ‘’ x)
‘⊤’ ‘’T[ b ]v x = ‘⊤’
‘⊥’ ‘’T[ b ]v x = ‘⊥’
‘Set’ ‘’T[ b ]v x = ‘Set’
‘Δ’ T ‘’T[ b ]v x = (‘Δ’ T) ‘’ x
T ‘’₁T[ b ]v x = T ‘’₁ x
wkTv T@(_ ‘’ _) = wkT T
wkTv T@(_ ‘’₁ _) = wkT T
wkTv (wkT T) = wkT (wkTv T)
wkTv ‘Context’ = ‘Context’
wkTv (‘Type’⌜ C ⌝) = ‘Type’⌜ C ⌝
wkTv ‘Term’ = wkT ‘Term’
wkTv (A ‘→’ B) = wkTv A ‘→’ wkTv B
wkTv ‘⊤’ = ‘⊤’
wkTv ‘⊥’ = ‘⊥’
wkTv ‘Set’ = ‘Set’
wkTv T@(‘Δ’ _) = wkT T

red1T Bias.None T = T
red1T b@(Bias.Left _) T = red1T' b T
red1T b@(Bias.Right _) T = red1T' b T
red1T b@(Bias.Both _ _) T = red1T' b T
red1T' b (T ‘’ x) = T ‘’T[ b ]v x
red1T' b (T ‘’₁ a) = T ‘’₁T[ b ]v a
red1T' b (wkT T) = wkTv T
red1T' b T@‘Context’ = T
red1T' b T@(‘Type’⌜ _ ⌝) = T
red1T' b T@‘Term’ = T
red1T' b (A ‘→’ B) = red1T (Bias.left b) A ‘→’ red1T (Bias.right b) B
red1T' b T@‘⊤’ = T
red1T' b T@‘⊥’ = T
red1T' b T@‘Set’ = T
red1T' b (‘Δ’ T) = ‘Δ’ T

red1t b ⌜ T ⌝ = ⌜ red1T b T ⌝
red1t b t@(⌜ _ ⌝c) = t
red1t b ⌜ t ⌝t = ⌜ t ⌝t
red1t b t@(f ‘’ₐ x) = t -- red1t (Bias.left b) f ‘’ₐ red1t (Bias.right b) x
red1t b t@(f ‘‘’’ₐ x) = t -- red1t (Bias.left b) f ‘‘’’ₐ red1t (Bias.right b) x
red1t b t@(‘λ’ f) = t -- ‘λ’ (red1t b f)
red1t b t@var₀ = t
red1t b t@‘tt’ = t
red1t b t@wrap = t
red1t b t@unwrap = t
red1t b t@(red1 _ _) = t
red1t b t@(unred1 _ _) = t
red1t b t@(wk v) = t -- wk (red1t b v)

Lӧb : ∀ {Γ} {X : Type Γ} → Term {Γ} (‘Term’ ‘’ ⌜ X ⌝ ‘→’ X) → Term {Γ} X
Lӧb {Γ} {X} f = {! !}
  where
    --f' : Term {Γ ▻ ‘Term’ ‘’ ⌜ X ⌝} (wkT X)
    --f' = let f' = red1 (wk f) in unred1 (f' ‘’ₐ var₀)

    val : Term {{!!}} (‘Term’ ‘’ ⌜ ‘Δ’ {!!} ⌝)
    val = {!!}

    inf : Term {Γ ▻ ‘Term’ ‘’ ⌜ ‘Δ’ (‘Term’ ‘→’ wkT X) ⌝} (wkT (‘Term’ ‘’ ⌜ X ⌝))
    inf = let r1 = red1 (Bias.Right (Bias.Both Bias.None Bias.None)) in
          let v = r1 (⌜ unwrap ⌝t ‘‘’’ₐ val) in
          unred1 Bias.None {!!}
--  wrap : ∀ {Γ F} → Term (F ‘’ ⌜ ‘Δ’ {Γ} F ⌝) → Term (‘Δ’ {Γ} F)
--  unwrap : ∀ {Γ F} → Term (‘Δ’ {Γ} F) → Term (F ‘’ ⌜ ‘Δ’ {Γ} F ⌝)

    K' : Term {Γ ▻ ‘Term’ ‘’ ⌜ ‘Δ’ (‘Term’ ‘→’ wkT X) ⌝} (wkT X)
    K' = let r1 = red1 (Bias.Both Bias.None Bias.None) in
         let r2 = unred1 (Bias.Both Bias.None Bias.None) in
         let f' = r1 (wk f) in r2 (f' ‘’ₐ inf)

    K : Term {Γ} (‘Δ’ (‘Term’ ‘→’ wkT X))
    K = wrap ‘’ₐ (unred1 Bias.None {!unred1 Bias.None (‘λ’ K')!})


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
Type⇓ (‘Type’⌜ C ⌝) Γ⇓ = Lifted (Type C)
-- Swapping the above two lines causes the following line to error with
{- /home/jgross/Documents/GitHub/lob/internal/mini-lob-with-context.agda:50,67-77
Γ != Γ ▻ A of type Context
when checking that the expression Σ.proj₂ Γ⇓ has type
Type⇓ B (Σ.proj₁ Γ⇓ , Term⇓ a (Σ.proj₁ Γ⇓)) -}
Type⇓ (T ‘’₁ a) Γ⇓ = Type⇓ T ((Σ.proj₁ Γ⇓ , Term⇓ a (Σ.proj₁ Γ⇓)) , Σ.proj₂ Γ⇓)
Type⇓ ‘Term’ Γ⇓ = Lifted (Term (lower (Σ.proj₂ Γ⇓)))
Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
Type⇓ ‘⊤’ Γ⇓ = ⊤
Type⇓ ‘⊥’ Γ⇓ = ⊥
Type⇓ (wkT T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
Type⇓ (‘Δ’ F) Γ⇓ = Type⇓ F (Γ⇓ , lift (‘Δ’ F))
--Type⇓ {Γ} ‘Δ→Type’ Γ⇓ = Term {Γ} ‘Δ→Type’ → Set

red1t⇓Ty1 : ∀ {Γ} (b : Bias) (Γ⇓ : Context⇓ Γ) → (T : Type Γ) → Term T → Set
red1t⇓Ty1 {Γ} b Γ⇓ ‘Type’⌜ C ⌝ T = Term (lower (Term⇓ {Γ} T Γ⇓)) → Term (lower (Term⇓ {Γ} (red1t b T) Γ⇓))
red1t⇓Ty1 b Γ⇓ (T ‘’ x) _ = ⊤
red1t⇓Ty1 b Γ⇓ (T ‘’₁ a) _ = ⊤
red1t⇓Ty1 b Γ⇓ (wkT T) _ = ⊤
red1t⇓Ty1 b Γ⇓ ‘Context’ _ = ⊤
red1t⇓Ty1 b Γ⇓ ‘Term’ _ = ⊤
red1t⇓Ty1 b Γ⇓ (T ‘→’ T₁) _ = ⊤
red1t⇓Ty1 b Γ⇓ ‘⊤’ _ = ⊤
red1t⇓Ty1 b Γ⇓ ‘⊥’ _ = ⊤
red1t⇓Ty1 b Γ⇓ ‘Set’ _ = ⊤
red1t⇓Ty1 b Γ⇓ (‘Δ’ T) _ = ⊤

red1t⇓Ty2 : ∀ {Γ} (b : Bias) (Γ⇓ : Context⇓ Γ) → (T : Type Γ) → Term T → Set
red1t⇓Ty2 {Γ} b Γ⇓ ‘Type’⌜ C ⌝ T = Term (lower (Term⇓ {Γ} (red1t b T) Γ⇓)) → Term (lower (Term⇓ {Γ} T Γ⇓))
red1t⇓Ty2 b Γ⇓ (T ‘’ x) _ = ⊤
red1t⇓Ty2 b Γ⇓ (T ‘’₁ a) _ = ⊤
red1t⇓Ty2 b Γ⇓ (wkT T) _ = ⊤
red1t⇓Ty2 b Γ⇓ ‘Context’ _ = ⊤
red1t⇓Ty2 b Γ⇓ ‘Term’ _ = ⊤
red1t⇓Ty2 b Γ⇓ (T ‘→’ T₁) _ = ⊤
red1t⇓Ty2 b Γ⇓ ‘⊤’ _ = ⊤
red1t⇓Ty2 b Γ⇓ ‘⊥’ _ = ⊤
red1t⇓Ty2 b Γ⇓ ‘Set’ _ = ⊤
red1t⇓Ty2 b Γ⇓ (‘Δ’ T) _ = ⊤

--


red1⇓ : ∀ {Γ} b T Γ⇓ → Type⇓ {Γ} T Γ⇓ → Type⇓ {Γ} (red1T b T) Γ⇓
unred1⇓ : ∀ {Γ} b T Γ⇓ → Type⇓ {Γ} (red1T b T) Γ⇓ → Type⇓ {Γ} T Γ⇓
red1⇓' : ∀ {Γ} b T Γ⇓ → Type⇓ {Γ} T Γ⇓ → Type⇓ {Γ} (red1T' b T) Γ⇓
unred1⇓' : ∀ {Γ} b T Γ⇓ → Type⇓ {Γ} (red1T' b T) Γ⇓ → Type⇓ {Γ} T Γ⇓
red1t⇓ : ∀ {Γ T} b (t : Term {Γ} T) Γ⇓ → red1t⇓Ty1 b Γ⇓ T t
red1t⇓⇑ : ∀ {Γ T} b (t : Term {Γ} T) Γ⇓ → red1t⇓Ty2 b Γ⇓ T t
_‘’Tv⇓_ : ∀ {Γ A T x Γ⇓ b} → Type⇓ {Γ ▻ A} T (Γ⇓ , Term⇓ x Γ⇓) → Type⇓ (T ‘’T[ b ]v x) Γ⇓
_‘’Tv⇓⇑_ : ∀ {Γ A T x Γ⇓ b} → Type⇓ (T ‘’T[ b ]v x) Γ⇓ → Type⇓ {Γ ▻ A} T (Γ⇓ , Term⇓ x Γ⇓)
--_‘’₁Tv⇓_ : ∀ {Γ A B T a Γ⇓} → Type⇓ {Γ ▻ A ▻ B} T (Γ⇓ , Term⇓ x Γ⇓) → Type⇓ (T ‘’T[ b ]v x) Γ⇓
--: ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
wkTv⇓ : ∀ {Γ A} T Γ⇓ → Type⇓ T (Σ.proj₁ Γ⇓) → Type⇓ (wkTv {Γ} {A} T) Γ⇓
wkTv⇓⇑ : ∀ {Γ A} T Γ⇓ → Type⇓ (wkTv {Γ} {A} T) Γ⇓ → Type⇓ T (Σ.proj₁ Γ⇓)
_‘’Tv⇓_ {Γ} {A} {T ‘’ a} {x} {Γ⇓} {b} v = _‘’Tv⇓_ {_} {_} {T} {a} {Γ⇓ , Term⇓ x Γ⇓} {b} v
_‘’Tv⇓_ {Γ} {.(_ ‘’ a)} {T ‘’₁ a} {x} {Γ⇓} {b} v = v
_‘’Tv⇓_ {Γ} {A} {wkT T} {x} {Γ⇓} v = v
_‘’Tv⇓_ {Γ} {A} {‘Context’} {x} {Γ⇓} v = v
_‘’Tv⇓_ {Γ} {A} {‘Type’⌜ _ ⌝} {x} {Γ⇓} v = v
_‘’Tv⇓_ {Γ} {._} {‘Term’} {T} {Γ⇓} {b} v = lift (red1t⇓ b T Γ⇓ (lower v))
_‘’Tv⇓_ {Γ} {A} {T ‘→’ T₁} {x} {Γ⇓} v = v
_‘’Tv⇓_ {Γ} {A} {‘⊤’} {x} {Γ⇓} v = v
_‘’Tv⇓_ {Γ} {A} {‘Set’} {x} {Γ⇓} v = v
_‘’Tv⇓_ {Γ} {A} {‘Δ’ T} {x} {Γ⇓} v = v
_‘’Tv⇓⇑_ {Γ} {A} {T ‘’ a} {x} {Γ⇓} {b} v = _‘’Tv⇓⇑_ {_} {_} {T} {a} {Γ⇓ , Term⇓ x Γ⇓} {b} v
_‘’Tv⇓⇑_ {Γ} {.(_ ‘’ a)} {T ‘’₁ a} {b} {Γ⇓} v = v
_‘’Tv⇓⇑_ {Γ} {A} {wkT T} {x} {Γ⇓} v = v
_‘’Tv⇓⇑_ {Γ} {A} {‘Context’} {x} {Γ⇓} v = v
_‘’Tv⇓⇑_ {Γ} {A} {‘Type’⌜ _ ⌝} {x} {Γ⇓} v = v
_‘’Tv⇓⇑_ {Γ} {._} {‘Term’} {T} {Γ⇓} {b} v = lift (red1t⇓⇑ b T Γ⇓ (lower v))
_‘’Tv⇓⇑_ {Γ} {A} {T ‘→’ T₁} {x} {Γ⇓} v = v
_‘’Tv⇓⇑_ {Γ} {A} {‘⊤’} {x} {Γ⇓} v = v
_‘’Tv⇓⇑_ {Γ} {A} {‘Set’} {x} {Γ⇓} v = v
_‘’Tv⇓⇑_ {Γ} {A} {‘Δ’ T} {x} {Γ⇓} v = v
{-
_‘’₁Tv_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
(T ‘’ a) ‘’T[ b ]v b = (T ‘’T[ b ]v a) ‘’ b
(T ‘’₁ a) ‘’T[ b ]v b = (T ‘’₁Tv a) ‘’ b
wkT T ‘’T[ b ]v x = T
‘Context’ ‘’T[ b ]v x = ‘Context’
‘Type’⌜ C ⌝ ‘’T[ b ]v x = ‘Type’⌜ C ⌝
‘Term’ ‘’T[ b ]v T = ‘Term’ ‘’ T
(A ‘→’ B) ‘’T[ b ]v x = (A ‘’ x) ‘→’ (B ‘’ x)
‘⊤’ ‘’T[ b ]v x = ‘⊤’
‘⊥’ ‘’T[ b ]v x = ‘⊥’
‘Set’ ‘’T[ b ]v x = ‘Set’
‘Δ’ T ‘’T[ b ]v x = (‘Δ’ T) ‘’ x
_‘’₁Tv_ = _‘’₁_
wkTv : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
-}
wkTv⇓ (T ‘’ x) Γ⇓ v = v
wkTv⇓ (T ‘’₁ a) Γ⇓ v = v
wkTv⇓ (wkT T) Γ⇓ v = wkTv⇓ T (Σ.proj₁ Γ⇓) v
wkTv⇓ ‘Context’ Γ⇓ v = v
wkTv⇓ (‘Type’⌜ x ⌝) Γ⇓ v = v
wkTv⇓ ‘Term’ Γ⇓ v = v
wkTv⇓ (A ‘→’ B) Γ⇓ f x = wkTv⇓ B _ (f (wkTv⇓⇑ A _ x))
wkTv⇓ ‘⊤’ Γ⇓ v = v
wkTv⇓ ‘Set’ Γ⇓ v = v
wkTv⇓ (‘Δ’ T) Γ⇓ v = v
wkTv⇓⇑ (T ‘’ x) Γ⇓ v = v
wkTv⇓⇑ (T ‘’₁ a) Γ⇓ v = v
wkTv⇓⇑ (wkT T) Γ⇓ v = wkTv⇓⇑ T (Σ.proj₁ Γ⇓) v
wkTv⇓⇑ ‘Context’ Γ⇓ v = v
wkTv⇓⇑ (‘Type’⌜ C ⌝) Γ⇓ v = v
wkTv⇓⇑ ‘Term’ Γ⇓ v = v
wkTv⇓⇑ (A ‘→’ B) Γ⇓ f x = wkTv⇓⇑ B _ (f (wkTv⇓ A _ x))
wkTv⇓⇑ ‘⊤’ Γ⇓ v = v
wkTv⇓⇑ ‘Set’ Γ⇓ v = v
wkTv⇓⇑ (‘Δ’ T) Γ⇓ v = v
red1⇓ Bias.None T Γ⇓ v = v
red1⇓ b@(Bias.Left _) T Γ⇓ v = red1⇓' b T Γ⇓ v
red1⇓ b@(Bias.Right _) T Γ⇓ v = red1⇓' b T Γ⇓ v
red1⇓ b@(Bias.Both _ _) T Γ⇓ v = red1⇓' b T Γ⇓ v
red1⇓' b (T ‘’ x) Γ⇓ v = _‘’Tv⇓_ {_} {_} {T} {x} {Γ⇓} {b} v
red1⇓' b (T ‘’₁ a) Γ⇓ v = v
red1⇓' b (wkT T) Γ⇓ v = wkTv⇓ T Γ⇓ v
red1⇓' b ‘Context’ Γ⇓ v = v
red1⇓' b (‘Type’⌜ _ ⌝) Γ⇓ v = v
red1⇓' b ‘Term’ Γ⇓ v = v
red1⇓' b (A ‘→’ B) Γ⇓ f x = red1⇓ (Bias.right b) B Γ⇓ (f (unred1⇓ (Bias.left b) A Γ⇓ x))
red1⇓' b ‘⊤’ Γ⇓ v = v
red1⇓' b ‘Set’ Γ⇓ v = v
red1⇓' b (‘Δ’ T) Γ⇓ v = v
unred1⇓ Bias.None T Γ⇓ v = v
unred1⇓ b@(Bias.Left _) T Γ⇓ v = unred1⇓' b T Γ⇓ v
unred1⇓ b@(Bias.Right _) T Γ⇓ v = unred1⇓' b T Γ⇓ v
unred1⇓ b@(Bias.Both _ _) T Γ⇓ v = unred1⇓' b T Γ⇓ v
unred1⇓' b (T ‘’ x) Γ⇓ v = _‘’Tv⇓⇑_ {_} {_} {T} {x} {Γ⇓} {b} v
unred1⇓' b (T ‘’₁ a) Γ⇓ v = v
unred1⇓' b (wkT T) Γ⇓ v = wkTv⇓⇑ T Γ⇓ v
unred1⇓' b ‘Context’ Γ⇓ v = v
unred1⇓' b (‘Type’⌜ C ⌝) Γ⇓ v = v
unred1⇓' b ‘Term’ Γ⇓ v = v
unred1⇓' b (A ‘→’ B) Γ⇓ f x = unred1⇓ (Bias.right b) B Γ⇓ (f (red1⇓ (Bias.left b) A Γ⇓ x))
unred1⇓' b ‘⊤’ Γ⇓ v = v
unred1⇓' b ‘Set’ Γ⇓ v = v
unred1⇓' b (‘Δ’ T) Γ⇓ v = v

red1t⇓-helper : ∀ {Γ C T} b → let t = ⌜_⌝ {Γ} {C} T in ∀ Γ⇓ → red1t⇓Ty1 {Γ} b Γ⇓ _ t

red1t⇓ b ⌜ x ⌝c Γ⇓ = tt
red1t⇓ b ⌜ T ⌝ Γ⇓ t = red1t⇓-helper b Γ⇓ t
red1t⇓ b ⌜ T ⌝t Γ⇓ = tt
red1t⇓ b (T ‘’ₐ T₁) Γ⇓ = {!!}
red1t⇓ b (T ‘‘’’ₐ T₁) Γ⇓ = tt
red1t⇓ b (‘λ’ T) Γ⇓ = tt
red1t⇓ b var₀ Γ⇓ = tt
red1t⇓ b (wk T) Γ⇓ = tt
red1t⇓ b ‘tt’ Γ⇓ = tt
red1t⇓ b wrap Γ⇓ = tt
red1t⇓ b unwrap Γ⇓ = tt
red1t⇓ b (red1 b₁ T) Γ⇓ = {!!}
red1t⇓ b (unred1 b₁ T) Γ⇓ = {!!}
red1t⇓⇑ b ⌜ x ⌝c Γ⇓ = tt
red1t⇓⇑ b ⌜ x ⌝ Γ⇓ = {!!}
red1t⇓⇑ b ⌜ T ⌝t Γ⇓ = tt
red1t⇓⇑ b (T ‘’ₐ T₁) Γ⇓ = {!!}
red1t⇓⇑ b (T ‘‘’’ₐ T₁) Γ⇓ = tt
red1t⇓⇑ b (‘λ’ T) Γ⇓ = tt
red1t⇓⇑ b var₀ Γ⇓ = tt
red1t⇓⇑ b (wk T) Γ⇓ = tt
red1t⇓⇑ b ‘tt’ Γ⇓ = tt
red1t⇓⇑ b wrap Γ⇓ = tt
red1t⇓⇑ b unwrap Γ⇓ = tt
red1t⇓⇑ b (red1 b₁ T) Γ⇓ = {!!}
red1t⇓⇑ b (unred1 b₁ T) Γ⇓ = {!!}

Term⇓ ⌜ C ⌝c Γ⇓ = lift C
Term⇓ ⌜ T ⌝ Γ⇓ = lift T
Term⇓ ⌜ t ⌝t Γ⇓ = lift t
Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
Term⇓ (f ‘‘’’ₐ x) Γ⇓ = lift (lower (Term⇓ f Γ⇓) ‘’ₐ lower (Term⇓ x Γ⇓))
--Term⇓ (Lӧb □‘X’→X) Γ⇓ = Term⇓ □‘X’→X Γ⇓ (lift (Lӧb □‘X’→X))
Term⇓ ‘tt’ Γ⇓ = tt
Term⇓ var₀ Γ⇓ = Σ.proj₂ Γ⇓
Term⇓ (‘λ’ f) Γ⇓ x = Term⇓ f (Γ⇓ , x)
Term⇓ (wk t) Γ⇓ = Term⇓ t (Σ.proj₁ Γ⇓)
Term⇓ wrap Γ⇓ x = x
Term⇓ unwrap Γ⇓ x = x
Term⇓ (red1 {Γ} {T} b t) Γ⇓ = red1⇓ b T Γ⇓ (Term⇓ t Γ⇓)
Term⇓ (unred1 {Γ} {T} b t) Γ⇓ = unred1⇓ b T Γ⇓ (Term⇓ t Γ⇓)

red1t⇓-helper b Γ⇓ = red1 b

⌞_⌟ : Type ε → Set _
⌞ T ⌟ = Type⇓ T tt

‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
‘¬’ T = T ‘→’ ‘⊥’

□ : Type ε → Set _
□ = Term {ε}

‘□’ : ∀ {Γ C} → Type (Γ ▻ ‘Type’⌜ C ⌝)
‘□’ {Γ} {C} = ‘Term’ {_} {C}

lӧb : ∀ {‘X’} → □ (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = Term⇓ (Lӧb f) tt

incompleteness : ¬ □ (‘¬’ (‘□’ ‘’ ⌜ ‘⊥’ {ε} ⌝))
incompleteness pf = ⊥-elim (lӧb pf)

soundness : ¬ □ ‘⊥’
soundness x = ⊥-elim (Term⇓ x tt)

non-emptyness : Σ (Type ε) (λ T → □ T)
non-emptyness = ‘⊤’ , ‘tt’

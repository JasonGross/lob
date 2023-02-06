{-# OPTIONS --without-K --allow-unsolved-metas #-}
module mini-lob-contextual-dependent-from-diagonal-language where
open import common

infixl 2 _▻_
infixl 2 _‘▻’_
infixl 3 _‘’_
infixl 3 _‘’₁_
infixr 1 _‘→’_
infixr 1 _‘‘→’’_
infixr 2 _‘×’_
infixr 2 _‘××’_
infixr 2 _‘××Σ’_
infixr 1 _‘≡’_
infixl 3 _‘’ₐ_
infixl 3 _‘’Πₐ_
infixl 3 _‘∘’_
infixl 3 _‘⨾’_

data Context : Set
data Type : Context → Set
data Term : {Γ : Context} → Type Γ → Set

data Context where
  ε : Context
  _▻_ : (Γ : Context) → Type Γ → Context

‘Type’⌜_⌝ : ∀ {Γ} → Context → Type Γ

data Type where
  _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
  _‘’₁_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
  Wk : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
  Wk₁ : ∀ {Γ A B} → Type (Γ ▻ B) → Type (Γ ▻ A ▻ Wk B)
  _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  _‘×’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  ‘Π’ : ∀ {Γ} A → Type (Γ ▻ A) → Type Γ
  ‘Σ’ : ∀ {Γ} A → Type (Γ ▻ A) → Type Γ
  ‘⊤’ : ∀ {Γ} → Type Γ
  ‘⊥’ : ∀ {Γ} → Type Γ
  ‘Eq’ : ∀ {Γ A} → Type (Γ ▻ A ▻ Wk A)
  ‘Context’ : ∀ {Γ} → Type Γ
  ‘Type’ : ∀ {Γ} → Type (Γ ▻ ‘Context’)
  ‘Term’ : ∀ {Γ} → Type (Γ ▻ ‘Context’ ▻ ‘Type’)
  ‘Δ’ : ∀ {Γ} → Type (Γ ▻ ‘Type’⌜ Γ ⌝) → Type Γ

_‘≡’_ : ∀ {Γ A} → Term {Γ} A → Term {Γ} A → Type Γ

red1 : ∀ {Γ} → Type Γ → Type Γ
subst1 : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
subst1₁ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
Wk1 : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
Wk1₁ : ∀ {Γ A B} → Type (Γ ▻ B) → Type (Γ ▻ A ▻ Wk B)
red1 (T ‘’ x) = subst1 T x
red1 (T ‘’₁ a) = subst1₁ T a
red1 ‘Context’ = ‘Context’
red1 ‘Type’ = ‘Type’
red1 ‘Term’ = ‘Term’
red1 (A ‘→’ B) = (red1 A) ‘→’ (red1 B)
red1 (A ‘×’ B) = (red1 A) ‘×’ (red1 B)
red1 ‘⊤’ = ‘⊤’
red1 ‘⊥’ = ‘⊥’
red1 (‘Σ’ A B) = ‘Σ’ A (red1 B)
red1 (‘Π’ A B) = ‘Π’ A (red1 B)
red1 (Wk T) = Wk1 T
red1 (Wk₁ T) = Wk1₁ T
red1 ‘Eq’ = ‘Eq’
red1 (‘Δ’ T) = ‘Δ’ T
Wk1 T@(_ ‘’ _) = Wk (red1 T)
Wk1 T@(_ ‘’₁ _) = Wk (red1 T)
Wk1 ‘Context’ = ‘Context’
Wk1 T@‘Type’ = Wk (red1 T)
Wk1 T@‘Term’ = Wk (red1 T)
Wk1 (A ‘→’ B) = Wk A ‘→’ Wk B
Wk1 (A ‘×’ B) = Wk A ‘×’ Wk B
Wk1 ‘⊤’ = ‘⊤’
Wk1 ‘⊥’ = ‘⊥’
Wk1 (‘Σ’ A B) = ‘Σ’ (Wk A) (Wk₁ B)
Wk1 (‘Π’ A B) = ‘Π’ (Wk A) (Wk₁ B)
Wk1 (Wk T) = Wk (Wk1 T)
Wk1 T@(Wk₁ _) = Wk (red1 T)
Wk1 T@‘Eq’ = Wk (red1 T)
Wk1 T@(‘Δ’ _) = Wk (red1 T)
Wk1₁ T@(_ ‘’ _) = Wk₁ (red1 T)
Wk1₁ T@(_ ‘’₁ _) = Wk₁ (red1 T)
Wk1₁ T@‘Context’ = Wk₁ (red1 T)
Wk1₁ T@‘Type’ = Wk₁ (red1 T)
Wk1₁ T@‘Term’ = Wk₁ (red1 T)
Wk1₁ (A ‘→’ B) = Wk₁ A ‘→’ Wk₁ B
Wk1₁ (A ‘×’ B) = Wk₁ A ‘×’ Wk₁ B
Wk1₁ ‘⊤’ = ‘⊤’
Wk1₁ ‘⊥’ = ‘⊥’
Wk1₁ T@(‘Σ’ A B) = Wk₁ (red1 T)
Wk1₁ T@(‘Π’ A B) = Wk₁ (red1 T)
Wk1₁ T@(Wk _) = Wk₁ (red1 T)
Wk1₁ T@(Wk₁ _) = Wk₁ (red1 T)
Wk1₁ T@‘Eq’ = Wk₁ (red1 T)
Wk1₁ T@(‘Δ’ _) = Wk₁ (red1 T)

subst1 (T ‘’ a) b = (subst1 T a) ‘’ b
subst1 (T ‘’₁ a) b = (subst1₁ T a) ‘’ b
subst1 ‘Context’ x = ‘Context’
subst1 T@‘Type’ x = T ‘’ x
subst1 T@‘Term’ t = T ‘’ t
subst1 (A ‘→’ B) x = A ‘’ x ‘→’ B ‘’ x
subst1 (A ‘×’ B) x = A ‘’ x ‘×’ B ‘’ x
subst1 ‘⊤’ x = ‘⊤’
subst1 ‘⊥’ x = ‘⊥’
subst1 (‘Σ’ A B) x = ‘Σ’ (A ‘’ x) (B ‘’₁ x)
subst1 (‘Π’ A B) x = ‘Π’ (A ‘’ x) (B ‘’₁ x)
subst1 (Wk T) x = T
subst1 (Wk₁ T) x = Wk1₁ T ‘’ x
subst1 T@‘Eq’ x = T ‘’ x
subst1 T@(‘Δ’ _) x = T ‘’ x
subst1₁ (T ‘’ a) b = ((subst1 T a) ‘’₁ b)
subst1₁ (T ‘’₁ a) b = ((subst1₁ T a) ‘’₁ b)
subst1₁ ‘Context’ x = ‘Context’
subst1₁ T@‘Type’ x = T ‘’₁ x
subst1₁ T@‘Term’ t = T ‘’₁ t
subst1₁ (A ‘→’ B) x = (A ‘’₁ x ‘→’ B ‘’₁ x)
subst1₁ (A ‘×’ B) x = (A ‘’₁ x ‘×’ B ‘’₁ x)
subst1₁ ‘⊤’ x = ‘⊤’
subst1₁ ‘⊥’ x = ‘⊥’
subst1₁ T@(‘Σ’ A B) x = T ‘’₁ x
subst1₁ T@(‘Π’ A B) x = T ‘’₁ x
subst1₁ (Wk T) x = Wk T ‘’₁ x
subst1₁ (Wk₁ T) x = Wk₁ T ‘’₁ x
subst1₁ T@‘Eq’ x = T ‘’₁ x
subst1₁ T@(‘Δ’ _) x = T ‘’₁ x

red1n : ℕ → ∀ {Γ} → Type Γ → Type Γ
red1n zero T = T
red1n (suc n) T = red1n n (red1 T)

⌜_⌝' : ∀ {Γ C} → Type C → Term {Γ} (‘Type’⌜ C ⌝)
⌜_⌝c : ∀ {Γ} → Context → Term {Γ} ‘Context’
_‘▻’_ : ∀ {Γ} → (C : Term {Γ} ‘Context’) → Term {Γ} (‘Type’ ‘’ C) → Term {Γ} ‘Context’

data Term where
  ⌜_⌝ : ∀ {Γ C} → Type C → Term {Γ} (‘Type’ ‘’ ⌜ C ⌝c)
  ⌜_⌝t : ∀ {Γ C T} → Term {C} T → Term {Γ} (‘Term’ ‘’₁ ⌜ C ⌝c ‘’ ⌜ T ⌝)
  ‘ε’ : ∀ {Γ} → Term {Γ} ‘Context’
  ‘ext’ : ∀ {Γ} → Term {Γ} (‘Π’ ‘Context’ (‘Type’ ‘→’ ‘Context’))
  ‘id’ : ∀ {Γ A} → Term {Γ} (A ‘→’ A)
  wk→ : ∀ {Γ A B C} → Term {Γ} (A ‘→’ B) → Term {Γ ▻ C} (Wk A ‘→’ Wk B)
  var₀ : ∀ {Γ A} → Term {Γ ▻ A} (Wk A)
  wk : ∀ {Γ A B C} → Term {Γ ▻ A} C → Term {Γ ▻ A ▻ B} (Wk C)
  ‘quote’ : ∀ {Γ Γ′ C T} → Term {Γ} (‘Term’ ‘’₁ ⌜ C ⌝c ‘’ ⌜ T ⌝ ‘→’ ‘Term’ ‘’₁ ⌜ Γ′ ⌝c ‘’ ⌜ ‘Term’ ‘’₁ ⌜ C ⌝c ‘’ ⌜ T ⌝ ⌝)
  ‘eval’ : ∀ {Γ A B} → Term {Γ} (((A ‘→’ B) ‘×’ A) ‘→’ B)
  ‘curry’ : ∀ {Γ A B C} → Term {Γ} ((A ‘×’ B ‘→’ C) ‘→’ (A ‘→’ (B ‘→’ C)))
  ‘uncurry’ : ∀ {Γ A B C} → Term {Γ} ((A ‘→’ (B ‘→’ C)) ‘→’ (A ‘×’ B ‘→’ C))
  _‘,’_ : ∀ {Γ A B} → Term {Γ} A → Term {Γ} B → Term {Γ} (A ‘×’ B)
  _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
  _‘’Πₐ_ : ∀ {Γ A B} → Term {Γ} (‘Π’ A B) → (a : Term {Γ} A) → Term {Γ} (B ‘’ a)
  ‘pairΣ’ : ∀ {Γ A B} → Term {Γ} (‘Π’ A (B ‘→’ Wk (‘Σ’ A B)))
  ‘const’ : ∀ {Γ A B} → Term {Γ} B → Term {Γ} (A ‘→’ B)
  ‘dup’ : ∀ {Γ A} → Term {Γ} (A ‘→’ A ‘×’ A)
  ‘proj₁’ : ∀ {Γ A B} → Term {Γ} (‘Σ’ A B ‘→’ A)
  _‘∘’_ : ∀ {Γ A B C} → Term {Γ} (B ‘→’ C) → Term {Γ} (A ‘→’ B) → Term {Γ} (A ‘→’ C)
  ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
  ‘refl’ : ∀ {Γ A} {x : Term {Γ} A} → Term (x ‘≡’ x)
  ‘λ’ : ∀ {Γ A B} → Term {Γ ▻ A} B → Term {Γ} (‘Π’ A B)
  ‘λ→’ : ∀ {Γ A B} → Term {Γ ▻ A} (Wk B) → Term {Γ} (A ‘→’ B)
  red1→ : ∀ {Γ A} → Term {Γ} A → Term (red1 A)
  red1← : ∀ {Γ A} → Term {Γ} (red1 A) → Term A
  _‘××’_ : ∀ {Γ A B C D} → Term {Γ} (A ‘→’ C) → Term {Γ} (B ‘→’ D) → Term {Γ} (A ‘×’ B ‘→’ C ‘×’ D)
  _‘××Σ’_ : ∀ {Γ A B A′ B′} → (f : Term {Γ} (A ‘→’ A′)) → Term {Γ} (‘Π’ A (B ‘→’ Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → Term {Γ} (‘Σ’ A B ‘→’ ‘Σ’ A′ B′)
  _‘××Σ'’_ : ∀ {Γ A B A′ B′} → (f : Term {Γ} (‘Σ’ A B ‘→’ A′)) → Term {Γ} (‘Π’ (‘Σ’ A B) (Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → Term {Γ} (‘Σ’ A B ‘→’ ‘Σ’ A′ B′)
  ‘‘’’ₐ : ∀ {Γ C A B} → Term {Γ} (‘Term’ ‘’₁ ⌜ C ⌝c ‘’ ⌜ A ‘→’ B ⌝ ‘→’ ‘Term’ ‘’₁ ⌜ C ⌝c  ‘’ ⌜ A ⌝ ‘→’ ‘Term’ ‘’₁ ⌜ C ⌝c ‘’ ⌜ B ⌝)
  ‘‘Eq’’ : ∀ {Γ C A} → Term {Γ} (‘Term’ ‘’₁ ⌜ C ⌝c ‘’ A ‘→’ ‘Term’ ‘’₁ ⌜ C ⌝c ‘’ A ‘→’ ‘Type’⌜ C ⌝)
  ‘‘,’’ : ∀ {Γ C A B} → Term {Γ} (‘Term’ ‘’₁ ⌜ C ⌝c ‘’ ⌜ A ⌝ ‘×’ ‘Term’ ‘’₁ ⌜ C ⌝c ‘’ ⌜ B ⌝ ‘→’ ‘Term’ ‘’₁ ⌜ C ⌝c ‘’ ⌜ A ‘×’ B ⌝)
  ‘‘Exp’’ : ∀ {Γ C} → Term {Γ} (‘Type’ ‘’ ⌜ C ⌝c ‘×’ ‘Type’ ‘’ ⌜ C ⌝c ‘→’ ‘Type’ ‘’ ⌜ C ⌝c)
  ‘‘Σ’’ : ∀ {Γ C} → Term {Γ} (‘Σ’ (‘Type’ ‘’ ⌜ C ⌝c) (Wk₁ ‘Type’ ‘’ red1← (⌜ C ⌝c ‘▻’ {!red1← (red1← var₀) !})) ‘→’ ‘Type’ ‘’ ⌜ C ⌝c)
--  ∀ {Γ} A → Type (Γ ▻ A) → Type Γ
  ‘Δ-fwd’ : ∀ {Γ T} → Term {Γ} (‘Δ’ T ‘→’ (T ‘’ ⌜ ‘Δ’ T ⌝'))
  ‘Δ-bak’ : ∀ {Γ T} → Term {Γ} (T ‘’ ⌜ ‘Δ’ T ⌝') → Term (‘Δ’ T)
  ‘‘Δ-bak’’ : ∀ {Γ C T} → Term {Γ} (‘Term’ ‘’₁ ⌜ C ⌝c ‘’ ⌜ T ‘’ ⌜ ‘Δ’ T ⌝' ⌝ ‘→’ ‘Term’ ‘’₁ ⌜ C ⌝c ‘’ ⌜ ‘Δ’ T ⌝)
  ‘Δ’-point-surjection : ∀ {Γ T} {f : Term {Γ} (T ‘’ ⌜ ‘Δ’ T ⌝')} → Term (‘Δ-fwd’ ‘’ₐ (‘Δ-bak’ f) ‘≡’ f)

‘Type’⌜ C ⌝ = ‘Type’ ‘’ ⌜ C ⌝c
⌜_⌝' = ⌜_⌝
C ‘▻’ T = red1→ (red1→ (‘ext’ ‘’Πₐ C)) ‘’ₐ T
⌜ ε ⌝c = ‘ε’
⌜ C ▻ T ⌝c = ⌜ C ⌝c ‘▻’ ⌜ T ⌝
_‘‘→’’_ : ∀ {Γ C} → Term {Γ} (‘Type’ ‘’ ⌜ C ⌝c) → Term {Γ} (‘Type’ ‘’ ⌜ C ⌝c) → Term {Γ} (‘Type’ ‘’ ⌜ C ⌝c)
_‘‘→’’_ {Γ} {C} A B = ‘‘Exp’’ {Γ} {C} ‘’ₐ (A ‘,’ B)
a ‘≡’ b = ‘Eq’ ‘’₁ a ‘’ red1← b

red1n→ : ∀ {Γ A} n → Term {Γ} A → Term (red1n n A)
red1n→ zero t = t
red1n→ (suc n) t = red1n→ n (red1→ t)

red1n← : ∀ {Γ A} n → Term {Γ} (red1n n A) → Term A
red1n← zero t = t
red1n← (suc n) t = red1← (red1n← n t)

_‘,Σ’_ : ∀ {Γ A B} → (a : Term {Γ} A) → Term {Γ} (B ‘’ a) → Term {Γ} (‘Σ’ A B)
a ‘,Σ’ b = red1n→ (suc (suc zero)) (‘pairΣ’ ‘’Πₐ a) ‘’ₐ red1→ b

□ : Type ε → Set _
□ = Term {ε}

max-level : Level
max-level = lsuc lzero

Context⇓ : (Γ : Context) → Set max-level
Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓

Context⇓ ε = ⊤
Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

Type⇓Wk₁ : ∀ {Γ A B} (T : Type (Γ ▻ B)) → Context⇓ (Γ ▻ A ▻ Wk B) → Set max-level
Type⇓‘Type’ : ∀ {Γ} → Context⇓ (Γ ▻ ‘Context’) → Set max-level
Type⇓‘Term’ : ∀ {Γ} → Context⇓ (Γ ▻ ‘Context’ ▻ ‘Type’) → Set max-level
Type⇓‘Eq’ : ∀ {Γ A} → Context⇓ (Γ ▻ A ▻ Wk A) → Set max-level
Type⇓‘Δ’ : ∀ {Γ} → Type (Γ ▻ ‘Type’⌜ Γ ⌝) → Context⇓ Γ → Set max-level
Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
Type⇓ (T ‘’₁ x) Γ⇓ = Type⇓ T ((Σ.proj₁ Γ⇓ , Term⇓ x (Σ.proj₁ Γ⇓)) , Σ.proj₂ Γ⇓)
Type⇓ ‘Context’ Γ⇓ = Lifted Context
Type⇓ (‘Type’ {Γ}) Γ⇓ = Type⇓‘Type’ {Γ} Γ⇓
Type⇓ (‘Term’ {Γ}) Γ⇓ = Type⇓‘Term’ {Γ} Γ⇓
Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
Type⇓ (A ‘×’ B) Γ⇓ = Type⇓ A Γ⇓ × Type⇓ B Γ⇓
Type⇓ ‘⊤’ Γ⇓ = ⊤
Type⇓ ‘⊥’ Γ⇓ = ⊥
Type⇓ (‘Σ’ A B) Γ⇓ = Σ (Type⇓ A Γ⇓) (λ a → Type⇓ B (Γ⇓ , a))
Type⇓ (‘Π’ A B) Γ⇓ = (a : Type⇓ A Γ⇓) → Type⇓ B (Γ⇓ , a)
Type⇓ (Wk T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
Type⇓ (Wk₁ {Γ} {A} {B} T) Γ⇓ = Type⇓Wk₁ {Γ} {A} {B} T Γ⇓
Type⇓ (‘Eq’ {Γ} {A}) Γ⇓ = Type⇓‘Eq’ {Γ} {A} Γ⇓
Type⇓ (‘Δ’ {Γ} T) Γ⇓ = Type⇓‘Δ’ {Γ} T Γ⇓
Type⇓Wk₁ T Γ⇓ = Type⇓ T (Σ.proj₁ (Σ.proj₁ Γ⇓) , Σ.proj₂ Γ⇓)
Type⇓‘Type’ Γ⇓ = Lifted (Type (lower (Σ.proj₂ Γ⇓)))
Type⇓‘Term’ Γ⇓ = Lifted (Term (lower (Σ.proj₂ Γ⇓)))
Type⇓‘Eq’ Γ⇓ = Σ.proj₂ (Σ.proj₁ Γ⇓) ≡ Σ.proj₂ Γ⇓

Term⇓-‘Δ’-point-surjection : ∀ {Γ T} {f : Term {Γ} (T ‘’ ⌜ ‘Δ’ T ⌝)}
      → ∀ Γ⇓ → Type⇓ (‘Δ-fwd’ ‘’ₐ (‘Δ-bak’ f) ‘≡’ f) Γ⇓
Term⇓-‘××Σ’ : ∀ {Γ} {A} {B} {A′} {B′} (f : Term {Γ} (A ‘→’ A′)) → Term {Γ} (‘Π’ A (B ‘→’ Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → ∀ Γ⇓ → Type⇓ (‘Σ’ A B ‘→’ ‘Σ’ A′ B′) Γ⇓
Term⇓-‘××Σ'’ : ∀ {Γ} {A} {B} {A′} {B′} (f : Term {Γ} (‘Σ’ A B ‘→’ A′)) → Term {Γ} (‘Π’ (‘Σ’ A B) (Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → ∀ Γ⇓ → Type⇓ (‘Σ’ A B ‘→’ ‘Σ’ A′ B′) Γ⇓

Term⇓-red1↔ : ∀ {Γ} (T : Type Γ) Γ⇓ → Type⇓ T Γ⇓ ↔ Type⇓ (red1 T) Γ⇓
Term⇓-subst1↔ : ∀ {Γ A} → (T : Type (Γ ▻ A)) (a : Term {Γ} A) → ∀ Γ⇓ → Type⇓ T (Γ⇓ , Term⇓ a Γ⇓) ↔ Type⇓ (subst1 T a) Γ⇓
Term⇓-subst1₁↔ : ∀ {Γ A B} → (T : Type (Γ ▻ A ▻ B)) → (a : Term {Γ} A) → ∀ Γ⇓ → Type⇓ T ((Σ.proj₁ Γ⇓ , Term⇓ a (Σ.proj₁ Γ⇓)) , Σ.proj₂ Γ⇓) ↔ Type⇓ (subst1₁ T a) Γ⇓
Term⇓-Wk1↔ : ∀ {Γ A} (T : Type Γ) Γ⇓ → Type⇓ T (Σ.proj₁ Γ⇓) ↔ Type⇓ (Wk1 {Γ} {A} T) Γ⇓
Term⇓-Wk1₁↔ : ∀ {Γ A B} (T : Type (Γ ▻ B)) Γ⇓ → Type⇓ T (Σ.proj₁ (Σ.proj₁ Γ⇓) , Σ.proj₂ Γ⇓) ↔ Type⇓ (Wk1₁ {Γ} {A} {B} T) Γ⇓
{-
Term⇓ ⌜ x ⌝c Γ⇓ = lift x
Term⇓ ⌜ x ⌝ Γ⇓ = lift x
Term⇓ ⌜ x ⌝t Γ⇓ = lift x
Term⇓ ‘quote’ Γ⇓ t = lift ⌜ lower t ⌝t
Term⇓ ‘id’ Γ⇓ = λ x → x
Term⇓ ‘eval’ Γ⇓ ( f , x ) = f x
Term⇓ ‘curry’ Γ⇓ f a b = f (a , b)
Term⇓ ‘uncurry’ Γ⇓ f ( a , b ) = f a b
Term⇓ (x ‘,’ y) Γ⇓ = Term⇓ x Γ⇓ , Term⇓ y Γ⇓
Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
Term⇓ (f ‘’Πₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
Term⇓ ‘pairΣ’ Γ⇓ = λ a b → a , b
Term⇓ (‘const’ x) Γ⇓ = λ _ → Term⇓ x Γ⇓
Term⇓ ‘dup’ Γ⇓ = λ x → x , x
Term⇓ ‘proj₁’ Γ⇓ = Σ.proj₁
Term⇓ (wk→ x) Γ⇓ = Term⇓ x (Σ.proj₁ Γ⇓)
Term⇓ var₀ Γ⇓ = Σ.proj₂ Γ⇓
Term⇓ (wk t) Γ⇓ = Term⇓ t (Σ.proj₁ Γ⇓)
Term⇓ (f ‘∘’ g) Γ⇓ = λ x → Term⇓ f Γ⇓ (Term⇓ g Γ⇓ x)
Term⇓ ‘tt’ Γ⇓ = tt
Term⇓ ‘refl’ Γ⇓ = {!refl!}
Term⇓ (‘λ’ f) Γ⇓ = λ a → Term⇓ f (Γ⇓ , a)
Term⇓ (‘λ→’ f) Γ⇓ = λ a → Term⇓ f (Γ⇓ , a)
Term⇓ (red1→ {Γ} {A} t) Γ⇓ = Term⇓-red1↔ {Γ} A Γ⇓ ._↔_.fwdl (Term⇓ t Γ⇓)
Term⇓ (red1← {Γ} {A} t) Γ⇓ = Term⇓-red1↔ {Γ} A Γ⇓ ._↔_.bakl (Term⇓ t Γ⇓)
Term⇓ (f ‘××’ g) Γ⇓ (a , b) = (Term⇓ f Γ⇓ a , Term⇓ g Γ⇓ b)
Term⇓ (_‘××Σ’_ {Γ} {A} {B} {A′} {B′} f g) Γ⇓ = Term⇓-‘××Σ’ {Γ} {A} {B} {A′} {B′} f g Γ⇓
Term⇓ (_‘××Σ'’_ {Γ} {A} {B} {A′} {B′} f g) Γ⇓ = Term⇓-‘××Σ'’ {Γ} {A} {B} {A′} {B′} f g Γ⇓
Term⇓ ‘‘’’ₐ Γ⇓ f x = lift (lower f ‘’ₐ lower x)
Term⇓ ‘‘Eq’’ Γ⇓ x y = lift (lower x ‘≡’ lower y)
Term⇓ ‘‘,’’ Γ⇓ (a , b) = lift (lower a ‘,’ lower b)
Term⇓ ‘‘Σ’’ Γ⇓ (a , b) = lift (‘Σ’ (lower a) {!!})
Term⇓ ‘‘Exp’’ Γ⇓ (a , b) = lift (lower a ‘→’ lower b)
Term⇓ ‘Δ-fwd’ Γ⇓ f⇓ = {!f⇓!}
Term⇓ (‘Δ-bak’ f) Γ⇓ = {!Term⇓ f Γ⇓!}
Term⇓ ‘‘Δ-bak’’ Γ⇓ f = lift (‘Δ-bak’ (lower f))
Term⇓ (‘Δ’-point-surjection {T} {f}) Γ⇓ = Term⇓-‘Δ’-point-surjection {T} {f} Γ⇓

Type⇓‘Δ’ T Γ⇓ = Type⇓ T (Γ⇓ , {!lift (‘Δ’ T)!})


Term⇓-‘Δ’-point-surjection Γ⇓ = refl
Term⇓-‘××Σ’ f g Γ⇓ = λ x → Term⇓ f Γ⇓ (Σ.proj₁ x) , Term⇓ g Γ⇓ (Σ.proj₁ x) (Σ.proj₂ x)
Term⇓-‘××Σ'’ f g Γ⇓ = λ x → Term⇓ f Γ⇓ x , Term⇓ g Γ⇓ x
open _↔_
Term⇓-red1↔ (T ‘’ x) Γ⇓ = Term⇓-subst1↔ T x Γ⇓
Term⇓-red1↔ (T ‘’₁ a) Γ⇓ = Term⇓-subst1₁↔ T a Γ⇓
Term⇓-red1↔ ‘Context’ Γ⇓ = id↔
Term⇓-red1↔ ‘Type’ Γ⇓ = id↔
Term⇓-red1↔ ‘Term’ Γ⇓ = id↔
Term⇓-red1↔ (A ‘→’ B) Γ⇓ =
  iff (λ f x → Term⇓-red1↔ B Γ⇓ .fwdl (f (Term⇓-red1↔ A Γ⇓ .bakl x)))
      (λ f x → Term⇓-red1↔ B Γ⇓ .bakl (f (Term⇓-red1↔ A Γ⇓ .fwdl x)))
Term⇓-red1↔ (A ‘×’ B) Γ⇓ =
  iff (λ (a , b) → Term⇓-red1↔ A Γ⇓ .fwdl a , Term⇓-red1↔ B Γ⇓ .fwdl b)
      (λ (a , b) → Term⇓-red1↔ A Γ⇓ .bakl a , Term⇓-red1↔ B Γ⇓ .bakl b)
Term⇓-red1↔ ‘⊤’ Γ⇓ = id↔
Term⇓-red1↔ ‘⊥’ Γ⇓ = id↔
Term⇓-red1↔ (‘Σ’ A B) Γ⇓ =
  iff (λ (a , b) → a , Term⇓-red1↔ B (Γ⇓ , a) .fwdl b)
      (λ (a , b) → a , Term⇓-red1↔ B (Γ⇓ , a) .bakl b)
Term⇓-red1↔ (‘Π’ A B) Γ⇓ =
  iff (λ f x → Term⇓-red1↔ B (Γ⇓ , x) .fwdl (f x))
      (λ f x → Term⇓-red1↔ B (Γ⇓ , x) .bakl (f x))
Term⇓-red1↔ (Wk T) Γ⇓ = Term⇓-Wk1↔ T Γ⇓
Term⇓-red1↔ (Wk₁ T) Γ⇓ = Term⇓-Wk1₁↔ T Γ⇓
Term⇓-red1↔ ‘Eq’ Γ⇓ = id↔
Term⇓-red1↔ (‘Δ’ T) Γ⇓ = id↔

Term⇓-subst1↔ (T ‘’ a) b Γ⇓ = Term⇓-subst1↔ T a _
Term⇓-subst1↔ (T ‘’₁ a) b Γ⇓ = Term⇓-subst1₁↔ T a _
Term⇓-subst1↔ ‘Context’ x Γ⇓ = id↔ {_} {Lifted Context}
Term⇓-subst1↔ ‘Type’ x Γ⇓ = id↔ {_} {Lifted (Type _)}
Term⇓-subst1↔ ‘Term’ x Γ⇓ = id↔ {_} {Lifted (Term _)}
Term⇓-subst1↔ (A ‘→’ B) x Γ⇓ = id↔ {_} {Type⇓ A _ → Type⇓ B _}
Term⇓-subst1↔ (A ‘×’ B) x Γ⇓ = id↔ {_} {Type⇓ A _ × Type⇓ B _}
Term⇓-subst1↔ ‘⊤’ x Γ⇓ = id↔ {_} {⊤}
Term⇓-subst1↔ ‘⊥’ x Γ⇓ = id↔ {_} {⊥}
Term⇓-subst1↔ (‘Σ’ A B) x Γ⇓ = id↔ {_} {Σ (Type⇓ A _) (λ a → Type⇓ B _)}
Term⇓-subst1↔ (‘Π’ A B) x Γ⇓ = id↔ {_} {(a : Type⇓ A _) → Type⇓ B _}
Term⇓-subst1↔ (Wk T) x Γ⇓ = id↔ {_} {Type⇓ T Γ⇓}
Term⇓-subst1↔ (Wk₁ T) x Γ⇓ = Term⇓-Wk1₁↔ T _
Term⇓-subst1↔ ‘Eq’ x Γ⇓ = id↔ {_} {_ ≡ _}
Term⇓-subst1↔ (‘Δ’ T) x Γ⇓ = id↔ {_} {Type⇓ T _}
Term⇓-subst1₁↔ (T ‘’ a) b Γ⇓ = Term⇓-subst1↔ T a _
Term⇓-subst1₁↔ (T ‘’₁ a) b Γ⇓ = Term⇓-subst1₁↔ T a _
Term⇓-subst1₁↔ ‘Context’ x Γ⇓ = id↔ {_} {Lifted Context}
Term⇓-subst1₁↔ ‘Type’ x Γ⇓ = id↔ {_} {Lifted (Type _)}
Term⇓-subst1₁↔ ‘Term’ x Γ⇓ = id↔ {_} {Lifted (Term _)}
Term⇓-subst1₁↔ (A ‘→’ B) x Γ⇓ = id↔ {_} {Type⇓ A _ → Type⇓ B _}
Term⇓-subst1₁↔ (A ‘×’ B) x Γ⇓ = id↔ {_} {Type⇓ A _ × Type⇓ B _}
Term⇓-subst1₁↔ ‘⊤’ x Γ⇓ = id↔ {_} {⊤}
Term⇓-subst1₁↔ ‘⊥’ x Γ⇓ = id↔ {_} {⊥}
Term⇓-subst1₁↔ (‘Σ’ A B) x Γ⇓ = id↔ {_} {Σ (Type⇓ A _) (λ a → Type⇓ B _)}
Term⇓-subst1₁↔ (‘Π’ A B) x Γ⇓ = id↔ {_} {(a : Type⇓ A _) → Type⇓ B _}
Term⇓-subst1₁↔ (Wk T) x Γ⇓ = id↔ {_} {Type⇓ T _}
Term⇓-subst1₁↔ (Wk₁ T) x Γ⇓ = id↔ {_} {Type⇓ T _}
Term⇓-subst1₁↔ ‘Eq’ x Γ⇓ = id↔ {_} {_ ≡ _}
Term⇓-subst1₁↔ (‘Δ’ T) x Γ⇓ = id↔ {_} {Type⇓ T _}

Term⇓-Wk1↔ T@(_ ‘’ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1↔ T@(_ ‘’₁ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1↔ ‘Context’ Γ⇓ = id↔ {_} {Lifted Context}
Term⇓-Wk1↔ ‘Type’ Γ⇓ = id↔ {_} {Lifted (Type _)}
Term⇓-Wk1↔ ‘Term’ Γ⇓ = id↔ {_} {Lifted (Term _)}
Term⇓-Wk1↔ (A ‘→’ B) Γ⇓ = id↔ {_} {Type⇓ A _ → Type⇓ B _}
Term⇓-Wk1↔ (A ‘×’ B) Γ⇓ = id↔ {_} {Type⇓ A _ × Type⇓ B _}
Term⇓-Wk1↔ ‘⊤’ Γ⇓ = id↔ {_} {⊤}
Term⇓-Wk1↔ ‘⊥’ Γ⇓ = id↔ {_} {⊥}
Term⇓-Wk1↔ (‘Σ’ A B) Γ⇓ = id↔ {_} {Σ (Type⇓ A _) (λ a → Type⇓ B _)}
Term⇓-Wk1↔ (‘Π’ A B) Γ⇓ = id↔ {_} {(a : Type⇓ A _) → Type⇓ B _}
Term⇓-Wk1↔ (Wk T) Γ⇓ = Term⇓-Wk1↔ T _
Term⇓-Wk1↔ T@(Wk₁ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1↔ T@(‘Eq’) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1↔ T@(‘Δ’ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(_ ‘’ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(_ ‘’₁ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ ‘Context’ Γ⇓ = id↔ {_} {Lifted Context}
Term⇓-Wk1₁↔ ‘Type’ Γ⇓ = id↔ {_} {Lifted (Type _)}
Term⇓-Wk1₁↔ ‘Term’ Γ⇓ = id↔ {_} {Lifted (Term _)}
Term⇓-Wk1₁↔ (A ‘→’ B) Γ⇓ = id↔ {_} {Type⇓ A _ → Type⇓ B _}
Term⇓-Wk1₁↔ (A ‘×’ B) Γ⇓ = id↔ {_} {Type⇓ A _ × Type⇓ B _}
Term⇓-Wk1₁↔ ‘⊤’ Γ⇓ = id↔ {_} {⊤}
Term⇓-Wk1₁↔ ‘⊥’ Γ⇓ = id↔ {_} {⊥}
Term⇓-Wk1₁↔ T@(‘Σ’ A B) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(‘Π’ A B) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(Wk _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(Wk₁ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(‘Eq’) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(‘Δ’ _) Γ⇓ = Term⇓-red1↔ T _
-}

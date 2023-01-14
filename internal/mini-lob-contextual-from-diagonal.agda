{-# OPTIONS --without-K #-}
module mini-lob-contextual-from-diagonal where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixr 1 _‘→’_
infixr 2 _‘×’_
infixr 2 _‘××’_
infixr 2 _‘××Σ’_
infixr 1 _‘≡’_
infixl 3 _‘’ₐ_
infixl 3 _‘∘’_

data Context : Set
data Type : Context → Set
data Term : {Γ : Context} → Type Γ → Set

data Context where
  ε : Context
  _▻_ : (Γ : Context) → Type Γ → Context

‘□Typeε’ : Type ε

red1 : ℕ → ∀ {Γ} → Type Γ → Type Γ

data Type where
  _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
  _‘’₁_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
  ‘Typeε’ : Type ε
  ‘□’ : Type (ε ▻ ‘Typeε’)
  ‘‘□’’ : Type (ε ▻ ‘□Typeε’)
  _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  _‘×’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  ‘⊤’ : ∀ {Γ} → Type Γ
  ‘⊥’ : ∀ {Γ} → Type Γ
  ‘Σ’ : ∀ {Γ} A → Type (Γ ▻ A) → Type Γ
  ‘Π’ : ∀ {Γ} A → Type (Γ ▻ A) → Type Γ
  Wk : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
  Wk₁ : ∀ {Γ A B} → Type (Γ ▻ B) → Type (Γ ▻ A ▻ Wk B)
  _‘≡’_ : ∀ {Γ} {A : Type Γ} → Term A → Term A → Type Γ
  ‘Δ’ : Type (ε ▻ ‘Typeε’) → Type ε

subst : ℕ → ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
subst₁ : (n : ℕ) → ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
red1 zero T = T
red1 n@(suc _) ‘Typeε’ = ‘Typeε’
red1 n@(suc _) ‘□’ = ‘□’
red1 n@(suc _) ‘‘□’’ = ‘‘□’’
red1 n@(suc _) (A ‘→’ B) = (red1 n A) ‘→’ (red1 n B)
red1 n@(suc _) (A ‘×’ B) = (red1 n A) ‘×’ (red1 n B)
red1 n@(suc _) ‘⊤’ = ‘⊤’
red1 n@(suc _) ‘⊥’ = ‘⊥’
red1 n@(suc _) (‘Σ’ A B) = ‘Σ’ A (red1 n B)
red1 n@(suc _) (‘Π’ A B) = ‘Π’ A (red1 n B)
red1 n@(suc _) (Wk T) = Wk (red1 n T)
red1 n@(suc _) (Wk₁ T) = Wk₁ (red1 n T)
red1 n@(suc _) (a ‘≡’ b) = a ‘≡’ b
red1 n@(suc _) (‘Δ’ T) = ‘Δ’ T
red1 (suc n) (T ‘’ x) = subst n T x
red1 (suc n) (T ‘’₁ a) = subst₁ n T a

subst n (T ‘’ a) b = T ‘’ a ‘’ b -- red1 n ((subst n T a) ‘’ b)
subst n (T ‘’₁ a) b = T ‘’₁ a ‘’ b -- red1 n ((subst₁ n T a) ‘’ b)
subst n ‘□’ x = ‘□’ ‘’ x
subst n ‘‘□’’ x = ‘‘□’’ ‘’ x
subst n (A ‘→’ B) x = red1 n (A ‘’ x ‘→’ B ‘’ x)
subst n (A ‘×’ B) x = red1 n (A ‘’ x ‘×’ B ‘’ x)
subst n ‘⊤’ x = ‘⊤’
subst n ‘⊥’ x = ‘⊤’
subst n (‘Σ’ A B) x = red1 n (‘Σ’ (A ‘’ x) (B ‘’₁ x))
subst n (‘Π’ A B) x = red1 n (‘Π’ (A ‘’ x) (B ‘’₁ x))
subst n (Wk T) x = T
subst n (Wk₁ T) x = Wk₁ (red1 n T) ‘’ x
subst n (a ‘≡’ b) x = (a ‘≡’ b) ‘’ x
subst₁ n (T ‘’ a) b = red1 n ((subst n T a) ‘’₁ b)
subst₁ n (T ‘’₁ a) b = red1 n ((subst₁ n T a) ‘’₁ b)
subst₁ n (A ‘→’ B) x = red1 n (A ‘’₁ x ‘→’ B ‘’₁ x)
subst₁ n (A ‘×’ B) x = red1 n (A ‘’₁ x ‘×’ B ‘’₁ x)
subst₁ n ‘⊤’ x = ‘⊤’
subst₁ n ‘⊥’ x = ‘⊤’
subst₁ n (‘Σ’ A B) x = (‘Σ’ A B ‘’₁ x)
subst₁ n (‘Π’ A B) x = (‘Π’ A B ‘’₁ x)
subst₁ n (Wk T) x = (Wk T ‘’₁ x)
subst₁ n (Wk₁ T) x = (Wk₁ T ‘’₁ x)
subst₁ n (a ‘≡’ b) x = (a ‘≡’ b) ‘’₁ x


data Term where
  ⌜_⌝ : Type ε → Term {ε} ‘Typeε’
  ⌜_⌝ₜ : ∀ {T} → Term T → Term (‘□’ ‘’ ⌜ T ⌝)
  ‘quote’ : ∀ {T} → Term (‘□’ ‘’ ⌜ T ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘□’ ‘’ ⌜ T ⌝ ⌝)
  ‘id’ : ∀ {Γ A} → Term {Γ} (A ‘→’ A)
  ‘eval’ : ∀ {Γ A B} → Term {Γ} (((A ‘→’ B) ‘×’ A) ‘→’ B)
  ‘curry’ : ∀ {Γ A B C} → Term {Γ} ((A ‘×’ B ‘→’ C) ‘→’ (A ‘→’ (B ‘→’ C)))
  ‘uncurry’ : ∀ {Γ A B C} → Term {Γ} ((A ‘→’ (B ‘→’ C)) ‘→’ (A ‘×’ B ‘→’ C))
  _‘,’_ : ∀ {Γ A B} → Term {Γ} A → Term {Γ} B → Term {Γ} (A ‘×’ B)
  _‘,Σ’_ : ∀ {Γ A B} → (a : Term {Γ} A) → Term {Γ} (B ‘’ a) → Term {Γ} (‘Σ’ A B)
  _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
  ‘‘’’ₐ : ∀ {A B} → Term (‘□’ ‘’ ⌜ A ‘→’ B ⌝ ‘→’ ‘□’ ‘’ ⌜ A ⌝ ‘→’ ‘□’ ‘’ ⌜ B ⌝)
  ‘‘≡’’ : ∀ {A} → Term (‘□’ ‘’ A ‘→’ ‘□’ ‘’ A ‘→’ ‘Typeε’)
  ‘const’ : ∀ {Γ A B} → Term {Γ} B → Term {Γ} (A ‘→’ B)
  ‘dup’ : ∀ {Γ A} → Term {Γ} (A ‘→’ A ‘×’ A)
  ‘proj₁’ : ∀ {Γ A B} → Term {Γ} (‘Σ’ A B ‘→’ A)
  _‘××’_ : ∀ {Γ A B C D} → Term {Γ} (A ‘→’ C) → Term {Γ} (B ‘→’ D) → Term {Γ} (A ‘×’ B ‘→’ C ‘×’ D)
  ‘‘,’’ : ∀ {A B} → Term (‘□’ ‘’ ⌜ A ⌝ ‘×’ ‘□’ ‘’ ⌜ B ⌝ ‘→’ ‘□’ ‘’ ⌜ A ‘×’ B ⌝)
  _‘∘’_ : ∀ {Γ A B C} → Term {Γ} (B ‘→’ C) → Term {Γ} (A ‘→’ B) → Term {Γ} (A ‘→’ C)
  ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
  ‘refl’ : ∀ {Γ A} {x : Term {Γ} A} → Term (x ‘≡’ x)
  wk→ : ∀ {Γ A B C} → Term {Γ} (A ‘→’ B) → Term {Γ ▻ C} (Wk A ‘→’ Wk B)
  var₀ : ∀ {Γ A} → Term {Γ ▻ A} (Wk A)
  red1→ : ∀ {Γ A} n → Term {Γ} A → Term (red1 n A)
  red1← : ∀ {Γ A} n → Term {Γ} (red1 n A) → Term A
  _‘××Σ’_ : ∀ {Γ A B A′ B′} → (f : Term {Γ} (A ‘→’ A′)) → Term {Γ} (‘Π’ A (B ‘→’ Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → Term {Γ} (‘Σ’ A B ‘→’ ‘Σ’ A′ B′)
  _‘××Σ'’_ : ∀ {Γ A B A′ B′} → (f : Term {Γ} (‘Σ’ A B ‘→’ A′)) → Term {Γ} (‘Π’ (‘Σ’ A B) (Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → Term {Γ} (‘Σ’ A B ‘→’ ‘Σ’ A′ B′)
  ‘Δ-fwd’ : ∀ {T} → Term (‘Δ’ T ‘→’ (T ‘’ ⌜ ‘Δ’ T ⌝))
  ‘Δ-bak’ : ∀ {T} → Term (T ‘’ ⌜ ‘Δ’ T ⌝) → Term (‘Δ’ T)
  ‘‘Δ-bak’’ : ∀ {T} → Term (‘□’ ‘’ ⌜ T ‘’ ⌜ ‘Δ’ T ⌝ ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘Δ’ T ⌝)
  ‘Δ’-point-surjection : ∀ {T} {f : Term (T ‘’ ⌜ ‘Δ’ T ⌝)} → Term (‘Δ-fwd’ ‘’ₐ (‘Δ-bak’ f) ‘≡’ f)

‘□Typeε’ = ‘□’ ‘’ ⌜ ‘Typeε’ ⌝

□ : Type ε → Set _
□ = Term {ε}

‘Lӧb’-gen : ∀ {X} {T} {S : □ (‘□’ ‘’ ⌜ X ⌝ ‘→’ ‘Typeε’)}
  (‘fst-T’ : □ (T ‘→’ ‘□’ ‘’ ⌜ X ⌝))
  (‘snd-T’ : ∀ (t : □ T) → □ (‘□’ ‘’ (S ‘’ₐ (‘fst-T’ ‘’ₐ t))))
  (‘pair-T’ : ∀ (pf : □ (‘□’ ‘’ ⌜ X ⌝)) (s : □ (‘□’ ‘’ (S ‘’ₐ pf))) → □ T)
  (f : □(T ‘→’ X))
  inf
  → let □inf = ‘□’ ‘’ ⌜ inf ⌝ in ∀
  (ϕ : □((□inf ‘×’ ‘□’ ‘’ ⌜ □inf ⌝) ‘→’ T))
  → let p = f ‘∘’ ϕ ‘∘’ ((‘id’ ‘××’ ‘quote’) ‘∘’ ‘dup’) in ∀
  (ϕ⁻¹p : □ □inf)
--  (ϕ-eq : ∀ (q : □ □inf) → □ (‘□’ ‘’ (‘‘≡’’ ‘’ₐ ⌜ p ‘’ₐ q ⌝ₜ ‘’ₐ (‘fst-T’ ‘’ₐ (ϕ ‘’ₐ (ϕ⁻¹p ‘,’ ⌜ q ⌝ₜ))))))
  → let löb-f = p ‘’ₐ ϕ⁻¹p in ∀
  (s : □ (‘□’ ‘’ (S ‘’ₐ ⌜ löb-f ⌝ₜ)))
  → □ X
‘Lӧb’-gen {X} {T} {S} ‘fst-T’ ‘snd-T’ ‘pair-T’ f inf ϕ ϕ⁻¹p s = löb-f
  module ‘Lӧb’-gen where
    □inf = ‘□’ ‘’ ⌜ inf ⌝
    p = f ‘∘’ ϕ ‘∘’ ((‘id’ ‘××’ ‘quote’) ‘∘’ ‘dup’)
    löb-f = p ‘’ₐ ϕ⁻¹p

the : ∀ {ℓ} → (A : Set ℓ) → A → A
the A x = x

‘Lӧb’ : ∀ {X} {S : □ X → Set} {‘S’ : Type (ε ▻ ‘□’ ‘’ ⌜ X ⌝)} →
  let T = ‘Σ’ (‘□’ ‘’ ⌜ X ⌝) ‘S’ in
  (f : □(T ‘→’ X))
  (‘Sᵢ’ : Type (ε ▻ ‘Typeε’ ▻ ‘□’)) -- ∀ {Y} → □(□Y → Type)
  (‘quoteΣSᵢ’ : ∀ {Y} → □(‘Σ’ (‘□’ ‘’ ⌜ Y ⌝) (‘Sᵢ’ ‘’₁ _) ‘→’ ‘□’ ‘’ ⌜ ‘Σ’ (‘□’ ‘’ ⌜ Y ⌝) (‘Sᵢ’ ‘’₁ _) ⌝)) →
  let □inf = ‘Δ’ (‘Σ’ ‘□’ ‘Sᵢ’ ‘→’ Wk T) in
  let □□inf = ‘□’ ‘’ ⌜ □inf ⌝ in
  let □□infₛ = ‘Σ’ □□inf (‘Sᵢ’ ‘’₁ _) in
  let ϕ = the (□(□inf ‘×’ □□infₛ ‘→’ T)) (‘uncurry’ ‘’ₐ red1→ (suc (suc zero)) (‘Δ-fwd’ {‘Σ’ ‘□’ ‘Sᵢ’ ‘→’ Wk T})) in
  let p = the (□(□□infₛ ‘→’ ‘□’ ‘’ ⌜ X ⌝)) (‘‘’’ₐ ‘’ₐ ⌜ f ‘∘’ ϕ ⌝ₜ ‘∘’ ‘‘,’’ ‘∘’ (‘proj₁’ ‘××’ ‘quoteΣSᵢ’) ‘∘’ ‘dup’) in
  (s₁ : □(‘Π’ □□infₛ (Wk₁ ‘S’ ‘’ (wk→ p ‘’ₐ var₀)))) →
  let pt = the (□(□□infₛ ‘→’ T)) (p ‘××Σ'’ s₁) in
  let ϕ⁻¹pt = the (□ □□inf) (‘‘Δ-bak’’ ‘’ₐ ⌜ red1← (suc (suc zero)) pt ⌝ₜ) in
  (s₂ : □ (‘Sᵢ’ ‘’₁ _ ‘’ ϕ⁻¹pt)) →
  let ϕ⁻¹pts = the (□ □□infₛ) (ϕ⁻¹pt ‘,Σ’ s₂) in
  let ‘löb’ = the (□ T) (pt ‘’ₐ ϕ⁻¹pts) in
  let löb = the (□ X) (f ‘’ₐ ‘löb’) in ∀
  (s₃ : S löb)
  → □ X
‘Lӧb’ {X} {S} {‘S’} f ‘Sᵢ’ ‘quoteΣSᵢ’ s₁ s₂ s₃ = löb
  module ‘Lӧb’ where
    T = ‘Σ’ (‘□’ ‘’ ⌜ X ⌝) ‘S’
    □inf = ‘Δ’ (‘Σ’ ‘□’ ‘Sᵢ’ ‘→’ Wk T)
    □□inf = ‘□’ ‘’ ⌜ □inf ⌝
    □□infₛ = ‘Σ’ □□inf (‘Sᵢ’ ‘’₁ _)
    ϕ = the (□(□inf ‘×’ □□infₛ ‘→’ T)) (‘uncurry’ ‘’ₐ red1→ (suc (suc zero)) (‘Δ-fwd’ {‘Σ’ ‘□’ ‘Sᵢ’ ‘→’ Wk T}))
    p = the (□(□□infₛ ‘→’ ‘□’ ‘’ ⌜ X ⌝)) (‘‘’’ₐ ‘’ₐ ⌜ f ‘∘’ ϕ ⌝ₜ ‘∘’ ‘‘,’’ ‘∘’ (‘proj₁’ ‘××’ ‘quoteΣSᵢ’) ‘∘’ ‘dup’)
    pt = the (□(□□infₛ ‘→’ T)) (p ‘××Σ'’ s₁)
    ϕ⁻¹pt = the (□ □□inf) (‘‘Δ-bak’’ ‘’ₐ ⌜ red1← (suc (suc zero)) pt ⌝ₜ)
    ϕ⁻¹pts = the (□ □□infₛ) (ϕ⁻¹pt ‘,Σ’ s₂)
    ‘löb’ = the (□ T) (pt ‘’ₐ ϕ⁻¹pts)
    löb = the (□ X) (f ‘’ₐ ‘löb’)

max-level : Level
max-level = lzero

Context⇓ : (Γ : Context) → Set max-level
Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓

Context⇓ ε = ⊤
Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

Type⇓‘‘□’’ : Context⇓ (ε ▻ ‘□Typeε’) → Set max-level
Type⇓Wk₁ : ∀ {Γ A B} (T : Type (Γ ▻ B)) → Context⇓ (Γ ▻ A ▻ Wk B) → Set max-level

Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
Type⇓ (T ‘’₁ x) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓ , Term⇓ x (Σ.proj₁ Γ⇓) , Σ.proj₂ Γ⇓)
Type⇓ ‘Typeε’ Γ⇓ = Lifted (Type ε)
Type⇓ ‘□’ Γ⇓ = Lifted (Term {ε} (lower (Σ.proj₂ Γ⇓)))
Type⇓ ‘‘□’’ Γ⇓ = Type⇓‘‘□’’ Γ⇓
Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
Type⇓ ‘⊤’ Γ⇓ = ⊤
Type⇓ ‘⊥’ Γ⇓ = ⊥
Type⇓ (‘Δ’ T) Γ⇓ = Type⇓ T (Γ⇓ , lift (‘Δ’ T))
Type⇓ (x ‘≡’ y) Γ⇓ = Term⇓ x Γ⇓ ≡ Term⇓ y Γ⇓
Type⇓ (A ‘×’ B) Γ⇓ = Type⇓ A Γ⇓ × Type⇓ B Γ⇓
Type⇓ (‘Σ’ A B) Γ⇓ = Σ (Type⇓ A Γ⇓) (λ a → Type⇓ B (Γ⇓ , a))
Type⇓ (‘Π’ A B) Γ⇓ = (a : Type⇓ A Γ⇓) → Type⇓ B (Γ⇓ , a)
Type⇓ (Wk T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
Type⇓ (Wk₁ {Γ} {A} {B} T) Γ⇓ = Type⇓Wk₁ {Γ} {A} {B} T Γ⇓

Type⇓Wk₁ T Γ⇓ = Type⇓ T (Σ.proj₁ (Σ.proj₁ Γ⇓) , Σ.proj₂ Γ⇓)

Term⇓-‘Δ’-point-surjection : ∀ {T} {f : Term (T ‘’ ⌜ ‘Δ’ T ⌝)}
      → ∀ Γ⇓ → Type⇓ (‘Δ-fwd’ ‘’ₐ (‘Δ-bak’ f) ‘≡’ f) Γ⇓
Term⇓-‘××Σ’ : ∀ {Γ} {A} {B} {A′} {B′} (f : Term {Γ} (A ‘→’ A′)) → Term {Γ} (‘Π’ A (B ‘→’ Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → ∀ Γ⇓ → Type⇓ (‘Σ’ A B ‘→’ ‘Σ’ A′ B′) Γ⇓
Term⇓-‘××Σ'’ : ∀ {Γ} {A} {B} {A′} {B′} (f : Term {Γ} (‘Σ’ A B ‘→’ A′)) → Term {Γ} (‘Π’ (‘Σ’ A B) (Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → ∀ Γ⇓ → Type⇓ (‘Σ’ A B ‘→’ ‘Σ’ A′ B′) Γ⇓
Term⇓-red1↔ : ∀ (n : ℕ) {Γ} (T : Type Γ) Γ⇓ → Type⇓ T Γ⇓ ↔ Type⇓ (red1 n T) Γ⇓
Term⇓-subst↔ : ∀ (n : ℕ) {Γ A} → (T : Type (Γ ▻ A)) (a : Term {Γ} A) → ∀ Γ⇓ → Type⇓ (T ‘’ a) Γ⇓ ↔ Type⇓ (subst n T a) Γ⇓
Term⇓-subst₁↔ : ∀ (n : ℕ) {Γ A B} → (T : Type (Γ ▻ A ▻ B)) → (a : Term {Γ} A) → ∀ Γ⇓ → Type⇓ (T ‘’₁ a) Γ⇓ ↔ Type⇓ (subst₁ n T a) Γ⇓

Term⇓ ⌜ x ⌝ Γ⇓ = lift x
Term⇓ ⌜ x ⌝ₜ Γ⇓ = lift x
Term⇓ ‘quote’ Γ⇓ t = lift ⌜ lower t ⌝ₜ
Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
Term⇓ ‘‘’’ₐ Γ⇓ f x = lift (lower f ‘’ₐ lower x)
Term⇓ ‘tt’ Γ⇓ = tt
Term⇓ ‘refl’ Γ⇓ = refl
Term⇓ (wk→ x) Γ⇓ = Term⇓ x (Σ.proj₁ Γ⇓)
Term⇓ var₀ Γ⇓ = Σ.proj₂ Γ⇓
Term⇓ (_‘××Σ’_ {Γ} {A} {B} {A′} {B′} f g) Γ⇓ = Term⇓-‘××Σ’ {Γ} {A} {B} {A′} {B′} f g Γ⇓
Term⇓ (_‘××Σ'’_ {Γ} {A} {B} {A′} {B′} f g) Γ⇓ = Term⇓-‘××Σ'’ {Γ} {A} {B} {A′} {B′} f g Γ⇓
Term⇓ ‘‘≡’’ Γ⇓ x y = lift (lower x ‘≡’ lower y)
Term⇓ ‘Δ-fwd’ Γ⇓ f⇓ = f⇓
Term⇓ (‘Δ-bak’ f) Γ⇓ = Term⇓ f Γ⇓
Term⇓ ‘‘Δ-bak’’ Γ⇓ f = lift (‘Δ-bak’ (lower f))
Term⇓ ‘id’ Γ⇓ = λ x → x
Term⇓ ‘eval’ Γ⇓ ( f , x ) = f x
Term⇓ ‘curry’ Γ⇓ f a b = f (a , b)
Term⇓ ‘uncurry’ Γ⇓ f ( a , b ) = f a b
Term⇓ (x ‘,’ y) Γ⇓ = Term⇓ x Γ⇓ , Term⇓ y Γ⇓
Term⇓ (x ‘,Σ’ y) Γ⇓ = Term⇓ x Γ⇓ , Term⇓ y Γ⇓
Term⇓ ‘‘,’’ Γ⇓ (a , b) = lift (lower a ‘,’ lower b)
Term⇓ (‘const’ x) Γ⇓ = λ _ → Term⇓ x Γ⇓
Term⇓ ‘dup’ Γ⇓ = λ x → x , x
Term⇓ ‘proj₁’ Γ⇓ = Σ.proj₁
Term⇓ (f ‘××’ g) Γ⇓ (a , b) = (Term⇓ f Γ⇓ a , Term⇓ g Γ⇓ b)
Term⇓ (f ‘∘’ g) Γ⇓ = λ x → Term⇓ f Γ⇓ (Term⇓ g Γ⇓ x)
Term⇓ (‘Δ’-point-surjection {T} {f}) Γ⇓ = Term⇓-‘Δ’-point-surjection {T} {f} Γ⇓
Term⇓ (red1→ {Γ} {A} n t) Γ⇓ = Term⇓-red1↔ n {Γ} A Γ⇓ ._↔_.fwdl (Term⇓ t Γ⇓)
Term⇓ (red1← {Γ} {A} n t) Γ⇓ = Term⇓-red1↔ n {Γ} A Γ⇓ ._↔_.bakl (Term⇓ t Γ⇓)

Type⇓‘‘□’’ Γ⇓ = Lifted (Term {ε} (‘□’ ‘’ (lower (Σ.proj₂ Γ⇓))))

Term⇓-‘Δ’-point-surjection Γ⇓ = refl
Term⇓-‘××Σ’ f g Γ⇓ = λ x → Term⇓ f Γ⇓ (Σ.proj₁ x) , Term⇓ g Γ⇓ (Σ.proj₁ x) (Σ.proj₂ x)
Term⇓-‘××Σ'’ f g Γ⇓ = λ x → Term⇓ f Γ⇓ x , Term⇓ g Γ⇓ x
open _↔_
id↔ : ∀ {a} {A : Set a} → A ↔ A
id↔ = iff (λ x → x) (λ x → x)
Term⇓-red1↔ zero T Γ⇓ = id↔
Term⇓-red1↔ n@(suc _) ‘Typeε’ Γ⇓ = id↔
Term⇓-red1↔ n@(suc _) ‘□’ Γ⇓ = id↔
Term⇓-red1↔ n@(suc _) ‘‘□’’ Γ⇓ = id↔
Term⇓-red1↔ n@(suc _) (A ‘→’ B) Γ⇓ =
  iff (λ f x → Term⇓-red1↔ n B Γ⇓ .fwdl (f (Term⇓-red1↔ n A Γ⇓ .bakl x)))
      (λ f x → Term⇓-red1↔ n B Γ⇓ .bakl (f (Term⇓-red1↔ n A Γ⇓ .fwdl x)))
Term⇓-red1↔ n@(suc _) (A ‘×’ B) Γ⇓ =
  iff (λ (a , b) → Term⇓-red1↔ n A Γ⇓ .fwdl a , Term⇓-red1↔ n B Γ⇓ .fwdl b)
      (λ (a , b) → Term⇓-red1↔ n A Γ⇓ .bakl a , Term⇓-red1↔ n B Γ⇓ .bakl b)
Term⇓-red1↔ n@(suc _) ‘⊤’ Γ⇓ = id↔
Term⇓-red1↔ n@(suc _) ‘⊥’ Γ⇓ = id↔
Term⇓-red1↔ n@(suc _) (‘Σ’ A B) Γ⇓ =
  iff (λ (a , b) → a , Term⇓-red1↔ n B (Γ⇓ , a) .fwdl b)
      (λ (a , b) → a , Term⇓-red1↔ n B (Γ⇓ , a) .bakl b)
Term⇓-red1↔ n@(suc _) (‘Π’ A B) Γ⇓ =
  iff (λ f x → Term⇓-red1↔ n B (Γ⇓ , x) .fwdl (f x))
      (λ f x → Term⇓-red1↔ n B (Γ⇓ , x) .bakl (f x))
Term⇓-red1↔ n@(suc _) (Wk T) Γ⇓ = Term⇓-red1↔ n T (Σ.proj₁ Γ⇓)
Term⇓-red1↔ n@(suc _) (Wk₁ T) Γ⇓ = Term⇓-red1↔ n T (Σ.proj₁ (Σ.proj₁ Γ⇓) , Σ.proj₂ Γ⇓)
Term⇓-red1↔ n@(suc _) (a ‘≡’ b) Γ⇓ = id↔
Term⇓-red1↔ n@(suc _) (‘Δ’ T) Γ⇓ = id↔
Term⇓-red1↔ (suc n) (T ‘’ x) Γ⇓ = Term⇓-subst↔ n T x Γ⇓
Term⇓-red1↔ (suc n) (T ‘’₁ a) Γ⇓ = Term⇓-subst₁↔ n T a Γ⇓

Term⇓-subst↔ n (T ‘’ a) b Γ⇓ = id↔ {_} {Type⇓ T (Γ⇓ , Term⇓ b Γ⇓ , Term⇓ a (Γ⇓ , Term⇓ b Γ⇓))}
Term⇓-subst↔ n (T ‘’₁ a) b Γ⇓ = id↔ {_} {Type⇓ T (Γ⇓ , Term⇓ a Γ⇓ , Term⇓ b Γ⇓)}
Term⇓-subst↔ n ‘□’ x Γ⇓ = id↔ {_} {Lifted (Term (lower (Term⇓ x Γ⇓)))}
Term⇓-subst↔ n ‘‘□’’ x Γ⇓ = id↔ {_} {Lifted (Term (‘□’ ‘’ lower (Term⇓ x Γ⇓)))}
Term⇓-subst↔ n (A ‘→’ B) x Γ⇓ = {!!}
Term⇓-subst↔ n (A ‘×’ B) x Γ⇓ = {!!}
Term⇓-subst↔ n ‘⊤’ x Γ⇓ = iff (λ _ → tt) (λ _ → tt)
Term⇓-subst↔ n ‘⊥’ x Γ⇓ = {!!}
Term⇓-subst↔ n (‘Σ’ A B) x Γ⇓ = {!!}
Term⇓-subst↔ n (‘Π’ A B) x Γ⇓ = {!!}
Term⇓-subst↔ n (Wk T) x Γ⇓ = {!!}
Term⇓-subst↔ n (Wk₁ T) x Γ⇓ = {!!}
Term⇓-subst↔ n (a ‘≡’ b) x Γ⇓ = {!!}
Term⇓-subst₁↔ n (T ‘’ a) b Γ⇓ = {!!}
Term⇓-subst₁↔ n (T ‘’₁ a) b Γ⇓ = {!!}
Term⇓-subst₁↔ n (A ‘→’ B) x Γ⇓ = {!!}
Term⇓-subst₁↔ n (A ‘×’ B) x Γ⇓ = {!!}
Term⇓-subst₁↔ n ‘⊤’ x Γ⇓ = iff (λ _ → tt) (λ _ → tt)
Term⇓-subst₁↔ n ‘⊥’ x Γ⇓ = {!!}
Term⇓-subst₁↔ n (‘Σ’ A B) x Γ⇓ = {!!}
Term⇓-subst₁↔ n (‘Π’ A B) x Γ⇓ = {!!}
Term⇓-subst₁↔ n (Wk T) x Γ⇓ = {!!}
Term⇓-subst₁↔ n (Wk₁ T) x Γ⇓ = {!!}
Term⇓-subst₁↔ n (a ‘≡’ b) x Γ⇓ = {!!}
{-
subst n (T ‘’ a) b = red1 n ((subst n T a) ‘’ b)
subst n (T ‘’₁ a) b = red1 n ((subst₁ n T a) ‘’ b)
subst n ‘□’ x = ‘□’ ‘’ x
subst n ‘‘□’’ x = ‘‘□’’ ‘’ x
subst n (A ‘→’ B) x = red1 n (A ‘’ x ‘→’ B ‘’ x)
subst n (A ‘×’ B) x = red1 n (A ‘’ x ‘×’ B ‘’ x)
subst n ‘⊤’ x = ‘⊤’
subst n ‘⊥’ x = ‘⊤’
subst n (‘Σ’ A B) x = red1 n (‘Σ’ (A ‘’ x) (B ‘’₁ x))
subst n (‘Π’ A B) x = red1 n (‘Π’ (A ‘’ x) (B ‘’₁ x))
subst n (Wk T) x = T
subst n (Wk₁ T) x = Wk₁ (red1 n T) ‘’ x
subst n (a ‘≡’ b) x = (a ‘≡’ b) ‘’ x
subst₁ n (T ‘’ a) b = red1 n ((subst n T a) ‘’₁ b)
subst₁ n (T ‘’₁ a) b = red1 n ((subst₁ n T a) ‘’₁ b)
subst₁ n (A ‘→’ B) x = red1 n (A ‘’₁ x ‘→’ B ‘’₁ x)
subst₁ n (A ‘×’ B) x = red1 n (A ‘’₁ x ‘×’ B ‘’₁ x)
subst₁ n ‘⊤’ x = ‘⊤’
subst₁ n ‘⊥’ x = ‘⊤’
subst₁ n (‘Σ’ A B) x = (‘Σ’ A B ‘’₁ x)
subst₁ n (‘Π’ A B) x = (‘Π’ A B ‘’₁ x)
subst₁ n (Wk T) x = (Wk T ‘’₁ x)
subst₁ n (Wk₁ T) x = (Wk₁ T ‘’₁ x)
subst₁ n (a ‘≡’ b) x = (a ‘≡’ b) ‘’₁ x
-}

-- We want to prove this, but it's not true unless we quotient syntax by conversion
-- Lӧb⇓-≡ : ∀ {X f Γ⇓} → Term⇓ (Lӧb {X} f) Γ⇓ ≡ Term⇓ f Γ⇓ (lift (Lӧb {X} f))
-- Lӧb⇓-≡ = {!!}

Lӧb : ∀ {X} → Term {ε} (‘□’ ‘’ ⌜ X ⌝ ‘→’ X) → Term {ε} X
Löb = {!!}

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

non-emptyness : Σ (Type ε) (λ T → □ T)
non-emptyness = ‘⊤’ , ‘tt’

{-# OPTIONS --without-K #-}
module mini-lob-contextual-from-diagonal where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixr 1 _‘→’_
infixr 2 _‘×’_
infixr 2 _‘××’_
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

data Type where
  _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
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
  ‘Δ’ : Type ε → Type ε

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
  _‘××’_ : ∀ {Γ A B C D} → Term {Γ} (A ‘→’ C) → Term {Γ} (B ‘→’ D) → Term {Γ} (A ‘×’ B ‘→’ C ‘×’ D)
  ‘‘,’’ : ∀ {A B} → Term (‘□’ ‘’ ⌜ A ⌝ ‘×’ ‘□’ ‘’ ⌜ B ⌝ ‘→’ ‘□’ ‘’ ⌜ A ‘×’ B ⌝)
  _‘∘’_ : ∀ {Γ A B C} → Term {Γ} (B ‘→’ C) → Term {Γ} (A ‘→’ B) → Term {Γ} (A ‘→’ C)
  ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
  ‘refl’ : ∀ {Γ A} {x : Term {Γ} A} → Term (x ‘≡’ x)
  wk→ : ∀ {Γ A B C} → Term {Γ} (A ‘→’ B) → Term {Γ ▻ C} (Wk A ‘→’ Wk B)
  var₀ : ∀ {Γ A} → Term {Γ ▻ A} (Wk A)
  _‘××Σ’_ : ∀ {Γ A B A′ B′} → (f : Term {Γ} (A ‘→’ A′)) → Term {Γ} (‘Π’ A (B ‘→’ Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → Term {Γ} (‘Σ’ A B ‘→’ ‘Σ’ A′ B′)
  ‘Δ-fwd’ : ∀ {T} → Term (‘Δ’ T ‘→’ (‘□’ ‘’ ⌜ ‘Δ’ T ⌝ ‘→’ T))
  ‘Δ-bak’ : ∀ {T} → Term (‘□’ ‘’ ⌜ ‘Δ’ T ⌝ ‘→’ T) → Term (‘Δ’ T)
  ‘‘Δ-bak’’ : ∀ {T} → Term (‘□’ ‘’ ⌜ ‘□’ ‘’ ⌜ ‘Δ’ T ⌝ ‘→’ T ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘Δ’ T ⌝)
  ‘Δ’-point-surjection : ∀ {T} {f : Term (‘□’ ‘’ ⌜ ‘Δ’ T ⌝ ‘→’ T)} {d}
    → Term (‘Δ-fwd’ ‘’ₐ (‘Δ-bak’ f) ‘’ₐ d ‘≡’ f ‘’ₐ d)

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

{-
Assume:
- `X`
- `S : □X → Type` classifying "suggested proofs"
- `"S" : □(□X → Type)`
Define:
- `T ≔ Σ_(pf : □X) (S pf)`
Assume:
- `f : □(T → X)`
- `□inf`
- `Sᵢ : □□inf → Type` classifying "small enough" double-encodings of infinity fragments
- `"Sᵢ" : □(□□inf → Type)`
- `ϕ : □(□inf × □□inf → T)`
Define:
- `p : □(□inf → X)`
- `p ≔ "λ q. {f} ({ϕ} (q, 'q))"`
Assume that `p` gives rise to a suggested proof on small infinity fragments, i.e.,
- `s : ∀ (q : □□inf) → Sᵢ q → S "{p} {q}"`
- `‘s’ : □"∀ (q : □□inf) → Sᵢq → S ({'p} q)"`
Define the extension of `'p`:
- `"pt" : □((Σ_(q : □□inf) (Sᵢ q)) → T)`
- `"pt" ≔ "(fst; {p}) × (uncurry {‘s’})"` (where `×` is more like `Σ-map`)
Assume we have point-surjectivity of `ϕ` at `"pt"` for small infinity fragments, i.e.,
- `ϕ⁻¹(pt) : □□inf` such that
- `s₂ : Sᵢ (ϕ⁻¹(pt))` and
- `‘s₂’ : □"Sᵢ {'(ϕ⁻¹(pt))}"` and
- `ϕ-eq : □"∀ (q : Σ_(q : □□inf) (Sᵢ q)) → pt q = {'ϕ} ({'(ϕ⁻¹(pt))}, 'q.1)"`
-}
‘Lӧb’ : ∀ {X} {S : □ X → Set} {‘S’ : Type (ε ▻ ‘□’ ‘’ ⌜ X ⌝)} →
  let T = ‘Σ’ (‘□’ ‘’ ⌜ X ⌝) ‘S’ in
--  (‘fst-T’ : □ (T ‘→’ ‘□’ ‘’ ⌜ X ⌝))
--  (‘pair-T’ : ∀ (pf : □ (‘□’ ‘’ ⌜ X ⌝)) (s : □ (‘□’ ‘’ (‘S’ ‘’ₐ pf))) → □ T)
--  (‘‘pair-T’’ : ∀ (pf : □ (‘□’ ‘’ ⌜ ‘□’ ‘’ ⌜ X ⌝ ⌝)) (s : □ (‘‘□’’ ‘’ (‘‘’’ₐ ‘’ₐ ⌜ ‘S’ ⌝ₜ ‘’ₐ pf))) → □ (‘□’ ‘’ ⌜ T ⌝))
  (f : □(T ‘→’ X)) →
  let □inf = ‘Δ’ T in
  let □□inf = ‘□’ ‘’ ⌜ □inf ⌝ in
  let □□□inf = ‘□’ ‘’ ⌜ □□inf ⌝ in ∀
  (Sᵢ : □ □inf → Set)
  (‘Sᵢ’ : Type (ε ▻ □□inf)) →
  let ϕ = the (□(□inf ‘×’ □□inf ‘→’ T)) (‘uncurry’ ‘’ₐ ‘Δ-fwd’) in
  let p = the (□(□□inf ‘→’ ‘□’ ‘’ ⌜ X ⌝)) (‘‘’’ₐ ‘’ₐ ⌜ f ‘∘’ ϕ ⌝ₜ ‘∘’ ‘‘,’’ ‘∘’ (‘id’ ‘××’ ‘quote’) ‘∘’ ‘dup’) in ∀
  (s : □(‘Π’ □□inf (‘Sᵢ’ ‘→’ Wk₁ ‘S’ ‘’ (wk→ p ‘’ₐ var₀)))) →
  let pt = the (□(‘Σ’ □□inf ‘Sᵢ’ ‘→’ T)) (p ‘××Σ’ s) in
  let ϕ⁻¹pt = the (□ □□inf) (‘‘Δ-bak’’ ‘’ₐ ⌜ {!pt!} ⌝ₜ) in ∀
  (s₂ : □ (‘Sᵢ’ ‘’ ϕ⁻¹pt)) →
  let ‘löb’ = the (□ T) (pt ‘’ₐ (ϕ⁻¹pt ‘,Σ’ s₂)) in
  let löb = the (□ X) (f ‘’ₐ ‘löb’) in ∀
  (s₃ : S löb) →
  ⊤ {-
  let ϕ = the (□((□□inf ‘×’ □□□inf) ‘→’ ‘□’ ‘’ ⌜ T ⌝)) (‘uncurry’ ‘’ₐ ‘Δ-fwd’) in
  let p = the (□(□□□inf ‘→’ ‘□’ ‘’ ⌜ ‘□’ ‘’ ⌜ X ⌝ ⌝)) (‘‘’’ₐ ‘’ₐ ⌜ ‘‘’’ₐ ‘’ₐ ⌜ f ⌝ₜ ‘∘’ ϕ ⌝ₜ ‘∘’ ‘‘,’’ ‘∘’ (‘id’ ‘××’ ‘quote’) ‘∘’ ‘dup’) in

  let ϕ⁻¹p = the (□ □□□inf) ⌜ ‘Δ-bak’ {!!} ⌝ₜ in
--  (ϕ-eq : ∀ (q : □ □ □inf) → □ (‘□’ ‘’ (‘‘≡’’ ‘’ₐ ⌜ p ‘’ₐ q ⌝ₜ ‘’ₐ (‘fst-T’ ‘’ₐ (ϕ ‘’ₐ (ϕ⁻¹p ‘,’ ⌜ q ⌝ₜ))))))
  let ‘‘löb-f’’ = the (□ (‘□’ ‘’ ⌜ ‘□’ ‘’ ⌜ X ⌝ ⌝)) (p ‘’ₐ ϕ⁻¹p) in ∀
  (‘s’ : □ (‘‘□’’ ‘’ (‘‘’’ₐ ‘’ₐ ⌜ ‘S’ ⌝ₜ ‘’ₐ ‘‘löb-f’’)))
  → let ‘löb-f’ = the (□ (‘□’ ‘’ ⌜ X ⌝)) (‘‘’’ₐ ‘’ₐ ⌜ f ⌝ₜ ‘’ₐ ‘‘pair-T’’ ‘‘löb-f’’ ‘s’) in ∀
  (s : □ (‘□’ ‘’ (‘S’ ‘’ₐ ‘löb-f’)))
  → let löb-f = the (□ X) (f ‘’ₐ ‘pair-T’ ‘löb-f’ s) in ∀
  (s' : S löb-f)
  → □ X -}
‘Lӧb’ = {!!} -- {X} {T} {S} ‘fst-T’ ‘snd-T’ ‘pair-T’ f ϕ⁻¹p s = löb-f
  module ‘Lӧb’ where
    {-inf = ‘Δ’ T
    □inf = ‘□’ ‘’ ⌜ inf ⌝
    ϕ = {!!}
    p = f ‘∘’ ϕ ‘∘’ ((‘id’ ‘××’ ‘quote’) ‘∘’ ‘dup’)
    löb-f = p ‘’ₐ {!ϕ⁻¹p!}-}

{-
Define:
- `löb_f : □X`
- `löb_f ≔ "{p} {ϕ⁻¹(p)}"`
Assume:
- `S löb_f`
-}

max-level : Level
max-level = lzero

Context⇓ : (Γ : Context) → Set max-level
Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓

Context⇓ ε = ⊤
Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

Type⇓‘‘□’’ : Context⇓ (ε ▻ ‘□Typeε’) → Set max-level

Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
Type⇓ ‘Typeε’ Γ⇓ = Lifted (Type ε)
Type⇓ ‘□’ Γ⇓ = Lifted (Term {ε} (lower (Σ.proj₂ Γ⇓)))
Type⇓ ‘‘□’’ Γ⇓ = Type⇓‘‘□’’ Γ⇓
Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
Type⇓ ‘⊤’ Γ⇓ = ⊤
Type⇓ ‘⊥’ Γ⇓ = ⊥
Type⇓ (‘Δ’ T) Γ⇓ = Term (‘Δ’ T) → Type⇓ T Γ⇓
Type⇓ (x ‘≡’ y) Γ⇓ = Term⇓ x Γ⇓ ≡ Term⇓ y Γ⇓
Type⇓ (A ‘×’ B) Γ⇓ = Type⇓ A Γ⇓ × Type⇓ B Γ⇓
Type⇓ (‘Σ’ A B) Γ⇓ = Σ (Type⇓ A Γ⇓) (λ a → Type⇓ B (Γ⇓ , a))
Type⇓ (‘Π’ A B) Γ⇓ = (a : Type⇓ A Γ⇓) → Type⇓ B (Γ⇓ , a)
Type⇓ (Wk T) Γ⇓ = Type⇓ T (Σ.proj₁ Γ⇓)
Type⇓ (Wk₁ T) Γ⇓ = Type⇓ T (Σ.proj₁ (Σ.proj₁ Γ⇓) , Σ.proj₂ Γ⇓)

Term⇓-‘Δ’-point-surjection : ∀ {T} {f : Term (‘□’ ‘’ ⌜ ‘Δ’ T ⌝ ‘→’ T)} {d}
      → ∀ Γ⇓ → Type⇓ (‘Δ-fwd’ ‘’ₐ (‘Δ-bak’ f) ‘’ₐ d ‘≡’ f ‘’ₐ d) Γ⇓
Term⇓-‘××Σ’ : ∀ {Γ} {A} {B} {A′} {B′} (f : Term {Γ} (A ‘→’ A′)) → Term {Γ} (‘Π’ A (B ‘→’ Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → ∀ Γ⇓ → Type⇓ (‘Σ’ A B ‘→’ ‘Σ’ A′ B′) Γ⇓

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
Term⇓ ‘‘≡’’ Γ⇓ x y = lift (lower x ‘≡’ lower y)
Term⇓ ‘Δ-fwd’ Γ⇓ f⇓ d = f⇓ (lower d)
Term⇓ (‘Δ-bak’ f) Γ⇓ d = Term⇓ f Γ⇓ (lift d)
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
Term⇓ (f ‘××’ g) Γ⇓ (a , b) = (Term⇓ f Γ⇓ a , Term⇓ g Γ⇓ b)
Term⇓ (f ‘∘’ g) Γ⇓ = λ x → Term⇓ f Γ⇓ (Term⇓ g Γ⇓ x)
Term⇓ (‘Δ’-point-surjection {T} {f} {d}) Γ⇓ = Term⇓-‘Δ’-point-surjection {T} {f} {d} Γ⇓

Type⇓‘‘□’’ Γ⇓ = Lifted (Term {ε} (‘□’ ‘’ (lower (Σ.proj₂ Γ⇓))))

Term⇓-‘Δ’-point-surjection Γ⇓ = refl
Term⇓-‘××Σ’ f g Γ⇓ = λ x → Term⇓ f Γ⇓ (Σ.proj₁ x) , Term⇓ g Γ⇓ (Σ.proj₁ x) (Σ.proj₂ x)

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

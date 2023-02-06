{-# OPTIONS --without-K #-}
module mini-lob-contextual-from-diagonal where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixl 3 _‘’₁_
infixr 1 _‘→’_
infixr 2 _‘×’_
infixr 2 _‘××’_
infixr 2 _‘××Σ’_
infixr 1 _‘≡’_
infixl 3 _‘’ₐ_
infixl 3 _‘’Πₐ_
infixl 3 _‘∘’_

data Context : Set
data Type : Context → Set
data Term : {Γ : Context} → Type Γ → Set

data Context where
  ε : Context
  _▻_ : (Γ : Context) → Type Γ → Context

red1n : ℕ → ∀ {Γ} → Type Γ → Type Γ

data Type where
  _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
  _‘’₁_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
  ‘Typeε’ : Type ε
  ‘□’ : Type (ε ▻ ‘Typeε’)
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

red1 : ∀ {Γ} → Type Γ → Type Γ
subst1 : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
subst1₁ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term {Γ} A) → Type (Γ ▻ B ‘’ a)
Wk1 : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
Wk1₁ : ∀ {Γ A B} → Type (Γ ▻ B) → Type (Γ ▻ A ▻ Wk B)
red1 ‘Typeε’ = ‘Typeε’
red1 ‘□’ = ‘□’
red1 (A ‘→’ B) = (red1 A) ‘→’ (red1 B)
red1 (A ‘×’ B) = (red1 A) ‘×’ (red1 B)
red1 ‘⊤’ = ‘⊤’
red1 ‘⊥’ = ‘⊥’
red1 (‘Σ’ A B) = ‘Σ’ A (red1 B)
red1 (‘Π’ A B) = ‘Π’ A (red1 B)
red1 (Wk T) = Wk1 T
red1 (Wk₁ T) = Wk1₁ T
red1 (a ‘≡’ b) = a ‘≡’ b
red1 (‘Δ’ T) = ‘Δ’ T
red1 (T ‘’ x) = subst1 T x
red1 (T ‘’₁ a) = subst1₁ T a

Wk1 T@(_ ‘’ _) = Wk (red1 T)
Wk1 T@(_ ‘’₁ _) = Wk (red1 T)
Wk1 T@‘Typeε’ = Wk (red1 T)
Wk1 T@‘□’ = Wk (red1 T)
Wk1 (A ‘→’ B) = Wk A ‘→’ Wk B
Wk1 (A ‘×’ B) = Wk A ‘×’ Wk B
Wk1 ‘⊤’ = ‘⊤’
Wk1 ‘⊥’ = ‘⊥’
Wk1 (‘Σ’ A B) = ‘Σ’ (Wk A) (Wk₁ B)
Wk1 (‘Π’ A B) = ‘Π’ (Wk A) (Wk₁ B)
Wk1 (Wk T) = Wk (Wk1 T)
Wk1 T@(Wk₁ _) = Wk (red1 T)
Wk1 T@(a ‘≡’ b) = Wk (red1 T)
Wk1 T@(‘Δ’ _) = Wk (red1 T)
Wk1₁ T@(_ ‘’ _) = Wk₁ (red1 T)
Wk1₁ T@(_ ‘’₁ _) = Wk₁ (red1 T)
Wk1₁ T@‘□’ = Wk₁ (red1 T)
Wk1₁ (A ‘→’ B) = Wk₁ A ‘→’ Wk₁ B
Wk1₁ (A ‘×’ B) = Wk₁ A ‘×’ Wk₁ B
Wk1₁ ‘⊤’ = ‘⊤’
Wk1₁ ‘⊥’ = ‘⊥’
Wk1₁ T@(‘Σ’ A B) = Wk₁ (red1 T)
Wk1₁ T@(‘Π’ A B) = Wk₁ (red1 T)
Wk1₁ T@(Wk _) = Wk₁ (red1 T)
Wk1₁ T@(Wk₁ _) = Wk₁ (red1 T)
Wk1₁ T@(a ‘≡’ b) = Wk₁ (red1 T)

subst1 (T ‘’ a) b = (subst1 T a) ‘’ b
subst1 (T ‘’₁ a) b = (subst1₁ T a) ‘’ b
subst1 ‘□’ x = ‘□’ ‘’ x
subst1 (A ‘→’ B) x = A ‘’ x ‘→’ B ‘’ x
subst1 (A ‘×’ B) x = A ‘’ x ‘×’ B ‘’ x
subst1 ‘⊤’ x = ‘⊤’
subst1 ‘⊥’ x = ‘⊥’
subst1 (‘Σ’ A B) x = ‘Σ’ (A ‘’ x) (B ‘’₁ x)
subst1 (‘Π’ A B) x = ‘Π’ (A ‘’ x) (B ‘’₁ x)
subst1 (Wk T) x = T
subst1 (Wk₁ T) x = Wk1₁ T ‘’ x
subst1 (a ‘≡’ b) x = (a ‘≡’ b) ‘’ x
subst1₁ (T ‘’ a) b = ((subst1 T a) ‘’₁ b)
subst1₁ (T ‘’₁ a) b = ((subst1₁ T a) ‘’₁ b)
subst1₁ (A ‘→’ B) x = (A ‘’₁ x ‘→’ B ‘’₁ x)
subst1₁ (A ‘×’ B) x = (A ‘’₁ x ‘×’ B ‘’₁ x)
subst1₁ ‘⊤’ x = ‘⊤’
subst1₁ ‘⊥’ x = ‘⊥’
subst1₁ (‘Σ’ A B) x = (‘Σ’ A B ‘’₁ x)
subst1₁ (‘Π’ A B) x = (‘Π’ A B ‘’₁ x)
subst1₁ (Wk T) x = (Wk T ‘’₁ x)
subst1₁ (Wk₁ T) x = (Wk₁ T ‘’₁ x)
subst1₁ (a ‘≡’ b) x = (a ‘≡’ b) ‘’₁ x

red1n zero T = T
red1n (suc n) T = red1n n (red1 T)

data Term where
  ⌜_⌝ : Type ε → Term {ε} ‘Typeε’
  ⌜_⌝ₜ : ∀ {T} → Term T → Term (‘□’ ‘’ ⌜ T ⌝)
  ‘quote’ : ∀ {T} → Term (‘□’ ‘’ ⌜ T ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘□’ ‘’ ⌜ T ⌝ ⌝)
  ‘id’ : ∀ {Γ A} → Term {Γ} (A ‘→’ A)
  ‘eval’ : ∀ {Γ A B} → Term {Γ} (((A ‘→’ B) ‘×’ A) ‘→’ B)
  ‘apply’ : ∀ {Γ A B} → Term {Γ} ((A ‘×’ (A ‘→’ B)) ‘→’ B)
  ‘curry’ : ∀ {Γ A B C} → Term {Γ} ((A ‘×’ B ‘→’ C) ‘→’ (A ‘→’ (B ‘→’ C)))
  ‘uncurry’ : ∀ {Γ A B C} → Term {Γ} ((A ‘→’ (B ‘→’ C)) ‘→’ (A ‘×’ B ‘→’ C))
  _‘,’_ : ∀ {Γ A B} → Term {Γ} A → Term {Γ} B → Term {Γ} (A ‘×’ B)
  _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
  _‘’Πₐ_ : ∀ {Γ A B} → Term {Γ} (‘Π’ A B) → (a : Term {Γ} A) → Term {Γ} (B ‘’ a)
  ‘pairΣ’ : ∀ {Γ A B} → Term {Γ} (‘Π’ A (B ‘→’ Wk (‘Σ’ A B)))
  ‘‘’’ₐ : ∀ {A B} → Term (‘□’ ‘’ ⌜ A ‘→’ B ⌝ ‘→’ ‘□’ ‘’ ⌜ A ⌝ ‘→’ ‘□’ ‘’ ⌜ B ⌝)
  ‘‘≡’’ : ∀ {A} → Term (‘□’ ‘’ A ‘→’ ‘□’ ‘’ A ‘→’ ‘Typeε’)
  ‘const’ : ∀ {Γ A B} → Term {Γ} B → Term {Γ} (A ‘→’ B)
  ‘dup’ : ∀ {Γ A} → Term {Γ} (A ‘→’ A ‘×’ A)
  ‘proj₁’ : ∀ {Γ A B} → Term {Γ} (‘Σ’ A B ‘→’ A)
  _‘××’_ : ∀ {Γ A B C D} → Term {Γ} (A ‘→’ C) → Term {Γ} (B ‘→’ D) → Term {Γ} (A ‘×’ B ‘→’ C ‘×’ D)
  wk→ : ∀ {Γ A B C} → Term {Γ} (A ‘→’ B) → Term {Γ ▻ C} (Wk A ‘→’ Wk B)
  var₀ : ∀ {Γ A} → Term {Γ ▻ A} (Wk A)
  ‘‘,’’ : ∀ {A B} → Term (‘□’ ‘’ ⌜ A ⌝ ‘×’ ‘□’ ‘’ ⌜ B ⌝ ‘→’ ‘□’ ‘’ ⌜ A ‘×’ B ⌝)
  _‘∘’_ : ∀ {Γ A B C} → Term {Γ} (B ‘→’ C) → Term {Γ} (A ‘→’ B) → Term {Γ} (A ‘→’ C)
  ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
  ‘refl’ : ∀ {Γ A} {x : Term {Γ} A} → Term (x ‘≡’ x)
  ‘λ’ : ∀ {Γ A B} → Term {Γ ▻ A} B → Term {Γ} (‘Π’ A B)
  ‘λ→’ : ∀ {Γ A B} → Term {Γ ▻ A} (Wk B) → Term {Γ} (A ‘→’ B)
  red1→ : ∀ {Γ A} → Term {Γ} A → Term (red1 A)
  red1← : ∀ {Γ A} → Term {Γ} (red1 A) → Term A
  _‘××Σ’_ : ∀ {Γ A B A′ B′} → (f : Term {Γ} (A ‘→’ A′)) → Term {Γ} (‘Π’ A (B ‘→’ Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → Term {Γ} (‘Σ’ A B ‘→’ ‘Σ’ A′ B′)
  _‘××Σ'’_ : ∀ {Γ A B A′ B′} → (f : Term {Γ} (‘Σ’ A B ‘→’ A′)) → Term {Γ} (‘Π’ (‘Σ’ A B) (Wk₁ B′ ‘’ (wk→ f ‘’ₐ var₀))) → Term {Γ} (‘Σ’ A B ‘→’ ‘Σ’ A′ B′)
  _‘,Σ→’_ : ∀ {Γ X A B} → (a : Term {Γ} (X ‘→’ A)) → Term {Γ} (‘Π’ X (Wk₁ B ‘’ (wk→ a ‘’ₐ var₀))) → Term {Γ} (X ‘→’ ‘Σ’ A B)
  ‘Δ-fwd’ : ∀ {T} → Term (‘Δ’ T ‘→’ (T ‘’ ⌜ ‘Δ’ T ⌝))
  ‘Δ-bak’ : ∀ {T} → Term (T ‘’ ⌜ ‘Δ’ T ⌝) → Term (‘Δ’ T)
  ‘‘Δ-bak’’ : ∀ {T} → Term (‘□’ ‘’ ⌜ T ‘’ ⌜ ‘Δ’ T ⌝ ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘Δ’ T ⌝)
  ‘Δ’-point-surjection : ∀ {T} {f : Term (T ‘’ ⌜ ‘Δ’ T ⌝)} → Term (‘Δ-fwd’ ‘’ₐ (‘Δ-bak’ f) ‘≡’ f)

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

‘clӧb’ : ∀ {X} {P : Type (ε ▻ ‘□’ ‘’ ⌜ X ⌝)} →
  let ΣP = ‘Σ’ (‘□’ ‘’ ⌜ X ⌝) P in
  (f : □ (ΣP ‘→’ X)) →
  (R₁ : Type (ε ▻ ‘Typeε’ ▻ ‘□’)) →
  (R₂ : Type (ε ▻ ‘Typeε’ ▻ (‘Σ’ ‘□’ R₁ ‘→’ Wk ΣP))) →
  let S = ‘Δ’ (‘Σ’ (‘Σ’ ‘□’ R₁ ‘→’ Wk ΣP) R₂) in
  let ΣR₁ = ‘Σ’ (‘□’ ‘’ ⌜ S ⌝) (R₁ ‘’₁ _) in
  let ϕ₁ = the (□ (S ‘→’ (ΣR₁ ‘→’ ΣP))) (red1n→ 2 (‘proj₁’ ‘∘’ red1n→ 2 (‘Δ-fwd’ {‘Σ’ (‘Σ’ ‘□’ R₁ ‘→’ Wk ΣP) R₂}))) in
  let ψ = the (∀ (m : □ (ΣR₁ ‘→’ ΣP)) → Term (R₂ ‘’₁ _ ‘’ red1n← 2 m) → □ S)
              λ{ m r → ‘Δ-bak’ (red1n← 1 (red1n← 2 m ‘,Σ’ r)) } in
  (quote-S : □ (S ‘→’ ΣR₁)) →
  let pair-ΣRΣP = the (∀ (m : □ (S ‘→’ X)) → □ (‘Π’ (‘□’ ‘’ ⌜ S ⌝) (R₁ ‘’₁ _ ‘→’ Wk₁ P ‘’ (wk→ (‘‘’’ₐ ‘’ₐ ⌜ m ⌝ₜ) ‘’ₐ var₀))) → □ (ΣR₁ ‘→’ ΣP))
                      λ{ m p → (‘‘’’ₐ ‘’ₐ ⌜ m ⌝ₜ) ‘××Σ’ p} in
  let pre-rewrap = the (□ (S ‘→’ X)) (f ‘∘’ ‘apply’ ‘∘’ (quote-S ‘××’ ϕ₁) ‘∘’ ‘dup’) in
  (p : □ (‘Π’ (‘□’ ‘’ ⌜ S ⌝) (R₁ ‘’₁ _ ‘→’ Wk₁ P ‘’ (wk→ (‘‘’’ₐ ‘’ₐ ⌜ pre-rewrap ⌝ₜ) ‘’ₐ var₀)))) →
  let rewrap = the (□ (ΣR₁ ‘→’ ΣP)) (pair-ΣRΣP pre-rewrap p) in
  (p₂ : □ (R₂ ‘’₁ _ ‘’ red1n← 2 rewrap)) →
  let lawvere = the (□ X) (pre-rewrap ‘’ₐ (ψ rewrap p₂)) in
  □ X
‘clӧb’ {X} {P} f R₁ R₂ quote-S p p₂ = lawvere
  module ‘clӧb’ where
    ΣP = ‘Σ’ (‘□’ ‘’ ⌜ X ⌝) P
    S = ‘Δ’ (‘Σ’ (‘Σ’ ‘□’ R₁ ‘→’ Wk ΣP) R₂)
    ΣR₁ = ‘Σ’ (‘□’ ‘’ ⌜ S ⌝) (R₁ ‘’₁ _)
    ϕ₁ = the (□ (S ‘→’ (ΣR₁ ‘→’ ΣP))) (red1n→ 2 (‘proj₁’ ‘∘’ red1n→ 2 (‘Δ-fwd’ {‘Σ’ (‘Σ’ ‘□’ R₁ ‘→’ Wk ΣP) R₂})))
    ψ = the (∀ (m : □ (ΣR₁ ‘→’ ΣP)) → Term (R₂ ‘’₁ _ ‘’ red1n← 2 m) → □ S)
              λ{ m r → ‘Δ-bak’ (red1n← 1 (red1n← 2 m ‘,Σ’ r)) }
    pair-ΣRΣP = the (∀ (m : □ (S ‘→’ X)) → □ (‘Π’ (‘□’ ‘’ ⌜ S ⌝) (R₁ ‘’₁ _ ‘→’ Wk₁ P ‘’ (wk→ (‘‘’’ₐ ‘’ₐ ⌜ m ⌝ₜ) ‘’ₐ var₀))) → □ (ΣR₁ ‘→’ ΣP))
                      λ{ m p → (‘‘’’ₐ ‘’ₐ ⌜ m ⌝ₜ) ‘××Σ’ p}
    pre-rewrap = the (□ (S ‘→’ X)) (f ‘∘’ ‘apply’ ‘∘’ (quote-S ‘××’ ϕ₁) ‘∘’ ‘dup’)
    rewrap = the (□ (ΣR₁ ‘→’ ΣP)) (pair-ΣRΣP pre-rewrap p)
    lawvere = the (□ X) (pre-rewrap ‘’ₐ (ψ rewrap p₂))

‘Lӧb’ : ∀ {X} {S : □ X → Set} {‘S’ : Type (ε ▻ ‘□’ ‘’ ⌜ X ⌝)} →
  let T = ‘Σ’ (‘□’ ‘’ ⌜ X ⌝) ‘S’ in
  (f : □(T ‘→’ X))
  (‘Sᵢ’ : Type (ε ▻ ‘Typeε’ ▻ ‘□’)) -- ∀ {Y} → □(□Y → Type)
  (‘quoteΣSᵢ’ : ∀ {Y} → □(‘Σ’ (‘□’ ‘’ ⌜ Y ⌝) (‘Sᵢ’ ‘’₁ _) ‘→’ ‘□’ ‘’ ⌜ ‘Σ’ (‘□’ ‘’ ⌜ Y ⌝) (‘Sᵢ’ ‘’₁ _) ⌝)) →
  let □inf = ‘Δ’ (‘Σ’ ‘□’ ‘Sᵢ’ ‘→’ Wk T) in
  let □□inf = ‘□’ ‘’ ⌜ □inf ⌝ in
  let □□infₛ = ‘Σ’ □□inf (‘Sᵢ’ ‘’₁ _) in
  let ϕ = the (□(□inf ‘×’ □□infₛ ‘→’ T)) (‘uncurry’ ‘’ₐ red1n→ (suc (suc zero)) (‘Δ-fwd’ {‘Σ’ ‘□’ ‘Sᵢ’ ‘→’ Wk T})) in
  let p = the (□(□□infₛ ‘→’ ‘□’ ‘’ ⌜ X ⌝)) (‘‘’’ₐ ‘’ₐ ⌜ f ‘∘’ ϕ ⌝ₜ ‘∘’ ‘‘,’’ ‘∘’ (‘proj₁’ ‘××’ ‘quoteΣSᵢ’) ‘∘’ ‘dup’) in
  (s₁ : □(‘Π’ □□infₛ (Wk₁ ‘S’ ‘’ (wk→ p ‘’ₐ var₀)))) →
  let pt = the (□(□□infₛ ‘→’ T)) (p ‘××Σ'’ s₁) in
  let ϕ⁻¹pt = the (□ □□inf) (‘‘Δ-bak’’ ‘’ₐ ⌜ red1n← (suc (suc zero)) pt ⌝ₜ) in
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
    ϕ = the (□(□inf ‘×’ □□infₛ ‘→’ T)) (‘uncurry’ ‘’ₐ red1n→ (suc (suc zero)) (‘Δ-fwd’ {‘Σ’ ‘□’ ‘Sᵢ’ ‘→’ Wk T}))
    p = the (□(□□infₛ ‘→’ ‘□’ ‘’ ⌜ X ⌝)) (‘‘’’ₐ ‘’ₐ ⌜ f ‘∘’ ϕ ⌝ₜ ‘∘’ ‘‘,’’ ‘∘’ (‘proj₁’ ‘××’ ‘quoteΣSᵢ’) ‘∘’ ‘dup’)
    pt = the (□(□□infₛ ‘→’ T)) (p ‘××Σ'’ s₁)
    ϕ⁻¹pt = the (□ □□inf) (‘‘Δ-bak’’ ‘’ₐ ⌜ red1n← (suc (suc zero)) pt ⌝ₜ)
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

Type⇓Wk₁ : ∀ {Γ A B} (T : Type (Γ ▻ B)) → Context⇓ (Γ ▻ A ▻ Wk B) → Set max-level

Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
Type⇓ (T ‘’₁ x) Γ⇓ = Type⇓ T ((Σ.proj₁ Γ⇓ , Term⇓ x (Σ.proj₁ Γ⇓)) , Σ.proj₂ Γ⇓)
Type⇓ ‘Typeε’ Γ⇓ = Lifted (Type ε)
Type⇓ ‘□’ Γ⇓ = Lifted (Term {ε} (lower (Σ.proj₂ Γ⇓)))
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
Term⇓-‘,Σ→’ : ∀ {Γ X A B} → (a : Term {Γ} (X ‘→’ A)) → (b : Term {Γ} (‘Π’ X (Wk₁ B ‘’ (wk→ a ‘’ₐ var₀)))) → ∀ Γ⇓ → Type⇓ (X ‘→’ ‘Σ’ A B) Γ⇓

Term⇓-red1↔ : ∀ {Γ} (T : Type Γ) Γ⇓ → Type⇓ T Γ⇓ ↔ Type⇓ (red1 T) Γ⇓
Term⇓-subst1↔ : ∀ {Γ A} → (T : Type (Γ ▻ A)) (a : Term {Γ} A) → ∀ Γ⇓ → Type⇓ T (Γ⇓ , Term⇓ a Γ⇓) ↔ Type⇓ (subst1 T a) Γ⇓
Term⇓-subst1₁↔ : ∀ {Γ A B} → (T : Type (Γ ▻ A ▻ B)) → (a : Term {Γ} A) → ∀ Γ⇓ → Type⇓ T ((Σ.proj₁ Γ⇓ , Term⇓ a (Σ.proj₁ Γ⇓)) , Σ.proj₂ Γ⇓) ↔ Type⇓ (subst1₁ T a) Γ⇓
Term⇓-Wk1↔ : ∀ {Γ A} (T : Type Γ) Γ⇓ → Type⇓ T (Σ.proj₁ Γ⇓) ↔ Type⇓ (Wk1 {Γ} {A} T) Γ⇓
Term⇓-Wk1₁↔ : ∀ {Γ A B} (T : Type (Γ ▻ B)) Γ⇓ → Type⇓ T (Σ.proj₁ (Σ.proj₁ Γ⇓) , Σ.proj₂ Γ⇓) ↔ Type⇓ (Wk1₁ {Γ} {A} {B} T) Γ⇓

Term⇓ ⌜ x ⌝ Γ⇓ = lift x
Term⇓ ⌜ x ⌝ₜ Γ⇓ = lift x
Term⇓ ‘quote’ Γ⇓ t = lift ⌜ lower t ⌝ₜ
Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
Term⇓ ‘‘’’ₐ Γ⇓ f x = lift (lower f ‘’ₐ lower x)
Term⇓ ‘tt’ Γ⇓ = tt
Term⇓ ‘refl’ Γ⇓ = refl
Term⇓ (‘λ’ f) Γ⇓ = λ a → Term⇓ f (Γ⇓ , a)
Term⇓ (‘λ→’ f) Γ⇓ = λ a → Term⇓ f (Γ⇓ , a)
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
Term⇓ ‘apply’ Γ⇓ ( x , f ) = f x
Term⇓ ‘curry’ Γ⇓ f a b = f (a , b)
Term⇓ ‘uncurry’ Γ⇓ f ( a , b ) = f a b
Term⇓ (x ‘,’ y) Γ⇓ = Term⇓ x Γ⇓ , Term⇓ y Γ⇓
Term⇓ (f ‘’Πₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
Term⇓ ‘pairΣ’ Γ⇓ = λ a b → a , b
Term⇓ ‘‘,’’ Γ⇓ (a , b) = lift (lower a ‘,’ lower b)
Term⇓ (‘const’ x) Γ⇓ = λ _ → Term⇓ x Γ⇓
Term⇓ ‘dup’ Γ⇓ = λ x → x , x
Term⇓ ‘proj₁’ Γ⇓ = Σ.proj₁
Term⇓ (_‘,Σ→’_ {Γ} {X} {A} {B} a b) Γ⇓ = Term⇓-‘,Σ→’ {Γ} {X} {A} {B} a b Γ⇓
Term⇓ (f ‘××’ g) Γ⇓ (a , b) = (Term⇓ f Γ⇓ a , Term⇓ g Γ⇓ b)
Term⇓ (f ‘∘’ g) Γ⇓ = λ x → Term⇓ f Γ⇓ (Term⇓ g Γ⇓ x)
Term⇓ (‘Δ’-point-surjection {T} {f}) Γ⇓ = Term⇓-‘Δ’-point-surjection {T} {f} Γ⇓
Term⇓ (red1→ {Γ} {A} t) Γ⇓ = Term⇓-red1↔ {Γ} A Γ⇓ ._↔_.fwdl (Term⇓ t Γ⇓)
Term⇓ (red1← {Γ} {A} t) Γ⇓ = Term⇓-red1↔ {Γ} A Γ⇓ ._↔_.bakl (Term⇓ t Γ⇓)

Term⇓-‘Δ’-point-surjection Γ⇓ = refl
Term⇓-‘××Σ’ f g Γ⇓ = λ x → Term⇓ f Γ⇓ (Σ.proj₁ x) , Term⇓ g Γ⇓ (Σ.proj₁ x) (Σ.proj₂ x)
Term⇓-‘××Σ'’ f g Γ⇓ = λ x → Term⇓ f Γ⇓ x , Term⇓ g Γ⇓ x
Term⇓-‘,Σ→’ a b Γ⇓ = λ x → Term⇓ a Γ⇓ _ , Term⇓ b Γ⇓ x

open _↔_
Term⇓-red1↔ ‘Typeε’ Γ⇓ = id↔
Term⇓-red1↔ ‘□’ Γ⇓ = id↔
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
Term⇓-red1↔ (a ‘≡’ b) Γ⇓ = id↔
Term⇓-red1↔ (‘Δ’ T) Γ⇓ = id↔
Term⇓-red1↔ (T ‘’ x) Γ⇓ = Term⇓-subst1↔ T x Γ⇓
Term⇓-red1↔ (T ‘’₁ a) Γ⇓ = Term⇓-subst1₁↔ T a Γ⇓

Term⇓-subst1↔ (T ‘’ a) b Γ⇓ = Term⇓-subst1↔ T a _
Term⇓-subst1↔ (T ‘’₁ a) b Γ⇓ = Term⇓-subst1₁↔ T a _
Term⇓-subst1↔ ‘□’ x Γ⇓ = id↔ {_} {Lifted (Term (lower (Term⇓ x Γ⇓)))}
Term⇓-subst1↔ (A ‘→’ B) x Γ⇓ = id↔ {_} {Type⇓ A _ → Type⇓ B _}
Term⇓-subst1↔ (A ‘×’ B) x Γ⇓ = id↔ {_} {Type⇓ A _ × Type⇓ B _}
Term⇓-subst1↔ ‘⊤’ x Γ⇓ = id↔ {_} {⊤}
Term⇓-subst1↔ ‘⊥’ x Γ⇓ = id↔ {_} {⊥}
Term⇓-subst1↔ (‘Σ’ A B) x Γ⇓ = id↔ {_} {Σ (Type⇓ A _) (λ a → Type⇓ B _)}
Term⇓-subst1↔ (‘Π’ A B) x Γ⇓ = id↔ {_} {(a : Type⇓ A _) → Type⇓ B _}
Term⇓-subst1↔ (Wk T) x Γ⇓ = id↔ {_} {Type⇓ T Γ⇓}
Term⇓-subst1↔ (Wk₁ T) x Γ⇓ = Term⇓-Wk1₁↔ T _
Term⇓-subst1↔ (a ‘≡’ b) x Γ⇓ = id↔ {_} {Term⇓ a _ ≡ Term⇓ b _}
Term⇓-subst1₁↔ (T ‘’ a) b Γ⇓ = Term⇓-subst1↔ T a _
Term⇓-subst1₁↔ (T ‘’₁ a) b Γ⇓ = Term⇓-subst1₁↔ T a _
Term⇓-subst1₁↔ (A ‘→’ B) x Γ⇓ = id↔ {_} {Type⇓ A _ → Type⇓ B _}
Term⇓-subst1₁↔ (A ‘×’ B) x Γ⇓ = id↔ {_} {Type⇓ A _ × Type⇓ B _}
Term⇓-subst1₁↔ ‘⊤’ x Γ⇓ = id↔ {_} {⊤}
Term⇓-subst1₁↔ ‘⊥’ x Γ⇓ = id↔ {_} {⊥}
Term⇓-subst1₁↔ (‘Σ’ A B) x Γ⇓ = id↔ {_} {Σ (Type⇓ A _) (λ a → Type⇓ B _)}
Term⇓-subst1₁↔ (‘Π’ A B) x Γ⇓ = id↔ {_} {(a : Type⇓ A _) → Type⇓ B _}
Term⇓-subst1₁↔ (Wk T) x Γ⇓ = id↔ {_} {Type⇓ T _}
Term⇓-subst1₁↔ (Wk₁ T) x Γ⇓ = id↔ {_} {Type⇓ T _}
Term⇓-subst1₁↔ (a ‘≡’ b) x Γ⇓ = id↔ {_} {Term⇓ a _ ≡ Term⇓ b _}

Term⇓-Wk1↔ T@(_ ‘’ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1↔ T@(_ ‘’₁ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1↔ T@‘Typeε’ Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1↔ T@‘□’ Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1↔ (A ‘→’ B) Γ⇓ = id↔ {_} {Type⇓ A _ → Type⇓ B _}
Term⇓-Wk1↔ (A ‘×’ B) Γ⇓ = id↔ {_} {Type⇓ A _ × Type⇓ B _}
Term⇓-Wk1↔ ‘⊤’ Γ⇓ = id↔ {_} {⊤}
Term⇓-Wk1↔ ‘⊥’ Γ⇓ = id↔ {_} {⊥}
Term⇓-Wk1↔ (‘Σ’ A B) Γ⇓ = id↔ {_} {Σ (Type⇓ A _) (λ a → Type⇓ B _)}
Term⇓-Wk1↔ (‘Π’ A B) Γ⇓ = id↔ {_} {(a : Type⇓ A _) → Type⇓ B _}
Term⇓-Wk1↔ (Wk T) Γ⇓ = Term⇓-Wk1↔ T _
Term⇓-Wk1↔ T@(Wk₁ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1↔ T@(a ‘≡’ b) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1↔ T@(‘Δ’ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(_ ‘’ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(_ ‘’₁ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@‘□’ Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ (A ‘→’ B) Γ⇓ = id↔ {_} {Type⇓ A _ → Type⇓ B _}
Term⇓-Wk1₁↔ (A ‘×’ B) Γ⇓ = id↔ {_} {Type⇓ A _ × Type⇓ B _}
Term⇓-Wk1₁↔ ‘⊤’ Γ⇓ = id↔ {_} {⊤}
Term⇓-Wk1₁↔ ‘⊥’ Γ⇓ = id↔ {_} {⊥}
Term⇓-Wk1₁↔ T@(‘Σ’ A B) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(‘Π’ A B) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(Wk _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(Wk₁ _) Γ⇓ = Term⇓-red1↔ T _
Term⇓-Wk1₁↔ T@(a ‘≡’ b) Γ⇓ = Term⇓-red1↔ T _

-- We want to prove this, but it's not true unless we quotient syntax by conversion
-- Lӧb⇓-≡ : ∀ {X f Γ⇓} → Term⇓ (Lӧb {X} f) Γ⇓ ≡ Term⇓ f Γ⇓ (lift (Lӧb {X} f))
-- Lӧb⇓-≡ = {!!}

Lӧb : ∀ {X} → Term {ε} (‘□’ ‘’ ⌜ X ⌝ ‘→’ X) → Term {ε} X
Lӧb {X} f = ‘Lӧb’ {X} {λ _ → ⊤} {‘⊤’} (f ‘∘’ ‘proj₁’) ‘⊤’ ((‘‘’’ₐ ‘’ₐ ⌜ ‘λ→’ (red1n← (suc (suc (suc zero))) (var₀ ‘,Σ’ red1← ‘tt’) ) ⌝ₜ) ‘∘’ ‘quote’ ‘∘’ ‘proj₁’) (‘λ’ (red1n← (suc (suc zero)) ‘tt’)) (red1n← (suc (suc zero)) ‘tt’) tt
-- ‘clӧb’ {X} {‘⊤’} (f ‘∘’ ‘proj₁’) ‘⊤’ ‘⊤’ ({!!} ‘,Σ→’ ‘λ’ (red1n← 3 ‘tt’)) (‘λ’ (red1n← 3 (‘const’ ‘tt’))) (red1n← 2 ‘tt’)
-- (‘‘’’ₐ ‘’ₐ ⌜ {!? ‘,Σ’ ?!} ⌝ₜ) ‘∘’ ‘quote’ ‘∘’ ‘proj₁’
-- (‘‘’’ₐ ‘’ₐ ⌜ ‘id’ ‘××Σ’ ‘λ’ (red1n← (suc (suc (suc zero))) (‘const’ ‘tt’)) ⌝ₜ) ‘∘’ {!!} ‘∘’ (‘quote’ ‘××Σ’ {!!})

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

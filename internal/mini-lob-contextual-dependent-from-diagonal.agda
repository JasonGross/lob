{-# OPTIONS --without-K #-}
module mini-lob-contextual-dependent-from-diagonal where
open import common
open import mini-lob-contextual-dependent-from-diagonal-language public

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

clӧb : ∀ {X} {‘S’ : Type (ε ▻ ‘□’ ‘’ ⌜ X ⌝)} →
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
  let löb = the (□ X) (f ‘’ₐ ‘löb’) in
  □ X
clӧb {X} {‘S’} f ‘Sᵢ’ ‘quoteΣSᵢ’ s₁ s₂ = löb
  module clӧb where
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
‘Lӧb’ {X} {S} {‘S’} f ‘Sᵢ’ ‘quoteΣSᵢ’ s₁ s₂ s₃ = clӧb {X} {‘S’} f ‘Sᵢ’ ‘quoteΣSᵢ’ s₁ s₂

‘dLӧb’ : ∀ {X} {T′ : Type ε}
  (f : □(‘□’ ‘’ ⌜ X ⌝ ‘×’ T′ ‘→’ X))
  → □ X
‘dLӧb’ {X} {T′} f = clӧb {X}
  {‘Σ’ {!!}
  (‘Σ’ {!!}
  (‘Σ’ {!!}
  (‘Σ’ {!!}
  (‘Σ’ {!!}
  (‘Σ’ {!!}
  (wk (wk (wk (wk (wk (wk var₀))))) ‘≡’ {!!}))))))}
  {!!} {!!} {!!} {!!} {!!}
{-
∀ {X} {S : □ X → Set} {‘S’ : Type (ε ▻ ‘□’ ‘’ ⌜ X ⌝)} →
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

S : □X → Type
S pf ≔
  ∃ (S : □X → Type)
    (qS : □"□‶{'X}″ → Type")
    (f₀ : □"{T} → □‶{{'t2}}″").
  let f : □"{T} → {X}"
        ≔ "λ (qs, pr). let qAU = {'AU}[qs] in (5, 0, (t1, p1), (t2, {f₀} qs pr))"
  in
  ∃ (Sᵢ : ∀ {Y} → □"□‶{{Y}}″ → Type")
    (quote-Sᵢ : ∀ {Y} → □"∀ (y : □‶{{Y}}″) → {Sᵢ} y → □‶{{qapp}} {{'Sᵢ}} {'y}″")
    (s₁ : □"∀ (q : {ssinfₛ}) → {qS} ({p} {q})")
    (s₂ : □"{Sᵢ} {invpt}")
    (s₃ : S löb_f).
  ∧ pf = clöb X S qS f Sᵢ quote-Sᵢ s₁ s₂ s₃


-}

-- We want to prove this, but it's not true unless we quotient syntax by conversion
-- Lӧb⇓-≡ : ∀ {X f Γ⇓} → Term⇓ (Lӧb {X} f) Γ⇓ ≡ Term⇓ f Γ⇓ (lift (Lӧb {X} f))
-- Lӧb⇓-≡ = {!!}

Lӧb : ∀ {X} → Term {ε} (‘□’ ‘’ ⌜ X ⌝ ‘→’ X) → Term {ε} X
Lӧb {X} f = ‘Lӧb’ {X} {λ _ → ⊤} {‘⊤’} (f ‘∘’ ‘proj₁’) ‘⊤’ ((‘‘’’ₐ ‘’ₐ ⌜ ‘λ→’ (red1n← (suc (suc (suc zero))) (var₀ ‘,Σ’ red1← ‘tt’) ) ⌝ₜ) ‘∘’ ‘quote’ ‘∘’ ‘proj₁’) (‘λ’ (red1n← (suc (suc zero)) ‘tt’)) (red1n← (suc (suc zero)) ‘tt’) tt
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

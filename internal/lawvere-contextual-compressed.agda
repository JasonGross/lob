{-# OPTIONS --without-K #-}
module lawvere-contextual-compressed
  {o a} {p r r₂}
  (𝒞 : Set o)
  (_~>_ : 𝒞 → 𝒞 → Set a)
  (id : ∀ {a} → a ~> a)
  (_⨾_ : ∀ {a b c} → a ~> b → b ~> c → a ~> c)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (dup : ∀ {a} → (a ~> (a × a)))
  (_××_ : ∀ {a b c d} → (a ~> b) → (c ~> d) → ((a × c) ~> (b × d)))
  (𝟙 : 𝒞)
--  (□ : 𝒞 → 𝒞)
  (B : 𝒞)
  (inf : 𝒞) -- inf := Δ (Σ (□inf) R → ΣP)
  (P : (𝟙 ~> B) → Set p)
  (ΣP : 𝒞) -- Σ (□ B) P
  (f : ΣP ~> B)
  (R : (𝟙 ~> inf) → Set r)
  (ΣR : 𝒞) -- Σ (□ inf) R
  (R₂ : (𝟙 ~> ΣR) → Set r₂)
  (ΣR₂ : 𝒞) -- Σ (□ ΣR) R₂
  (××ΣR₂P-but-this-needs-a-better-name : (l : ΣR ~> B) → (r : ∀ i → R₂ i → P (i ⨾ l)) → ΣR₂ ~> ΣP)
  (pair-ΣR₂ : (l : 𝟙 ~> ΣR) → R₂ l → (𝟙 ~> ΣR₂))
  (quot : ΣR ~> ΣR₂)
  (ϕ : (ΣR × ΣR₂) ~> ΣP) -- □ (inf × □ inf) ~> □ B)
  (ϕ⁻¹ : (ΣR₂ ~> ΣP) → (𝟙 ~> ΣR))
  (f : ΣP ~> B)
  where

k : ΣR ~> B
k = ((dup ⨾ (id ×× quot)) ⨾ ϕ) ⨾ f

module _ (s₁ : ∀ (i : 𝟙 ~> ΣR) → R₂ i → P (i ⨾ k)) where
  pt : ΣR₂ ~> ΣP -- this needs a better name too
  pt = ××ΣR₂P-but-this-needs-a-better-name k s₁

  lawvere : 𝟙 ~> B
  lawvere = ϕ⁻¹ pt ⨾ k


{-
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

-}
{-
lawvere : (𝟙 ~> B)
lawvere = p ∘ ϕ⁻¹ p
  module lawvere where
    p : □ inf ~> B
    p = f ∘ (ϕ ∘ id×quot∘dup)

lawvere-fix : ∀
  (□-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b))
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (□tt : 𝟙 ~> □ 𝟙)
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((f ∘ g) ∘ h) ≈ (f ∘ (g ∘ h)))
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (_∘-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → g ≈ g‵ → f ≈ f‵ → (g ∘ f) ≈ (g‵ ∘ f‵))
  (ϕ-eq : ∀ {f} → ((ϕ ∘ id×quot∘dup) ∘ ϕ⁻¹ f) ≈ (□-map (f ∘ ϕ⁻¹ f) ∘ □tt))
  → lawvere ≈ (f ∘ (□-map lawvere ∘ □tt))
lawvere-fix □-map _≈_ □tt _■_ assoc 2id _∘-map_ ϕ-eq =
  assoc ■ (2id ∘-map ϕ-eq)
-}

{-# OPTIONS --without-K #-}
module lawvere-semicomonad-exp-alt-razored-presheaf
  {o a}
  (𝒞 : Set o)
  (_~>_ : 𝒞 → 𝒞 → Set a)
  {u} (_~>𝒳 : 𝒞 → Set u)
  (_⨾_ : ∀ {a b c} → a ~> b → b ~> c → a ~> c)
  (_⨾𝒳_ : ∀ {a b} → a ~> b → b ~>𝒳 → a ~>𝒳)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (dup : ∀ {a} → (a ~> (a × a)))
  (_××_ : ∀ {a b c d} → (a ~> b) → (c ~> d) → ((a × c) ~> (b × d)))
  (𝟙 : 𝒞)
  (□ : 𝒞 → 𝒞)
  (□𝒳 : 𝒞)
  (□-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b))
  (□-map𝒳 : ∀ {a} → (a ~>𝒳) → (□ a ~> □𝒳))
  (□-×-codistr : ∀ {a b} → (□ a × □ b) ~> □ (a × b))
  (□-𝟙-codistr : 𝟙 ~> □ 𝟙)
  (quot : ∀ {a} → □ a ~> □ (□ a))
  {pu} (P𝒳 : (𝟙 ~>𝒳) → Set pu)
  {p} (P : (𝟙 ~> □𝒳) → Set p)
  (ΣP : 𝒞) -- Σ_(□𝒳) P
  (ΣP^_ : 𝒞 → 𝒞)
  (apply : ∀ {a} → (a × (ΣP^ a)) ~> ΣP)
  (S : 𝒞) -- Δ Σ_(Σ_□S R → Σ_□X P) Q
  {r} (R : (𝟙 ~> S) → Set r)
  (ΣR : 𝒞)
  (quote-pair-ΣR : (s : 𝟙 ~> S) → R s → (𝟙 ~> ΣR))
  (proj₁-S : ΣR ~> □ S)
  (quote-R : ΣR ~> □ ΣR)
  {pi} (□Π : ∀ a → (P : (𝟙 ~> a) → Set _) → Set pi) -- represents □(Π_a P)
  (pair-ΣP : ∀ {a} (f : a ~> □𝒳) → (□Π a (λ{ s → P (s ⨾ f) })) → (a ~> ΣP))
  (ϕ : S ~> (ΣP^ ΣR))
  (ψ : (ΣR ~> ΣP) → (𝟙 ~> S))
  (f : ΣP ~>𝒳)
  where

rewrap : (s : (𝟙 ~> S)) → R s → (𝟙 ~>𝒳)
rewrap = λ s rs → (dup ⨾ ((quote-pair-ΣR s rs ×× (s ⨾ ϕ)) ⨾ apply)) ⨾𝒳 f

rewrap2 : ΣR ~> □𝒳
rewrap2 = ((dup ⨾ (quote-R ×× (proj₁-S ⨾ □-map ϕ))) ⨾ (□-×-codistr ⨾ □-map apply)) ⨾ □-map𝒳 f

module _
  (Hp : □Π ΣR (λ{ s → P (s ⨾ rewrap2) }))
  (Hq : R (ψ (pair-ΣP rewrap2 Hp)))
  where
  lawvere : (𝟙 ~>𝒳)
  lawvere = rewrap (ψ (pair-ΣP rewrap2 Hp)) Hq

  module _
    (Hp𝒳 : P𝒳 lawvere)
    where

{-
module _
  (□-𝟙-codistr : 𝟙 ~> □ 𝟙)
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (𝒞λ : ∀ {a b} (f : a ~> b) → (𝟙 ~> (b ^ a)))
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → (h ⨾ (g ⨾ f)) ≈ ((h ⨾ g) ⨾ f))
  (assoc⁻¹ : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((h ⨾ g) ⨾ f) ≈ (h ⨾ (g ⨾ f)))
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (××-map : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ×× f′) ⨾ (g ×× g′)) ≈ ((f ⨾ g) ×× (f′ ⨾ g′)))
  (_××-2map_ : ∀ {a b c d} {f f′ : a ~> b} {g g′ : c ~> d} → (f ≈ f′) → (g ≈ g′) → ((f ×× g) ≈ (f′ ×× g′)))
  (dup-×× : ∀ {a b} {f : a ~> b} → (f ⨾ dup) ≈ (dup ⨾ (f ×× f)))
  (apply-λ : ∀ {a b} {f : a ~> b} {g : 𝟙 ~> a} → (dup {𝟙} ⨾ ((g ×× 𝒞λ f) ⨾ apply)) ≈ (g ⨾ f))
  (□-map-⨾ : ∀ {a b c} {f : a ~> b} {g : b ~> c} → (□-map f ⨾ □-map g) ≈ □-map (f ⨾ g))
  (□-map-quote-S : ∀ {f : 𝟙 ~> S} → (f ⨾ quote-S) ≈ (□-𝟙-codistr ⨾ □-map f))
  (ϕ-eq : ∀ {f} → (ϕ⁻¹ f ⨾ ϕ) ≈ (𝒞λ f))
  where
  lawvere-fix : lawvere ≈ ((□-𝟙-codistr ⨾ □-map lawvere) ⨾ f)
  lawvere-fix =
    let eq4 = ××-map ■ (□-map-quote-S ××-2map ϕ-eq) in
    let eq3 = assoc⁻¹ ■ (apply-λ ■ (assoc⁻¹ ■ (2id ⨾-map □-map-⨾))) in
    let eq2 = assoc ■ ((dup-×× ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map eq4))) in
    let eq1 = assoc ■ ((eq2 ⨾-map 2id) ■ eq3) in
    assoc ■ (eq1 ⨾-map 2id)
-}

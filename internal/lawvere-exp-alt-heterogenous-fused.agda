{-# OPTIONS --without-K #-}
module lawvere-exp-alt-heterogenous-fused
  {o a}
  (𝒞 : Set o)
  (_~>_ : 𝒞 → 𝒞 → Set a)
  {u} (_~>𝒰 : 𝒞 → Set u)
  (_⨾_ : ∀ {a b c} → a ~> b → b ~> c → a ~> c)
  (_⨾𝒰_ : ∀ {a b} → a ~> b → b ~>𝒰 → a ~>𝒰)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (_^_ : 𝒞 → 𝒞 → 𝒞)
  (apply : ∀ {a b} → (a × (b ^ a)) ~> b)
  (dup : ∀ {a} → (a ~> (a × a)))
  (_××_ : ∀ {a b c d} → (a ~> b) → (c ~> d) → ((a × c) ~> (b × d)))
  (𝟙 : 𝒞)
  (□ : 𝒞 → 𝒞)
  (□𝒰 : 𝒞)
  (□-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b))
  (□-map𝒰 : ∀ {a} → (a ~>𝒰) → (□ a ~> □𝒰))
  (S : 𝒞) -- Δ (□(S → 𝒰))
  (quote-S : S ~> □ S)
  (ϕ : S ~> (□𝒰 ^ □ S))
  (ϕ⁻¹-□-map𝒰 : (S ~>𝒰) → (𝟙 ~> S))
  (f : □𝒰 ~>𝒰)
  where

rewrap : S ~>𝒰
rewrap = ((dup ⨾ (quote-S ×× ϕ)) ⨾ apply) ⨾𝒰 f

lawvere : (𝟙 ~>𝒰)
lawvere = ϕ⁻¹-□-map𝒰 rewrap ⨾𝒰 rewrap

module _
  (□-𝟙-codistr : 𝟙 ~> □ 𝟙)
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  {u₂} (_≈𝒰_ : ∀ {a} → (a ~>𝒰) → (a ~>𝒰) → Set u₂)
  (𝒞λ : ∀ {a b} (f : a ~> b) → (𝟙 ~> (b ^ a)))
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (_■𝒰_ : ∀ {a} {f : a ~>𝒰} {g : a ~>𝒰} {h : a ~>𝒰} → f ≈𝒰 g → g ≈𝒰 h → f ≈𝒰 h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → (h ⨾ (g ⨾ f)) ≈ ((h ⨾ g) ⨾ f))
  (assoc⁻¹ : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((h ⨾ g) ⨾ f) ≈ (h ⨾ (g ⨾ f)))
  (assoc𝒰 : ∀ {a b c} {h : a ~> b} {g : b ~> c} {f : c ~>𝒰} → (h ⨾𝒰 (g ⨾𝒰 f)) ≈𝒰 ((h ⨾ g) ⨾𝒰 f))
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (2id𝒰 : ∀ {a} {f : a ~>𝒰} → f ≈𝒰 f)
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (_⨾𝒰-map_ : ∀ {a b} {f f‵ : a ~> b} {g g‵ : b ~>𝒰} → f ≈ f‵ → g ≈𝒰 g‵ → (f ⨾𝒰 g) ≈𝒰 (f‵ ⨾𝒰 g‵))
  (××-map : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ×× f′) ⨾ (g ×× g′)) ≈ ((f ⨾ g) ×× (f′ ⨾ g′)))
  (_××-2map_ : ∀ {a b c d} {f f′ : a ~> b} {g g′ : c ~> d} → (f ≈ f′) → (g ≈ g′) → ((f ×× g) ≈ (f′ ×× g′)))
  (dup-×× : ∀ {a b} {f : a ~> b} → (f ⨾ dup) ≈ (dup ⨾ (f ×× f)))
  (apply-λ : ∀ {a b} {f : a ~> b} {g : 𝟙 ~> a} → (dup {𝟙} ⨾ ((g ×× 𝒞λ f) ⨾ apply)) ≈ (g ⨾ f))
  (□-map-⨾𝒰 : ∀ {a b} {f : a ~> b} {g : b ~>𝒰} → (□-map f ⨾ □-map𝒰 g) ≈ □-map𝒰 (f ⨾𝒰 g))
  (□-map-quote-S : ∀ {f : 𝟙 ~> S} → (f ⨾ quote-S) ≈ (□-𝟙-codistr ⨾ □-map f))
  (ϕ-eq : ∀ {f} → (ϕ⁻¹-□-map𝒰 f ⨾ ϕ) ≈ (𝒞λ (□-map𝒰 f)))
  where
  lawvere-fix : lawvere ≈𝒰 ((□-𝟙-codistr ⨾ □-map𝒰 lawvere) ⨾𝒰 f)
  lawvere-fix =
    let eq4 = ××-map ■ (□-map-quote-S ××-2map ϕ-eq) in
    let eq3 = assoc⁻¹ ■ (apply-λ ■ (assoc⁻¹ ■ (2id ⨾-map □-map-⨾𝒰) )) in
    let eq2 = assoc ■ ((dup-×× ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map eq4))) in
    let eq1 = assoc ■ ((eq2 ⨾-map 2id) ■ eq3) in
    assoc𝒰 ■𝒰 (eq1 ⨾𝒰-map 2id𝒰)

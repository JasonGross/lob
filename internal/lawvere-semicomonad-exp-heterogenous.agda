{-# OPTIONS --without-K #-}
module lawvere-semicomonad-exp-heterogenous
  {o a}
  (𝒞 : Set o)
  (_~>_ : 𝒞 → 𝒞 → Set a)
  {u} (_~>𝒰 : 𝒞 → Set u)
  (_⨾_ : ∀ {a b c} → a ~> b → b ~> c → a ~> c)
  (_⨾𝒰_ : ∀ {a b} → a ~> b → b ~>𝒰 → a ~>𝒰)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (𝒰^_ : 𝒞 → 𝒞)
  (apply : ∀ {a} → (a × (𝒰^ a)) ~>𝒰)
  (dup : ∀ {a} → (a ~> (a × a)))
  (_××_ : ∀ {a b c d} → (a ~> b) → (c ~> d) → ((a × c) ~> (b × d)))
  (𝟙 : 𝒞)
  (□ : 𝒞 → 𝒞)
  (□𝒰 : 𝒞)
  (□-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b))
  (□-map𝒰 : ∀ {a} → (a ~>𝒰) → (□ a ~> □𝒰))
  (□-×-codistr : ∀ {a b} → (□ a × □ b) ~> □ (a × b))
  (□-𝟙-codistr : 𝟙 ~> □ 𝟙)
  (quot : ∀ {a} → □ a ~> □ (□ a))
  (S : 𝒞) -- Δ (□S → 𝒰)
  (ϕ : S ~> (𝒰^ □ S))
  (ϕ⁻¹ : (□ S ~>𝒰) → (𝟙 ~> S))
  (f : □𝒰 ~>𝒰)
  where

rewrap : □ S ~>𝒰
rewrap = ((dup ⨾ (quot ×× □-map ϕ)) ⨾ (□-×-codistr ⨾ □-map𝒰 apply)) ⨾𝒰 f

lawvere : (𝟙 ~>𝒰)
lawvere = (□-𝟙-codistr ⨾ □-map (ϕ⁻¹ rewrap)) ⨾𝒰 rewrap

module _
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  {u₂} (_≈𝒰_ : ∀ {a} → (a ~>𝒰) → (a ~>𝒰) → Set u₂)
  (λ𝒰 : ∀ {a} (f : a ~>𝒰) → (𝟙 ~> (𝒰^ a)))
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (_■𝒰_ : ∀ {a} {f : a ~>𝒰} {g : a ~>𝒰} {h : a ~>𝒰} → f ≈𝒰 g → g ≈𝒰 h → f ≈𝒰 h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → (h ⨾ (g ⨾ f)) ≈ ((h ⨾ g) ⨾ f))
  (assoc⁻¹ : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((h ⨾ g) ⨾ f) ≈ (h ⨾ (g ⨾ f)))
  (assoc𝒰 : ∀ {a b c} {h : a ~> b} {g : b ~> c} {f : c ~>𝒰} → (h ⨾𝒰 (g ⨾𝒰 f)) ≈𝒰 ((h ⨾ g) ⨾𝒰 f))
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (2id𝒰 : ∀ {a} {f : a ~>𝒰} → f ≈𝒰 f)
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (_⨾𝒰-map_ : ∀ {a b} {f f‵ : a ~> b} {g g‵ : b ~>𝒰} → f ≈ f‵ → g ≈𝒰 g‵ → (f ⨾𝒰 g) ≈𝒰 (f‵ ⨾𝒰 g‵))
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (××-map : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ×× f′) ⨾ (g ×× g′)) ≈ ((f ⨾ g) ×× (f′ ⨾ g′)))
  (××-map⁻¹ : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ⨾ g) ×× (f′ ⨾ g′)) ≈ ((f ×× f′) ⨾ (g ×× g′)))
  (_××-2map_ : ∀ {a b c d} {f f′ : a ~> b} {g g′ : c ~> d} → (f ≈ f′) → (g ≈ g′) → ((f ×× g) ≈ (f′ ×× g′)))
  (dup-×× : ∀ {a b} {f : a ~> b} → (f ⨾ dup) ≈ (dup ⨾ (f ×× f)))
  (dup-××⁻¹ : ∀ {a b} {f : a ~> b} → (dup ⨾ (f ×× f)) ≈ (f ⨾ dup))
  (apply-λ : ∀ {a} {f : a ~>𝒰} {g : 𝟙 ~> a} → (dup {𝟙} ⨾𝒰 ((g ×× λ𝒰 f) ⨾𝒰 apply)) ≈𝒰 (g ⨾𝒰 f))
  (□-map-⨾ : ∀ {a b c} {f : a ~> b} {g : b ~> c} → (□-map f ⨾ □-map g) ≈ □-map (f ⨾ g))
  (□-map-⨾𝒰 : ∀ {a b} {f : a ~> b} {g : b ~>𝒰} → (□-map f ⨾ □-map𝒰 g) ≈ □-map𝒰 (f ⨾𝒰 g))
  (□-2map : ∀ {a b} {f f′ : a ~> b} → (f ≈ f′) → (□-map f) ≈ (□-map f′))
  (□-2map𝒰 : ∀ {a} {f f′ : a ~>𝒰} → (f ≈𝒰 f′) → (□-map𝒰 f) ≈ (□-map𝒰 f′))
  (dup-□-×-codistr : ∀ {a} → (dup {□ a} ⨾ □-×-codistr) ≈ □-map dup)
  (□-map-××-codistr : ∀ {a b c d} {f : a ~> b} {g : c ~> d} → ((□-map f ×× □-map g) ⨾ □-×-codistr) ≈ (□-×-codistr ⨾ □-map (f ×× g)))
  (□-map-quot : ∀ {a} {f : 𝟙 ~> □ a} → (f ⨾ quot) ≈ (□-𝟙-codistr ⨾ □-map f))
  (ϕ-eq : ∀ {f} → (ϕ⁻¹ f ⨾ ϕ) ≈ (λ𝒰 f))
  where
  lawvere-fix : lawvere ≈𝒰 ((□-𝟙-codistr ⨾ □-map𝒰 lawvere) ⨾𝒰 f)
  lawvere-fix =
    let eq13 = apply-λ in
    let eq12 = assoc ■ ((dup-□-×-codistr ⨾-map 2id) ■ (□-map-⨾𝒰 ■ □-2map𝒰 eq13)) in
    let eq11 = □-map-⨾𝒰 in
    let eq10 = assoc ■ ((□-map-××-codistr ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map eq11))) in
    let eq9 = assoc ■ (dup-××⁻¹ ⨾-map 2id) in
    let eq8 = assoc⁻¹ ■ (2id ⨾-map (□-map-⨾ ■ □-2map ϕ-eq)) in
    let eq7 = □-map-quot in
    let eq6 = ××-map⁻¹ in
    let eq5 = ××-map ■ ((eq7 ××-2map eq8) ■ eq6) in
    let eq4 = assoc⁻¹ ■ ((2id ⨾-map eq5) ■ eq9) in
    let eq3 = assoc⁻¹ ■ (2id ⨾-map (assoc⁻¹ ■ ((2id ⨾-map eq10) ■ eq12))) in
    let eq2 = assoc ■ ((dup-×× ⨾-map 2id) ■ (eq4 ■ assoc⁻¹)) in
    let eq1 = assoc ■ ((eq2 ⨾-map 2id) ■ eq3) in
    assoc𝒰 ■𝒰 (eq1 ⨾𝒰-map 2id𝒰)

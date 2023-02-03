{-# OPTIONS --without-K #-}
module lawvere-alt
  {o a}
  (𝒞 : Set o)
  (_~>_ : 𝒞 → 𝒞 → Set a)
  (id : ∀ {a} → a ~> a)
  (_⨾_ : ∀ {a b c} → a ~> b → b ~> c → a ~> c)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (dup : ∀ {a} → (a ~> (a × a)))
  (_××_ : ∀ {a b c d} → (a ~> b) → (c ~> d) → ((a × c) ~> (b × d)))
  (𝟙 : 𝒞)
  (□ : 𝒞 → 𝒞)
  (□-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b))
  (X : 𝒞)
  (S : 𝒞) -- Δ (□(S → X))
  (quote-S : S ~> □ S)
  (ϕ : (S × □ S) ~> □ X)
  (ϕ⁻¹ : (□ S ~> □ X) → (𝟙 ~> S))
  (f : □ X ~> X)
  where

rewrap : S ~> X
rewrap = ((dup ⨾ (id ×× quote-S)) ⨾ ϕ) ⨾ f

lawvere : (𝟙 ~> X)
lawvere = ϕ⁻¹ (□-map rewrap) ⨾ rewrap

module _
  (□-𝟙-codistr : 𝟙 ~> □ 𝟙)
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → (h ⨾ (g ⨾ f)) ≈ ((h ⨾ g) ⨾ f))
  (assoc⁻¹ : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((h ⨾ g) ⨾ f) ≈ (h ⨾ (g ⨾ f)))
  (rid : ∀ {a b} {f : a ~> b} → (f ⨾ id) ≈ f)
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (××-map : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ×× f′) ⨾ (g ×× g′)) ≈ ((f ⨾ g) ×× (f′ ⨾ g′)))
  (_××-2map_ : ∀ {a b c d} {f f′ : a ~> b} {g g′ : c ~> d} → (f ≈ f′) → (g ≈ g′) → ((f ×× g) ≈ (f′ ×× g′)))
  (dup-×× : ∀ {a b} {f : a ~> b} → (f ⨾ dup) ≈ (dup ⨾ (f ×× f)))
  (□-map-⨾ : ∀ {a b c} {f : a ~> b} {g : b ~> c} → (□-map f ⨾ □-map g) ≈ □-map (f ⨾ g))
  (□-map-quote-S : ∀ {f : 𝟙 ~> S} → (f ⨾ quote-S) ≈ (□-𝟙-codistr ⨾ □-map f))
  (ϕ-eq : ∀ {f : □ S ~> □ X} {g : 𝟙 ~> □ S} → (dup ⨾ (((ϕ⁻¹ f) ×× g) ⨾ ϕ)) ≈ (g ⨾ f))
  where
  lawvere-fix : lawvere ≈ ((□-𝟙-codistr ⨾ □-map lawvere) ⨾ f)
  lawvere-fix =
    let eq4 = ××-map ■ (rid ××-2map □-map-quote-S) in
    let eq3 = assoc⁻¹ ■ (ϕ-eq ■ (assoc⁻¹ ■ (2id ⨾-map □-map-⨾))) in
    let eq2 = assoc ■ ((dup-×× ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map eq4))) in
    let eq1 = assoc ■ ((eq2 ⨾-map 2id) ■ eq3) in
    assoc ■ (eq1 ⨾-map 2id)

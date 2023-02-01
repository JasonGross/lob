{-# OPTIONS --without-K #-}
module lawvere-semicomonad
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
  (□-×-codistr : ∀ {a b} → (□ a × □ b) ~> □ (a × b))
  (□-𝟙-codistr : 𝟙 ~> □ 𝟙)
  (quot : ∀ {a} → □ a ~> □ (□ a))
  (B : 𝒞)
  (inf : 𝒞)
  (ϕ : (inf × □ inf) ~> B)
  (ϕ⁻¹ : (□ inf ~> B) → (𝟙 ~> inf))
  (f : □ B ~> B)
  where

lawvere : (𝟙 ~> B)
lawvere = (□-𝟙-codistr ⨾ □-map (ϕ⁻¹ p)) ⨾ p
  module lawvere where
    p : □ inf ~> B
    p = (dup ⨾ ((id ×× quot) ⨾ (□-×-codistr ⨾ □-map ϕ))) ⨾ f

lawvere-fix : ∀
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → (h ⨾ (g ⨾ f)) ≈ ((h ⨾ g) ⨾ f))
  (assoc⁻¹ : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((h ⨾ g) ⨾ f) ≈ (h ⨾ (g ⨾ f)))
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (rid : ∀ {a b} {f : a ~> b} → (f ⨾ id) ≈ f)
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (dup-×× : ∀ {a b} {f : a ~> b} → (f ⨾ dup) ≈ (dup ⨾ (f ×× f)))
  (××-map : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ×× f′) ⨾ (g ×× g′)) ≈ ((f ⨾ g) ×× (f′ ⨾ g′)))
  (_××-2map_ : ∀ {a b c d} {f f′ : a ~> b} {g g′ : c ~> d} → (f ≈ f′) → (g ≈ g′) → ((f ×× g) ≈ (f′ ×× g′)))
  (□-map-⨾ : ∀ {a b} {f : 𝟙 ~> □ a} {g : □ a ~> b} → (□-map f ⨾ □-map g) ≈ □-map (f ⨾ g))
  (□-map-quot : ∀ {a} {f : 𝟙 ~> □ a} → (f ⨾ quot) ≈ (□-𝟙-codistr ⨾ □-map f))
  (ϕ-eq : ∀ {f : □ inf ~> B} {g : 𝟙 ~> □ (□ inf)} → (dup ⨾ (((□-𝟙-codistr ⨾ □-map (ϕ⁻¹ f)) ×× g) ⨾ (□-×-codistr ⨾ □-map ϕ))) ≈ (g ⨾ □-map f))
  → lawvere ≈ ((□-𝟙-codistr ⨾ □-map lawvere) ⨾ f)
lawvere-fix _≈_ _■_ assoc assoc⁻¹ 2id rid _⨾-map_ dup-×× ××-map _××-2map_ □-map-⨾ □-map-quot ϕ-eq =
  assoc ■ (((assoc ■ (dup-×× ⨾-map 2id)) ■ (assoc⁻¹ ■ ((2id ⨾-map (assoc ■ ((××-map ⨾-map 2id) ■ (((rid ××-2map 2id) ⨾-map 2id))))) ■ (ϕ-eq ■ ((□-map-quot ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map □-map-⨾))))))) ⨾-map 2id)

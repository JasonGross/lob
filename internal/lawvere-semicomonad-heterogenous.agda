{-# OPTIONS --without-K #-}
module lawvere-semicomonad-heterogenous
  {o a}
  (𝒞 : Set o)
  (_~>_ : 𝒞 → 𝒞 → Set a)
  {u} (_~>𝒰 : 𝒞 → Set u)
  (id : ∀ {a} → a ~> a)
  (_⨾_ : ∀ {a b c} → a ~> b → b ~> c → a ~> c)
  (_⨾𝒰_ : ∀ {a b} → a ~> b → b ~>𝒰 → a ~>𝒰)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (dup : ∀ {a} → (a ~> (a × a)))
  (_××_ : ∀ {a b c d} → (a ~> b) → (c ~> d) → ((a × c) ~> (b × d)))
  (𝟙 : 𝒞)
  (□𝒰 : 𝒞)
  (□ : 𝒞 → 𝒞)
  (□-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b))
  (□-map𝒰 : ∀ {a} → (a ~>𝒰) → (□ a ~> □𝒰))
  (□-×-codistr : ∀ {a b} → (□ a × □ b) ~> □ (a × b))
  (□-𝟙-codistr : 𝟙 ~> □ 𝟙)
  (quot : ∀ {a} → □ a ~> □ (□ a))
  (S : 𝒞)
  (ϕ : (S × □ S) ~>𝒰)
  (ϕ⁻¹ : (□ S ~>𝒰) → (𝟙 ~> S))
  (f : □𝒰 ~>𝒰)
  where

lawvere : (𝟙 ~>𝒰)
lawvere = (□-𝟙-codistr ⨾ □-map (ϕ⁻¹ p)) ⨾𝒰 p
  module lawvere where
    p : □ S ~>𝒰
    p = (dup ⨾ ((id ×× quot) ⨾ (□-×-codistr ⨾ □-map𝒰 ϕ))) ⨾𝒰 f
{-
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
  (ϕ-eq : ∀ {f : □ S ~>𝒰} {g : 𝟙 ~> □ (□ S)} → (dup ⨾ (((□-𝟙-codistr ⨾ □-map (ϕ⁻¹ f)) ×× g) ⨾ (□-×-codistr ⨾ □-map ϕ))) ≈ (g ⨾ □-map f))
  → lawvere ≈ ((□-𝟙-codistr ⨾ □-map lawvere) ⨾ f)
lawvere-fix _≈_ _■_ assoc assoc⁻¹ 2id rid _⨾-map_ dup-×× ××-map _××-2map_ □-map-⨾ □-map-quot ϕ-eq =
  assoc ■ (((assoc ■ (dup-×× ⨾-map 2id)) ■ (assoc⁻¹ ■ ((2id ⨾-map (assoc ■ ((××-map ⨾-map 2id) ■ (((rid ××-2map 2id) ⨾-map 2id))))) ■ (ϕ-eq ■ ((□-map-quot ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map □-map-⨾))))))) ⨾-map 2id)
-}

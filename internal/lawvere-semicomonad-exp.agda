{-# OPTIONS --without-K #-}
module lawvere-semicomonad-exp
  {o a}
  (𝒞 : Set o)
  (_~>_ : 𝒞 → 𝒞 → Set a)
  (_⨾_ : ∀ {a b c} → a ~> b → b ~> c → a ~> c)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (_^_ : 𝒞 → 𝒞 → 𝒞)
  (apply : ∀ {a b} → (a × (b ^ a)) ~> b)
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
  (ϕ : inf ~> (B ^ (□ inf)))
  (ϕ⁻¹ : (□ inf ~> B) → (𝟙 ~> inf))
  (f : □ B ~> B)
  where

lawvere : (𝟙 ~> B)
lawvere = (□-𝟙-codistr ⨾ □-map (ϕ⁻¹ p)) ⨾ p
  module lawvere where
    p : □ inf ~> B
    p = (dup ⨾ ((quot ×× (□-map ϕ)) ⨾ (□-×-codistr ⨾ □-map apply))) ⨾ f

lawvere-fix : ∀
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (𝒞λ : ∀ {a b} (f : a ~> b) → (𝟙 ~> (b ^ a)))
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → (h ⨾ (g ⨾ f)) ≈ ((h ⨾ g) ⨾ f))
  (assoc⁻¹ : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((h ⨾ g) ⨾ f) ≈ (h ⨾ (g ⨾ f)))
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (apply-λ : ∀ {a b} {f : a ~> b} {g : 𝟙 ~> a} → (dup {𝟙} ⨾ ((g ×× 𝒞λ f) ⨾ apply)) ≈ (g ⨾ f))
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (dup-×× : ∀ {a b} {f : a ~> b} → (f ⨾ dup) ≈ (dup ⨾ (f ×× f)))
  (dup-××⁻¹ : ∀ {a b} {f : a ~> b} → (dup ⨾ (f ×× f)) ≈ (f ⨾ dup))
  (××-map : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ×× f′) ⨾ (g ×× g′)) ≈ ((f ⨾ g) ×× (f′ ⨾ g′)))
  (××-map⁻¹ : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ⨾ g) ×× (f′ ⨾ g′)) ≈ ((f ×× f′) ⨾ (g ×× g′)))
  (_××-2map_ : ∀ {a b c d} {f f′ : a ~> b} {g g′ : c ~> d} → (f ≈ f′) → (g ≈ g′) → ((f ×× g) ≈ (f′ ×× g′)))
  (□-2map : ∀ {a b} {f f′ : a ~> b} → (f ≈ f′) → (□-map f) ≈ (□-map f′))
  (□-map-⨾ : ∀ {a b c} {f : a ~> b} {g : b ~> c} → (□-map f ⨾ □-map g) ≈ □-map (f ⨾ g))
  (dup-□-×-codistr : ∀ {a} → (dup {□ a} ⨾ □-×-codistr) ≈ □-map dup)
  (□-map-××-codistr : ∀ {a b c d} {f : a ~> b} {g : c ~> d} → ((□-map f ×× □-map g) ⨾ □-×-codistr) ≈ (□-×-codistr ⨾ □-map (f ×× g)))
  (□-map-quot : ∀ {a} {f : 𝟙 ~> □ a} → (f ⨾ quot) ≈ (□-𝟙-codistr ⨾ □-map f))
  (ϕ-eq : ∀ {f} → (ϕ⁻¹ f ⨾ ϕ) ≈ (𝒞λ f))
  → lawvere ≈ ((□-𝟙-codistr ⨾ □-map lawvere) ⨾ f)
lawvere-fix _≈_ 𝒞λ _■_ assoc assoc⁻¹ 2id apply-λ _⨾-map_ dup-×× dup-××⁻¹ ××-map ××-map⁻¹ _××-2map_ □-2map □-map-⨾ dup-□-×-codistr □-map-××-codistr □-map-quot ϕ-eq =
  assoc ■ (((((assoc ■ (dup-×× ⨾-map 2id)) ■ (assoc⁻¹ ■ ((2id ⨾-map ((assoc ■ (((××-map ■ (□-map-quot ××-2map (assoc⁻¹ ■ (2id ⨾-map (□-map-⨾ ■ □-2map ϕ-eq)) ))) ⨾-map 2id))) ■ ((××-map⁻¹ ■ (2id ⨾-map 2id)) ⨾-map 2id))) ■ ((2id ⨾-map (assoc⁻¹ ■ (2id ⨾-map (assoc ■ ((□-map-××-codistr ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map □-map-⨾))))))) ■ (assoc ■ ((dup-××⁻¹ ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map (assoc ■ ((dup-□-×-codistr ⨾-map 2id) ■ (□-map-⨾ ■ □-2map apply-λ)) )))))))))) ⨾-map 2id))

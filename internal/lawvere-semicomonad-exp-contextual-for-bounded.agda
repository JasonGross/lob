{-# OPTIONS --without-K #-}
module lawvere-semicomonad-exp-contextual-for-bounded
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
  (X : 𝒞)
  --{p} (P : (𝟙 ~> □ X) → Set p)
  (ΣP : 𝒞)
  (S : 𝒞) -- S ≔ Δ (Σ_□S R → X)
  {r} (R : (𝟙 ~> □ S) → Set r)
  (ΣR : 𝒞)
  (ΣR-proj₁ : ΣR ~> □ S)
  (quote-ΣR : ΣR ~> □ ΣR)
  {r₂} (R₂ : (ΣR ~> □ X) → Set r₂)
  (p₁ : (k : ΣR ~> □ X) → R₂ k → ΣR ~> ΣP) -- in blöb, this one makes the argument about the expansion-factor of quotation, etc (and does it all under quotes)
  (p₂ : (k : 𝟙 ~> □ S) → R k → 𝟙 ~> ΣR) -- defn of ΣR
  (ϕ : S ~> (X ^ ΣR))
  (ϕ⁻¹ : (ΣR ~> X) → (𝟙 ~> S))
  (f : ΣP ~> X)
  where

pre-k : ΣR ~> □ X
pre-k = (dup ⨾ (quote-ΣR ×× (ΣR-proj₁ ⨾ □-map ϕ))) ⨾ (□-×-codistr ⨾ □-map apply)

module _
  (prop2 : R₂ pre-k) where -- easy if R₂ is (· = pre-k)

  k : ΣR ~> X
  k = p₁ pre-k prop2 ⨾ f

  this-needs-a-better-name : 𝟙 ~> □ S
  this-needs-a-better-name = □-𝟙-codistr ⨾ □-map (ϕ⁻¹ k)

  module _
    (prop3 : R this-needs-a-better-name) -- actually slightly interesting in blöb, forces a lower-bound on size of proof
    where
    lawvere : (𝟙 ~> X)
    lawvere = p₂ this-needs-a-better-name prop3 ⨾ k
{-
lawvere : (𝟙 ~> X)
lawvere = ϕ⁻¹ p ⨾ p
  module lawvere where
    p : □ S ~> X
    p = (dup ⨾ ((quot ×× (□-map ϕ)) ⨾ (□-×-codistr ⨾ □-map apply))) ⨾ f

lawvere-fix : ∀
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (□tt : 𝟙 ~> □ 𝟙)
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
  (□-map-quot : ∀ {a} {f : 𝟙 ~> □ a} → (f ⨾ quot) ≈ (□tt ⨾ □-map f))
  (ϕ-eq : ∀ {f} → (ϕ⁻¹ f ⨾ □-map ϕ) ≈ (□tt ⨾ □-map (𝒞λ f)))
  → lawvere ≈ ((□tt ⨾ □-map lawvere) ⨾ f)
lawvere-fix _≈_ □tt 𝒞λ _■_ assoc assoc⁻¹ 2id apply-λ _⨾-map_ dup-×× dup-××⁻¹ ××-map ××-map⁻¹ _××-2map_ □-2map □-map-⨾ dup-□-×-codistr □-map-××-codistr □-map-quot ϕ-eq =
  assoc ■ (((((assoc ■ (dup-×× ⨾-map 2id)) ■ (assoc⁻¹ ■ ((2id ⨾-map ((assoc ■ (((××-map ■ (□-map-quot ××-2map ϕ-eq)) ⨾-map 2id))) ■ ((××-map⁻¹ ■ (2id ⨾-map 2id)) ⨾-map 2id))) ■ ((2id ⨾-map (assoc⁻¹ ■ (2id ⨾-map (assoc ■ ((□-map-××-codistr ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map □-map-⨾))))))) ■ (assoc ■ ((dup-××⁻¹ ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map (assoc ■ ((dup-□-×-codistr ⨾-map 2id) ■ (□-map-⨾ ■ □-2map apply-λ)) )))))))))) ⨾-map 2id))
-}

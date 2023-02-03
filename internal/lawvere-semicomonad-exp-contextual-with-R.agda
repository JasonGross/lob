{-# OPTIONS --without-K #-}
module lawvere-semicomonad-exp-contextual-with-R
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
  (X : 𝒞)
  {p} (P : (𝟙 ~> X) → Set p)
  (ΣP : 𝒞)
  (S : 𝒞) -- S ~ Σ_(Σ R₁ → ΣP) R₂
  {r₁} (R₁ : (𝟙 ~> S) → Set r₁)
  (ΣR₁ : 𝒞)
  {r₂} (R₂ : (ΣR₁ ~> ΣP) → Set r₂)
  (pair-ΣRΣP : (f : S ~> X) → (∀ (s : 𝟙 ~> S) → R₁ s → P (s ⨾ f)) → (ΣR₁ ~> ΣP))
  (quote-S : S ~> ΣR₁)
  (ϕ₁ : S ~> (ΣP ^ ΣR₁))
  -- We should also have ϕ₂ that says R₂ holds
  (ϕ⁻¹ : (f : ΣR₁ ~> ΣP) → R₂ f → (𝟙 ~> S))
  (f : ΣP ~> X)
  where

pre-rewrap : S ~> X
pre-rewrap = ((dup ⨾ (quote-S ×× ϕ₁)) ⨾ apply) ⨾ f

module _
  (p : ∀ (s : 𝟙 ~> S) → R₁ s → P (s ⨾ pre-rewrap))
  where

  rewrap : ΣR₁ ~> ΣP
  rewrap = pair-ΣRΣP pre-rewrap p

  module _
    (p₂ : R₂ rewrap)
    where

    lawvere : (𝟙 ~> X)
    lawvere = ϕ⁻¹ rewrap p₂ ⨾ pre-rewrap

    module _
      (p₃ : R₁ (ϕ⁻¹ rewrap p₂))
      where

      Plawvere : P lawvere
      Plawvere = p (ϕ⁻¹ rewrap p₂) p₃

{-
module _
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  (𝒞λ : ∀ {a b} (f : a ~> b) → (𝟙 ~> (b ^ a)))
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → (h ⨾ (g ⨾ f)) ≈ ((h ⨾ g) ⨾ f))
  (assoc⁻¹ : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((h ⨾ g) ⨾ f) ≈ (h ⨾ (g ⨾ f)))
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (××-map : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ×× f′) ⨾ (g ×× g′)) ≈ ((f ⨾ g) ×× (f′ ⨾ g′)))
  (××-map⁻¹ : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ⨾ g) ×× (f′ ⨾ g′)) ≈ ((f ×× f′) ⨾ (g ×× g′)))
  (_××-2map_ : ∀ {a b c d} {f f′ : a ~> b} {g g′ : c ~> d} → (f ≈ f′) → (g ≈ g′) → ((f ×× g) ≈ (f′ ×× g′)))
  (dup-×× : ∀ {a b} {f : a ~> b} → (f ⨾ dup) ≈ (dup ⨾ (f ×× f)))
  (dup-××⁻¹ : ∀ {a b} {f : a ~> b} → (dup ⨾ (f ×× f)) ≈ (f ⨾ dup))
  (apply-λ : ∀ {a b} {f : a ~> b} {g : 𝟙 ~> a} → (dup {𝟙} ⨾ ((g ×× 𝒞λ f) ⨾ apply)) ≈ (g ⨾ f))
  (□-map-⨾ : ∀ {a b c} {f : a ~> b} {g : b ~> c} → (□-map f ⨾ □-map g) ≈ □-map (f ⨾ g))
  (□-2map : ∀ {a b} {f f′ : a ~> b} → (f ≈ f′) → (□-map f) ≈ (□-map f′))
  (dup-□-×-codistr : ∀ {a} → (dup {□ a} ⨾ □-×-codistr) ≈ □-map dup)
  (□-map-××-codistr : ∀ {a b c d} {f : a ~> b} {g : c ~> d} → ((□-map f ×× □-map g) ⨾ □-×-codistr) ≈ (□-×-codistr ⨾ □-map (f ×× g)))
  (□-map-quot : ∀ {a} {f : 𝟙 ~> □ a} → (f ⨾ quot) ≈ (□-𝟙-codistr ⨾ □-map f))
  (ϕ-eq : ∀ {f} → (ϕ⁻¹ f ⨾ ϕ) ≈ (𝒞λ f))
  where
  lawvere-fix : lawvere ≈ ((□-𝟙-codistr ⨾ □-map lawvere) ⨾ f)
  lawvere-fix =
    let eq13 = apply-λ in
    let eq12 = assoc ■ ((dup-□-×-codistr ⨾-map 2id) ■ (□-map-⨾ ■ □-2map eq13)) in
    let eq11 = □-map-⨾ in
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
    assoc ■ (eq1 ⨾-map 2id)
    ⊢ □ₖϕ → □𝓔ₖ□ₖϕ
-}

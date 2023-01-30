{-# OPTIONS --without-K #-}
open import common using (Σ ; _,_) -- ; tt) renaming (⊤ to Unit)
module lawvere-semicomonad-via-depmon-exp
  {o a e}
  (𝒳 : Set o)
  (ℳ : 𝒳 → Set a)
  (ext : Σ 𝒳 ℳ → 𝒳)
  (_≈_ : 𝒳 → 𝒳 → Set e)
  (_■_ : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c)
  (sub-ℳ : ∀ {x y} → x ≈ y → ℳ x → ℳ y)
  (ap-ext : ∀ {x y} {e : x ≈ y} {m : ℳ x} → ext (x , m) ≈ ext (y , sub-ℳ e m))
  (T : {x : 𝒳} -> Σ (ℳ x) (λ{ y → ℳ (ext (x , y)) }) → ℳ x)
  (T-law : ∀ {x : 𝒳} {y : ℳ x} {z : ℳ (ext (x , y))} → ext (ext (x , y) , z) ≈ ext (x , (T (y , z))))
  (_×_ : 𝒳 → 𝒳 → 𝒳)
  (_^_ : 𝒳 → 𝒳 → 𝒳)
  --  (I : {x : 𝒳} → Unit {o} → ℳ x)
  where
_▻_ : (x : 𝒳) → ℳ x → 𝒳
x ▻ y = ext (x , y)
infixl 0 _▻_
_⊙_ : ∀ {x} → (y : ℳ x) → ℳ (x ▻ y) → ℳ x
y ⊙ z = T (y , z)
infixl 6 _⊙_
import lawvere-semicomonad-exp
𝒞 : Set o
𝒞 = 𝒳
_~>_ : 𝒞 → 𝒞 → Set _
x ~> y = Σ (ℳ x) λ{ m → y ≈ ext (x , m) }
_⨾_ : ∀ {a b c} → a ~> b → b ~> c → a ~> c
f ⨾ g = f₁ ⊙ sub-ℳ f₂ g₁ , (g₂ ■ ap-ext) ■ T-law
  where
    f₁ = Σ.proj₁ f ; f₂ = Σ.proj₂ f ; g₁ = Σ.proj₁ g ; g₂ = Σ.proj₂ g
postulate
  apply : ∀ {a b} → (a × (b ^ a)) ~> b
  dup : ∀ {a} → (a ~> (a × a))
  _××_ : ∀ {a b c d} → (a ~> b) → (c ~> d) → ((a × c) ~> (b × d))
  𝟙 : 𝒞
  □ : 𝒞 → 𝒞
  □-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b)
  □-×-codistr : ∀ {a b} → (□ a × □ b) ~> □ (a × b)
  quot : ∀ {a} → □ a ~> □ (□ a)
  B : 𝒞
  inf : 𝒞
  ϕ : inf ~> (B ^ (□ inf))
  ϕ⁻¹ : (□ inf ~> B) → (𝟙 ~> □ inf)
  f : □ B ~> B
-- open lawvere-semicomonad-exp 𝒞 _~>_ _⨾_ _×_ _^_ apply dup _××_ 𝟙 □ □-map □-×-codistr quot B inf ϕ ϕ⁻¹ f public
{-
lawvere : (𝟙 ~> B)
lawvere = ϕ⁻¹ p ⨾ p
  module lawvere where
    p : □ inf ~> B
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

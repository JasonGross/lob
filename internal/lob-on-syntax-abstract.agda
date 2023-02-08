{-# OPTIONS --without-K --allow-unsolved-metas #-}
-- We develop Löb's theorem from first principles on a fully abstract type of syntax, contexts, etc
module lob-on-syntax-abstract where

{- First the diagonal lemma -}
module _
  {ℓ₁} {Ctx : Set ℓ₁}
  {ℓ₂} {Ty : Ctx → Set ℓ₂}
  {ℓ₃} {Tm : ∀ {Γ} → Ty Γ → Set ℓ₃}
  (_‘→’_ : ∀ {Γ} → Ty Γ → Ty Γ → Ty Γ)
  (_▻_ : (Γ : Ctx) → Ty Γ → Ctx)
  where
  _~>_ : ∀ {Γ} → Ty Γ → Ty Γ → Set _
  a ~> b = Tm (a ‘→’ b)
  _~>𝒰 : ∀ {Γ} → Ty Γ → Set _
  T ~>𝒰 = Ty (_ ▻ T)
  module _
    (‘id’ : ∀ {Γ} {a : Ty Γ} → a ~> a)
    (_⨾_ : ∀ {Γ} {a b c : Ty Γ} → a ~> b → b ~> c → a ~> c)
    (𝟙 : ∀ {Γ} → Ty Γ)
    (_‘×’_ : ∀ {Γ} → Ty Γ → Ty Γ → Ty Γ)
    (dup : ∀ {Γ} {a : Ty Γ} → (a ~> (a ‘×’ a)))
    (getl : ∀ {Γ} {a b : Ty Γ} → (a ‘×’ b) ~> a)
    (getr : ∀ {Γ} {a b : Ty Γ} → (a ‘×’ b) ~> a)
    (_‘××’_ : ∀ {Γ} {a b c d : Ty Γ} → (a ~> b) → (c ~> d) → ((a ‘×’ c) ~> (b ‘×’ d)))
    (apply : ∀ {Γ} {a b : Ty Γ} → ((a ‘→’ b) ‘×’ a) ~> b)
    (curry : ∀ {Γ} {a b c : Ty Γ} → ((a ‘×’ b) ~> c) → (a ~> (b ‘→’ c)))
    (_⨾𝒰_ : ∀ {Γ} {a b : Ty Γ} → a ~> b → b ~>𝒰 → a ~>𝒰) -- substitution
    (‘Σ’ : ∀ {Γ} → (A : Ty Γ) → Ty (Γ ▻ A) → Ty Γ)
    (‘Π’ : ∀ {Γ} → (A : Ty Γ) → Ty (Γ ▻ A) → Ty Γ)
    (‘Ctx’ : ∀ {Γ} → Ty Γ)
    (‘Ty’ : ∀ {Γ} → Ty (Γ ▻ ‘Ctx’))
    (‘Tm’ : ∀ {Γ} → Ty (Γ ▻ ‘Σ’ ‘Ctx’ ‘Ty’))
    (⌜_⌝c : ∀ {Γ} → Ctx → (𝟙 {Γ} ~> ‘Ctx’))
    (_‘,Σ’_ : ∀ {Γ X A B} → (a : Tm {Γ} (X ‘→’ A)) → Tm {Γ} (‘Π’ X (a ⨾𝒰 B)) → Tm {Γ} (X ‘→’ ‘Σ’ A B))
    (⌜_⌝ : ∀ {Γ C} → Ty C → Tm {Γ} (‘Π’ 𝟙 (⌜ C ⌝c ⨾𝒰 ‘Ty’)))
    where
    □𝒰 : ∀ {Γ} → Ty Γ
    □𝒰 {Γ} = ‘Π’ 𝟙 (⌜ Γ ⌝c ⨾𝒰 ‘Ty’)
    □ : ∀ {Γ} → Ty Γ → Ty Γ
    □ {Γ} T = ‘Π’ 𝟙 ((⌜ Γ ⌝c ‘,Σ’ ⌜ T ⌝) ⨾𝒰 ‘Tm’)
    module _
      (□-map : ∀ {Γ} {a b : Ty Γ} → (a ~> b) → (□ a ~> □ b))
      (□-map𝒰 : ∀ {Γ} {a : Ty Γ} → (a ~>𝒰) → (□ a ~> □𝒰))
      (□-×-codistr : ∀ {Γ} {a b : Ty Γ} → (□ a ‘×’ □ b) ~> □ (a ‘×’ b))
      (□-𝟙-codistr : ∀ {Γ} → 𝟙 {Γ} ~> □ 𝟙)
      (quot : ∀ {Γ} {a : Ty Γ} → □ a ~> □ (□ a))
      (const : ∀ {Γ} {a b : Ty Γ} → Tm {Γ} b → (a ~> b))
      (⌜_⌝ₜ : ∀ {Γ C A} → Tm {C} A → Tm {Γ} (‘Π’ 𝟙 ((⌜ C ⌝c ‘,Σ’ ⌜ A ⌝) ⨾𝒰 ‘Tm’)))
      (‘quote’ : ∀ {Γ} → Tm {Γ} (‘Σ’ ‘Ctx’ ‘Ty’ ‘→’ □ (‘Σ’ ‘Ctx’ ‘Ty’))) -- quotes the quoted context, and then the quoted type.  We should have `(‘quote’ ‘⨾’ ‘proj₂’) ≈ (proj₂ ⨾ quot)` (if that were a thing that typechecked)
      (semidec-eq-proj₁ : ∀ {Γ A} {B : Ty Γ} → (c : Tm {Γ} (𝟙 ‘→’ ‘Ctx’)) → ((‘Π’ 𝟙 (c ⨾𝒰 A)) ~> B) → (𝟙 ~> B) → (‘Σ’ ‘Ctx’ A ~> B))
      (‘subst’ : ∀ {Γ A} → (‘Π’ 𝟙 (⌜ Γ ▻ A ⌝c ⨾𝒰 ‘Ty’) ~> (□ A ‘→’ ‘Π’ 𝟙 (⌜ Γ ⌝c ⨾𝒰 ‘Ty’)))) -- TODO: is there a better type for this?
      --(Wk : ∀ {Γ A} → Ty Γ → Ty (Γ ▻ A))
      --(wk : ∀ {Γ A B} → Tm {Γ} A → Tm {Γ ▻ B} (Wk A))
      where

      S : ∀ {Γ} → Ty Γ
      S = ‘Σ’ ‘Ctx’ ‘Ty’
      quote-S : ∀ {Γ} → S {Γ} ~> □ S
      quote-S = ‘quote’
      ϕ : ∀ {Γ} → S {Γ} ~> (□ S ‘→’ □𝒰)
      ϕ {Γ} = semidec-eq-proj₁ ⌜ Γ ▻ S ⌝c ‘subst’ (curry (const ⌜ 𝟙 ⌝))
      ϕ⁻¹-□-map𝒰 : ∀ {Γ} → (S {Γ} ~>𝒰) → (𝟙 ~> S {Γ})
      ϕ⁻¹-□-map𝒰 {Γ} p = ⌜ Γ ▻ S ⌝c ‘,Σ’ ⌜ p ⌝

      rewrap : ∀ {Γ} → (□𝒰 ~>𝒰) → S {Γ} ~>𝒰
      rewrap f = ((dup ⨾ (ϕ ‘××’ quote-S)) ⨾ apply) ⨾𝒰 f

      lawvere : ∀ {Γ} → (□𝒰 ~>𝒰) → (𝟙 {Γ} ~>𝒰)
      lawvere f = ϕ⁻¹-□-map𝒰 (rewrap f) ⨾𝒰 (rewrap f)

      -- □-map-quote-S : ∀ {f : 𝟙 ~> S} → (f ⨾ quote-S) ≈ (□-𝟙-codistr ⨾ □-map f)
      -- ϕ-eq : ∀ {f : □ S ~> □𝒰} {g : 𝟙 ~> □ S} → (dup ⨾ (((ϕ⁻¹ f) ×× g) ⨾ ϕ)) ≈ (g ⨾ f)
      module _
        {e} (_≈_ : ∀ {Γ} {a b : Ty Γ} → a ~> b → a ~> b → Set e)
        where
        foo : ∀ {Γ} {f : S {Γ} ~>𝒰} → ((ϕ⁻¹-□-map𝒰 f) ⨾ ϕ) ≈ {!!}
        foo = {!!}
{-    □-map𝒰-ϕ : ∀ {Γ} → □S {Γ} ‘×’ □S) ~> □𝒰
    □-map𝒰-ϕ = {!!}
    □-map-ϕ⁻¹ : ∀ {Γ} → (□ (S {Γ}) ~>𝒰) → □ 𝟙 ~> □ (S {Γ})
    □-map-ϕ⁻¹ p = {!!}-}
  {-

  (□-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b))
  (□-map𝒰 : ∀ {a} → (a ~>𝒰) → (□ a ~> □𝒰))
  (S : 𝒞) -- Δ (□(S → 𝒰))
  (quote-S : S ~> □ S)
  (ϕ : (S × □ S) ~> □𝒰)
  (ϕ⁻¹ : (□ S ~> □𝒰) → (𝟙 ~> S))
  (f : □𝒰 ~>𝒰)



  (□-map𝒰 : ∀ {a} → (a ~>𝒰) → (□ a ~> □𝒰))
  (S : 𝒞)
  (f : □𝒰 ~>𝒰)
  where

rewrap : □ S ~>𝒰
rewrap = (dup ⨾ ((id ×× quot) ⨾ (□-×-codistr ⨾ □-map𝒰 ϕ))) ⨾𝒰 f

lawvere : (𝟙 ~>𝒰)
lawvere = (□-𝟙-codistr ⨾ □-map (ϕ⁻¹ rewrap)) ⨾𝒰 rewrap

module _
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  {u₂} (_≈𝒰_ : ∀ {a} → (a ~>𝒰) → (a ~>𝒰) → Set u₂)
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (_■𝒰_ : ∀ {a} {f : a ~>𝒰} {g : a ~>𝒰} {h : a ~>𝒰} → f ≈𝒰 g → g ≈𝒰 h → f ≈𝒰 h)


  (quote-S : S ~> □ S)
  (ϕ : (S × □ S) ~> □𝒰)
  (ϕ⁻¹ : (□ S ~> □𝒰) → (𝟙 ~> S))
  (f : □𝒰 ~>𝒰)

(S : 𝒞) -- Δ (□(S → 𝒰))
  (quote-S : S ~> □ S)
  (ϕ : (S × □ S) ~> □𝒰)
  (ϕ⁻¹ : (□ S ~> □𝒰) → (𝟙 ~> S))
  (f : □𝒰 ~>𝒰)
  where

rewrap : S ~>𝒰
rewrap = ((dup ⨾ (id ×× quote-S)) ⨾ ϕ) ⨾𝒰 f

lawvere : (𝟙 ~>𝒰)
lawvere = ϕ⁻¹ (□-map𝒰 rewrap) ⨾𝒰 rewrap

module _
  (□-𝟙-codistr : 𝟙 ~> □ 𝟙)
  {a₂} (_≈_ : ∀ {a b} → (a ~> b) → (a ~> b) → Set a₂)
  {u₂} (_≈𝒰_ : ∀ {a} → (a ~>𝒰) → (a ~>𝒰) → Set u₂)
  (_■_ : ∀ {a b} {f : a ~> b} {g : a ~> b} {h : a ~> b} → f ≈ g → g ≈ h → f ≈ h)
  (_■𝒰_ : ∀ {a} {f : a ~>𝒰} {g : a ~>𝒰} {h : a ~>𝒰} → f ≈𝒰 g → g ≈𝒰 h → f ≈𝒰 h)
  (assoc : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → (h ⨾ (g ⨾ f)) ≈ ((h ⨾ g) ⨾ f))
  (assoc⁻¹ : ∀ {a b c d} {h : a ~> b} {g : b ~> c} {f : c ~> d} → ((h ⨾ g) ⨾ f) ≈ (h ⨾ (g ⨾ f)))
  (assoc𝒰 : ∀ {a b c} {h : a ~> b} {g : b ~> c} {f : c ~>𝒰} → (h ⨾𝒰 (g ⨾𝒰 f)) ≈𝒰 ((h ⨾ g) ⨾𝒰 f))
  (rid : ∀ {a b} {f : a ~> b} → (f ⨾ id) ≈ f)
  (2id : ∀ {a b} {f : a ~> b} → f ≈ f)
  (2id𝒰 : ∀ {a} {f : a ~>𝒰} → f ≈𝒰 f)
  (_⨾-map_ : ∀ {a b c} {f f‵ : a ~> b} {g g‵ : b ~> c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵))
  (_⨾𝒰-map_ : ∀ {a b} {f f‵ : a ~> b} {g g‵ : b ~>𝒰} → f ≈ f‵ → g ≈𝒰 g‵ → (f ⨾𝒰 g) ≈𝒰 (f‵ ⨾𝒰 g‵))
  (××-map : ∀ {a b c a′ b′ c′} {f : a ~> b} {g : b ~> c} {f′ : a′ ~> b′} {g′ : b′ ~> c′} → ((f ×× f′) ⨾ (g ×× g′)) ≈ ((f ⨾ g) ×× (f′ ⨾ g′)))
  (_××-2map_ : ∀ {a b c d} {f f′ : a ~> b} {g g′ : c ~> d} → (f ≈ f′) → (g ≈ g′) → ((f ×× g) ≈ (f′ ×× g′)))
  (dup-×× : ∀ {a b} {f : a ~> b} → (f ⨾ dup) ≈ (dup ⨾ (f ×× f)))
  (□-map-⨾𝒰 : ∀ {a b} {f : a ~> b} {g : b ~>𝒰} → (□-map f ⨾ □-map𝒰 g) ≈ □-map𝒰 (f ⨾𝒰 g))
  (□-map-quote-S : ∀ {f : 𝟙 ~> S} → (f ⨾ quote-S) ≈ (□-𝟙-codistr ⨾ □-map f))
  (ϕ-eq : ∀ {f : □ S ~> □𝒰} {g : 𝟙 ~> □ S} → (dup ⨾ (((ϕ⁻¹ f) ×× g) ⨾ ϕ)) ≈ (g ⨾ f))
  where
  lawvere-fix : lawvere ≈𝒰 ((□-𝟙-codistr ⨾ □-map𝒰 lawvere) ⨾𝒰 f)
  lawvere-fix =
    let eq4 = ××-map ■ (rid ××-2map □-map-quote-S) in
    let eq3 = assoc⁻¹ ■ (ϕ-eq ■ (assoc⁻¹ ■ (2id ⨾-map □-map-⨾𝒰))) in
    let eq2 = assoc ■ ((dup-×× ⨾-map 2id) ■ (assoc⁻¹ ■ (2id ⨾-map eq4))) in
    let eq1 = assoc ■ ((eq2 ⨾-map 2id) ■ eq3) in
    assoc𝒰 ■𝒰 (eq1 ⨾𝒰-map 2id𝒰)


  (
  (S : 𝒞)
  (ϕ : (S × □ S) ~>𝒰)
  (ϕ⁻¹ : (□ S ~>𝒰) → (𝟙 ~> S))
  (f : □𝒰 ~>𝒰)



  (S : Ty Γ) -- Δ (□(S → 𝒰))
  (quote-S : S ~> □ S)
  (ϕ : S ~> (□𝒰 ^ □ S))
  (ϕ⁻¹ : (□ S ~> □𝒰) → (𝟙 ~> S))
  (f : □𝒰 ~>𝒰)
  where



(𝒰^_ : Ty Γ → TySyntax Γ)
  (apply : ∀ {a} → (a × (𝒰^ a)) ~>𝒰)
  (dup : ∀ {a} → (a ~> (a × a)))
  (_××_ : ∀ {a b c d} → (a ~> b) → (c ~> d) → ((a × c) ~> (b × d)))
  (𝟙 : TySyntax Γ)
  (□ : TySyntax Γ → TySyntax Γ)
  (□𝒰 : TySyntax Γ)
  (□-map : ∀ {a b} → (a ~> b) → (□ a ~> □ b))
  (□-map𝒰 : ∀ {a} → (a ~>𝒰) → (□ a ~> □𝒰))
  (□-×-codistr : ∀ {a b} → (□ a × □ b) ~> □ (a × b))
  (□-𝟙-codistr : 𝟙 ~> □ 𝟙)
  (quot : ∀ {a} → □ a ~> □ (□ a))
  (S : TySyntax Γ) -- Δ (□S → 𝒰)
  (ϕ : S ~> (𝒰^ □ S))
  (ϕ⁻¹ : (□ S ~>𝒰) → (𝟙 ~> S))
  (f : □𝒰 ~>𝒰)


  where
-}

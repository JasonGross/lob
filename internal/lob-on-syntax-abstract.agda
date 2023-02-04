{-# OPTIONS --without-K #-}
-- We develop Löb's theorem from first principles on a fully abstract type of syntax, contexts, etc
module lob-on-syntax-abstract where

{- First the diagonal lemma -}
module _
  {ℓ₁} {CtxSyntax : Set ℓ₁}
  {ℓ₂} {TySyntax : CtxSyntax → Set ℓ₂}
  {ℓ₃} {TmSyntax : ∀ {Γ} → TySyntax Γ → Set ℓ₃}
  (_‘→’_ : ∀ {Γ} → TySyntax Γ → TySyntax Γ → TySyntax Γ)
  (_▻_ : (Γ : CtxSyntax) → TySyntax Γ → CtxSyntax)
  where
  _~>_ : ∀ {Γ} → TySyntax Γ → TySyntax Γ → Set _
  a ~> b = TmSyntax (a ‘→’ b)
  _~>𝒰 : ∀ {Γ} → TySyntax Γ → Set _
  T ~>𝒰 = TySyntax (_ ▻ T)
  module _
    (‘id’ : ∀ {Γ} {a : TySyntax Γ} → a ~> a)
    (_⨾_ : ∀ {Γ} {a b c : TySyntax Γ} → a ~> b → b ~> c → a ~> c)
    (_⨾𝒰_ : ∀ {Γ} {a b : TySyntax Γ} → a ~> b → b ~>𝒰 → a ~>𝒰) -- substitution
    (_‘×’_ : ∀ {Γ} → TySyntax Γ → TySyntax Γ → TySyntax Γ)
    (apply : ∀ {Γ} {a b : TySyntax Γ} → ((a ‘→’ b) ‘×’ a) ~> b)
    (curry : ∀ {Γ} {a b c : TySyntax Γ} → ((a ‘×’ b) ~> c) → (a ~> (b ‘→’ c)))
    (dup : ∀ {Γ} {a : TySyntax Γ} → (a ~> (a ‘×’ a)))
    (_‘××’_ : ∀ {Γ} {a b c d : TySyntax Γ} → (a ~> b) → (c ~> d) → ((a ‘×’ c) ~> (b ‘×’ d)))
    (𝟙 : ∀ {Γ} → TySyntax Γ)
    (‘Σ’ : ∀ {Γ} → (A : TySyntax Γ) → TySyntax (Γ ▻ A) → TySyntax Γ)
    (‘Π’ : ∀ {Γ} → (A : TySyntax Γ) → TySyntax (Γ ▻ A) → TySyntax Γ)
    (‘CtxSyntax’ : ∀ {Γ} → TySyntax Γ)
    (‘TySyntax’ : ∀ {Γ} → TySyntax (Γ ▻ ‘CtxSyntax’))
    (‘TmSyntax’ : ∀ {Γ} → TySyntax (Γ ▻ ‘Σ’ ‘CtxSyntax’ ‘TySyntax’))
    (⌜_⌝c : ∀ {Γ} → CtxSyntax → (𝟙 {Γ} ~> ‘CtxSyntax’))
    (𝟙-law : ∀ {Γ} → TySyntax (Γ ▻ 𝟙) → TySyntax Γ)
    (_‘,Σ’_ : ∀ {Γ X A B} → (a : TmSyntax {Γ} (X ‘→’ A)) → TmSyntax {Γ} (‘Π’ X (a ⨾𝒰 B)) → TmSyntax {Γ} (X ‘→’ ‘Σ’ A B))
    (⌜_⌝ : ∀ {Γ C} → TySyntax C → TmSyntax {Γ} (‘Π’ 𝟙 (⌜ C ⌝c ⨾𝒰 ‘TySyntax’)))
    where
    □𝒰 : ∀ {Γ} → TySyntax Γ
    □𝒰 {Γ} = ‘Π’ 𝟙 (⌜ Γ ⌝c ⨾𝒰 ‘TySyntax’)
    □ : ∀ {Γ} → TySyntax Γ → TySyntax Γ
    □ {Γ} T = 𝟙-law ((⌜ Γ ⌝c ‘,Σ’ ⌜ T ⌝) ⨾𝒰 ‘TmSyntax’)
    module _
      (□-map : ∀ {Γ} {a b : TySyntax Γ} → (a ~> b) → (□ a ~> □ b))
      (□-map𝒰 : ∀ {Γ} {a : TySyntax Γ} → (a ~>𝒰) → (□ a ~> □𝒰))
      (□-×-codistr : ∀ {Γ} {a b : TySyntax Γ} → (□ a ‘×’ □ b) ~> □ (a ‘×’ b))
      (□-𝟙-codistr : ∀ {Γ} → 𝟙 {Γ} ~> □ 𝟙)
      (quot : ∀ {Γ} {a : TySyntax Γ} → □ a ~> □ (□ a))
      (fst : ∀ {Γ} {a b : TySyntax Γ} → (a ‘×’ b) ~> a)
      (const : ∀ {Γ} {a b : TySyntax Γ} → TmSyntax {Γ} b → (a ~> b))
      (⌜_⌝ₜ : ∀ {Γ C A} → TmSyntax {C} A → TmSyntax {Γ} (‘Π’ 𝟙 ((⌜ C ⌝c ‘,Σ’ ⌜ A ⌝) ⨾𝒰 ‘TmSyntax’)))
      (‘quote’ : ∀ {Γ} → TmSyntax {Γ} (‘Σ’ ‘CtxSyntax’ ‘TySyntax’ ‘→’ □ (‘Σ’ ‘CtxSyntax’ ‘TySyntax’))) -- quotes the quoted context, and then the quoted type.  We should have `(‘quote’ ‘⨾’ ‘proj₂’) ≈ (proj₂ ⨾ quot)` (if that were a thing that typechecked)
      (semidec-eq-proj₁ : ∀ {Γ A} {B : TySyntax Γ} → (c : TmSyntax {Γ} (𝟙 ‘→’ ‘CtxSyntax’)) → ((‘Π’ 𝟙 (c ⨾𝒰 A)) ~> B) → (𝟙 ~> B) → (‘Σ’ ‘CtxSyntax’ A ~> B))
      (‘subst’ : ∀ {Γ A} → (‘Π’ 𝟙 (⌜ Γ ▻ A ⌝c ⨾𝒰 ‘TySyntax’) ~> (□ A ‘→’ ‘Π’ 𝟙 (⌜ Γ ⌝c ⨾𝒰 ‘TySyntax’)))) -- TODO: is there a better type for this?
      --(Wk : ∀ {Γ A} → TySyntax Γ → TySyntax (Γ ▻ A))
      --(wk : ∀ {Γ A B} → TmSyntax {Γ} A → TmSyntax {Γ ▻ B} (Wk A))
      where

      S : ∀ {Γ} → TySyntax Γ
      S = ‘Σ’ ‘CtxSyntax’ ‘TySyntax’
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
        {e} (_≈_ : ∀ {Γ} {a b : TySyntax Γ} → a ~> b → a ~> b → Set e)
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



  (S : TySyntax Γ) -- Δ (□(S → 𝒰))
  (quote-S : S ~> □ S)
  (ϕ : S ~> (□𝒰 ^ □ S))
  (ϕ⁻¹ : (□ S ~> □𝒰) → (𝟙 ~> S))
  (f : □𝒰 ~>𝒰)
  where



(𝒰^_ : TySyntax Γ → TySyntax Γ)
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

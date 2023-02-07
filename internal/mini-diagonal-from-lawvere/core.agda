{-# OPTIONS --without-K #-}
module mini-diagonal-from-lawvere.core where

infixl 2 _▻_
infixr 1 _‘→’_
infixl 3 _‘’ₐ_

data CtxSyntax : Set
data TySyntax : CtxSyntax → Set
data TmSyntax : ∀ {Γ} → TySyntax Γ → Set
data CtxSyntax where
  ε : CtxSyntax
  _▻_ : (Γ : CtxSyntax) → (T : TySyntax Γ) → CtxSyntax

_~>𝒰 : ∀ {Γ} → TySyntax Γ → Set _
T ~>𝒰 = TySyntax (_ ▻ T)

data TySyntax where
  _‘→’_ : ∀ {Γ} → (a b : TySyntax Γ) → TySyntax Γ
  _⨾𝒰_ : ∀ {Γ} {a b : TySyntax Γ} → (s : TmSyntax (a ‘→’ b)) → (T : b ~>𝒰) → a ~>𝒰 -- substitution
  _‘×’_ : ∀ {Γ} → (a b : TySyntax Γ) → TySyntax Γ
  𝟙 : ∀ {Γ} → TySyntax Γ
  ‘Σ’ : ∀ {Γ} → (A : TySyntax Γ) → (B : TySyntax (Γ ▻ A)) → TySyntax Γ
  ‘Π’ : ∀ {Γ} → (A : TySyntax Γ) → (B : TySyntax (Γ ▻ A)) → TySyntax Γ
  ‘CtxSyntax’ : ∀ {Γ} → TySyntax Γ
  ‘TySyntax’ : ∀ {Γ} → TySyntax (Γ ▻ ‘CtxSyntax’)
  ‘TmSyntax’ : ∀ {Γ} → TySyntax (Γ ▻ ‘Σ’ ‘CtxSyntax’ ‘TySyntax’)
--  𝟙-law : ∀ {Γ} → TySyntax (Γ ▻ 𝟙) → TySyntax Γ

_~>_ : ∀ {Γ} → TySyntax Γ → TySyntax Γ → Set _
a ~> b = TmSyntax (a ‘→’ b)

□𝒰 : ∀ {Γ} → TySyntax Γ
□ : ∀ {Γ} → TySyntax Γ → TySyntax Γ

data TmSyntax where
  ‘id’ : ∀ {Γ} {a : TySyntax Γ} → a ~> a
  _⨾_ : ∀ {Γ} {a b c : TySyntax Γ} → (f : a ~> b) → (g : b ~> c) → a ~> c
  apply : ∀ {Γ} {a b : TySyntax Γ} → ((a ‘→’ b) ‘×’ a) ~> b
  curry : ∀ {Γ} {a b c : TySyntax Γ} → (f : (a ‘×’ b) ~> c) → (a ~> (b ‘→’ c))
  dup : ∀ {Γ} {a : TySyntax Γ} → (a ~> (a ‘×’ a))
  _‘××’_ : ∀ {Γ} {a b c d : TySyntax Γ} → (f : a ~> b) → (g : c ~> d) → ((a ‘×’ c) ~> (b ‘×’ d))
  ⌜_⌝c : ∀ {Γ} → (C : CtxSyntax) → (𝟙 {Γ} ~> ‘CtxSyntax’)
  □-map : ∀ {Γ} {a b : TySyntax Γ} → (f : a ~> b) → (□ a ~> □ b)
  □-map𝒰 : ∀ {Γ} {a : TySyntax Γ} → (f : a ~>𝒰) → (□ a ~> □𝒰)
  □-×-codistr : ∀ {Γ} {a b : TySyntax Γ} → (□ a ‘×’ □ b) ~> □ (a ‘×’ b)
  □-𝟙-codistr : ∀ {Γ} → 𝟙 {Γ} ~> □ 𝟙
  quot : ∀ {Γ} {a : TySyntax Γ} → □ a ~> □ (□ a)
  fst : ∀ {Γ} {a b : TySyntax Γ} → (a ‘×’ b) ~> a
  _‘,Σ’_ : ∀ {Γ X A B} → (a : TmSyntax {Γ} (X ‘→’ A)) → (b : TmSyntax {Γ} (‘Π’ X (a ⨾𝒰 B))) → TmSyntax {Γ} (X ‘→’ ‘Σ’ A B)
  const : ∀ {Γ} {a b : TySyntax Γ} → (x : TmSyntax {Γ} b) → (a ~> b)
  _‘’ₐ_ : ∀ {Γ a b} → (f : a ~> b) → (x : TmSyntax {Γ} a) → TmSyntax {Γ} b -- hack :-(
  ‘tt’ : ∀ {Γ} → TmSyntax {Γ} 𝟙
  ⌜_⌝ : ∀ {Γ C} → (T : TySyntax C) → TmSyntax {Γ} (‘Π’ 𝟙 (⌜ C ⌝c ⨾𝒰 ‘TySyntax’))
  ⌜_⌝ₜ : ∀ {Γ C A} → (t : TmSyntax {C} A) → TmSyntax {Γ} (‘Π’ 𝟙 ((⌜ C ⌝c ‘,Σ’ ⌜ A ⌝) ⨾𝒰 ‘TmSyntax’))
  ‘quote’ : ∀ {Γ} → TmSyntax {Γ} (‘Σ’ ‘CtxSyntax’ ‘TySyntax’ ‘→’ □ (‘Σ’ ‘CtxSyntax’ ‘TySyntax’)) -- quotes the quoted context, and then the quoted type.  We should have `(‘quote’ ‘⨾’ ‘proj₂’) ≈ (proj₂ ⨾ quot)` (if that were a thing that typechecked)
  semidec-eq-proj₁ : ∀ {Γ A} {B : TySyntax Γ} → (c : TmSyntax {Γ} (𝟙 ‘→’ ‘CtxSyntax’)) → ((‘Π’ 𝟙 (c ⨾𝒰 A)) ~> B) → (𝟙 ~> B) → (‘Σ’ ‘CtxSyntax’ A ~> B)
  ‘subst’ : ∀ {Γ A} → (‘Π’ 𝟙 (⌜ Γ ▻ A ⌝c ⨾𝒰 ‘TySyntax’) ~> (□ A ‘→’ ‘Π’ 𝟙 (⌜ Γ ⌝c ⨾𝒰 ‘TySyntax’))) -- TODO: is there a better type for this?

□𝒰 {Γ} = ‘Π’ 𝟙 (⌜ Γ ⌝c ⨾𝒰 ‘TySyntax’)
□ {Γ} T = ‘Π’ 𝟙 ((⌜ Γ ⌝c ‘,Σ’ ⌜ T ⌝) ⨾𝒰 ‘TmSyntax’)

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

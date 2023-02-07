{-# OPTIONS --without-K --allow-unsolved-metas #-}
module mini-diagonal-from-lawvere.len where
open import mini-diagonal-from-lawvere.core
open import common

Ctx-len : CtxSyntax → ℕ
Ty-len : ∀ {Γ} → TySyntax Γ → ℕ
Tm-len : ∀ {Γ T} → TmSyntax {Γ} T → ℕ

Ctx-len ε = 0
Ctx-len (Γ ▻ T) = suc (Ty-len T)

Ty-len (a ‘→’ b) = suc (max (Ty-len a) (Ty-len b))
Ty-len (s ⨾𝒰 T) = suc (suc (max (Tm-len s) (Ty-len T)))
Ty-len (a ‘×’ b) = suc (max (Ty-len a) (Ty-len b))
Ty-len (𝟙 {Γ}) = suc (Ctx-len Γ)
Ty-len (‘Σ’ A B) = suc (max (Ty-len A) (Ty-len B))
Ty-len (‘Π’ A B) = suc (max (Ty-len A) (Ty-len B))
Ty-len (‘CtxSyntax’ {Γ}) = suc (Ctx-len Γ)
Ty-len (‘TySyntax’ {Γ}) = suc (suc (suc (Ctx-len Γ)))
Ty-len (‘TmSyntax’ {Γ}) = suc (suc (suc (suc (max (Ctx-len Γ) (suc (suc (Ctx-len Γ)))))))

Tm-len (‘id’ {Γ} {a}) = suc (suc (max (Ty-len a) (Ty-len a)))
Tm-len (f ⨾ g) = suc (max (Tm-len f) (Tm-len g))
Tm-len (apply {Γ} {a} {b}) = suc (max (Ty-len a) (Ty-len b))
Tm-len (curry f) = suc (Tm-len f)
Tm-len (dup {Γ} {a}) = suc (Ty-len a)
Tm-len (f ‘××’ g) = suc (max (Tm-len f) (Tm-len g))
Tm-len (⌜_⌝c {Γ} C) = suc (max (Ctx-len Γ) (Ctx-len C))
Tm-len (□-map f) = suc (Tm-len f)
Tm-len (□-map𝒰 f) = suc (Ty-len f)
Tm-len (□-×-codistr {Γ} {a} {b}) = suc (max (Ty-len a) (Ty-len b))
Tm-len (□-𝟙-codistr {Γ}) = suc (Ctx-len Γ)
Tm-len (quot {Γ} {a}) = suc (Ty-len a)
Tm-len (fst {Γ} {a} {b}) = suc (max (Ty-len a) (Ty-len b))
Tm-len (a ‘,Σ’ b) = suc (max (Tm-len a) (Tm-len b))
Tm-len (const {Γ} {a} {b} t) = suc (max (Ty-len a) (Tm-len t))
Tm-len (f ‘’ₐ t) = suc (max (Tm-len f) (Tm-len t))
Tm-len (‘tt’ {Γ}) = suc (Ctx-len Γ)
Tm-len (⌜_⌝ {Γ} T) = suc (max (Ctx-len Γ) (Ty-len T))
Tm-len (⌜_⌝ₜ {Γ} t) = suc (max (Ctx-len Γ) (Tm-len t))
Tm-len (‘quote’ {Γ}) = suc (Ctx-len Γ)
Tm-len (semidec-eq-proj₁ v t f) = suc (max (Tm-len v) (max (Tm-len t) (Tm-len f)))
Tm-len (‘subst’ {Γ} {A}) = suc (Ty-len A)

Ty-len< : ∀ {Γ} T → Ctx-len Γ < Ty-len {Γ} T
Tm-len< : ∀ {Γ T} t → Ty-len T < Tm-len {Γ} {T} t
Ctx-Tm-len< : ∀ {Γ T} t → Ctx-len Γ < Tm-len {Γ} {T} t
Ctx-Tm-len< {Γ} {T} t = <-trans (Ty-len< T) (Tm-len< t)

Ty-len< {Γ} (a ‘→’ b) = <-trans (Ty-len< a) (<-max-spec-L-suc <-suc)
Ty-len< (s ⨾𝒰 T) = <-suc→ (<-max-spec-L-suc <-suc ■< Tm-len< s ■< <-max-spec-L-suc <-suc)
Ty-len< (a ‘×’ b) = <-trans (Ty-len< a) (<-max-spec-L-suc <-suc)
Ty-len< 𝟙 = <-suc
Ty-len< (‘Σ’ A B) = <-trans (Ty-len< A) (<-max-spec-L-suc <-suc)
Ty-len< (‘Π’ A B) = <-trans (Ty-len< A) (<-max-spec-L-suc <-suc)
Ty-len< (‘CtxSyntax’) = <-suc
Ty-len< (‘TySyntax’) = <-suc
Ty-len< (‘TmSyntax’) = <-suc

Tm-len< ‘id’ = <-suc
Tm-len< (_⨾_ {Γ} {a} {b} {c} f g) = <-suc→ (<-max {Ty-len a} {Tm-len f} {Ty-len c} {Tm-len g} {!!} {!!})
Tm-len< apply = {!!}
Tm-len< (curry f) = {!!}
Tm-len< dup = {!!}
Tm-len< (f ‘××’ g) = {!!}
Tm-len< ⌜ C ⌝c = {!!}
Tm-len< (□-map f) = {!!}
Tm-len< (□-map𝒰 f) = {!!}
Tm-len< □-×-codistr = {!!}
Tm-len< □-𝟙-codistr = {!!}
Tm-len< quot = {!!}
Tm-len< fst = {!!}
Tm-len< (t ‘,Σ’ t₁) = {!!}
Tm-len< (const t) = {!!}
Tm-len< (f ‘’ₐ t) = {!!}
Tm-len< ‘tt’ = {!!}
Tm-len< ⌜ T ⌝ = {!!}
Tm-len< ⌜ t ⌝ₜ = {!!}
Tm-len< ‘quote’ = {!!}
Tm-len< (semidec-eq-proj₁ t x x₁) = {!!}
Tm-len< ‘subst’ = {!!}

invert-len-_▻_ : ∀ Γ T → let l = Ctx-len (Γ ▻ T) in (Ctx-len Γ < l) × (Ty-len T < l)
invert-len- Γ ▻ T = {!!}
{-
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


Ctx-len ε = 0
Ctx-len (Γ ▻ T) = suc (Ty-len T)

Ty-len (a ‘→’ b) = suc (Ty-len a + Ty-len b)
Ty-len (s ⨾𝒰 T) = suc (Tm-len s + Ty-len T)
Ty-len (a ‘×’ b) = suc (Ty-len a + Ty-len b)
Ty-len (𝟙 {Γ}) = suc (Ctx-len Γ)
Ty-len (‘Σ’ A B) = suc (Ty-len A + Ty-len B)
Ty-len (‘Π’ A B) = suc (Ty-len A + Ty-len B)
Ty-len (‘CtxSyntax’ {Γ}) = suc (Ctx-len Γ)
Ty-len (‘TySyntax’ {Γ}) = suc (Ctx-len Γ)
Ty-len (‘TmSyntax’ {Γ}) = suc (Ctx-len Γ)

Tm-len (‘id’ {Γ} {a}) = suc (Ty-len a)
Tm-len (f ⨾ g) = suc (Tm-len f + Tm-len g)
Tm-len (apply {Γ} {a} {b}) = suc (Ty-len a + Ty-len b)
Tm-len (curry f) = suc (Tm-len f)
Tm-len (dup {Γ} {a}) = suc (Ty-len a)
Tm-len (f ‘××’ g) = suc (Tm-len f + Tm-len g)
Tm-len (⌜_⌝c {Γ} C) = suc (Ctx-len Γ + Ctx-len C)
Tm-len (□-map f) = suc (Tm-len f)
Tm-len (□-map𝒰 f) = suc (Ty-len f)
Tm-len (□-×-codistr {Γ} {a} {b}) = suc (Ty-len a + Ty-len b)
Tm-len (□-𝟙-codistr {Γ}) = suc (Ctx-len Γ)
Tm-len (quot {Γ} {a}) = suc (Ty-len a)
Tm-len (fst {Γ} {a} {b}) = suc (Ty-len a + Ty-len b)
Tm-len (a ‘,Σ’ b) = suc (Tm-len a + Tm-len b)
Tm-len (const {Γ} {a} {b} t) = suc (Ty-len a + Tm-len t)
Tm-len (f ‘’ₐ t) = suc (Tm-len f + Tm-len t)
Tm-len (‘tt’ {Γ}) = suc (Ctx-len Γ)
Tm-len (⌜_⌝ {Γ} T) = suc (Ctx-len Γ + Ty-len T)
Tm-len (⌜_⌝ₜ {Γ} t) = suc (Ctx-len Γ + Tm-len t)
Tm-len (‘quote’ {Γ}) = suc (Ctx-len Γ)
Tm-len (semidec-eq-proj₁ v t f) = suc (Tm-len v + Tm-len t + Tm-len f)
Tm-len (‘subst’ {Γ} {A}) = suc (Ty-len A)
-}

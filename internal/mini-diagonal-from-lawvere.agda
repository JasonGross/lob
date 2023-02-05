{-# OPTIONS --without-K #-}
module mini-diagonal-from-lawvere where

infixl 2 _▻_
infixr 1 _‘→’_
infixl 3 _‘’ₐ_

data CtxSyntax : Set
data TySyntax : CtxSyntax → Set
data TmSyntax : ∀ {Γ} → TySyntax Γ → Set
data CtxSyntax where
  ε : CtxSyntax
  _▻_ : (Γ : CtxSyntax) → TySyntax Γ → CtxSyntax

_~>𝒰 : ∀ {Γ} → TySyntax Γ → Set _
T ~>𝒰 = TySyntax (_ ▻ T)

data TySyntax where
  _‘→’_ : ∀ {Γ} → TySyntax Γ → TySyntax Γ → TySyntax Γ
  _⨾𝒰_ : ∀ {Γ} {a b : TySyntax Γ} → TmSyntax (a ‘→’ b) → b ~>𝒰 → a ~>𝒰 -- substitution
  _‘×’_ : ∀ {Γ} → TySyntax Γ → TySyntax Γ → TySyntax Γ
  𝟙 : ∀ {Γ} → TySyntax Γ
  ‘Σ’ : ∀ {Γ} → (A : TySyntax Γ) → TySyntax (Γ ▻ A) → TySyntax Γ
  ‘Π’ : ∀ {Γ} → (A : TySyntax Γ) → TySyntax (Γ ▻ A) → TySyntax Γ
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
  _⨾_ : ∀ {Γ} {a b c : TySyntax Γ} → a ~> b → b ~> c → a ~> c
  apply : ∀ {Γ} {a b : TySyntax Γ} → ((a ‘→’ b) ‘×’ a) ~> b
  curry : ∀ {Γ} {a b c : TySyntax Γ} → ((a ‘×’ b) ~> c) → (a ~> (b ‘→’ c))
  dup : ∀ {Γ} {a : TySyntax Γ} → (a ~> (a ‘×’ a))
  _‘××’_ : ∀ {Γ} {a b c d : TySyntax Γ} → (a ~> b) → (c ~> d) → ((a ‘×’ c) ~> (b ‘×’ d))
  ⌜_⌝c : ∀ {Γ} → CtxSyntax → (𝟙 {Γ} ~> ‘CtxSyntax’)
  □-map : ∀ {Γ} {a b : TySyntax Γ} → (a ~> b) → (□ a ~> □ b)
  □-map𝒰 : ∀ {Γ} {a : TySyntax Γ} → (a ~>𝒰) → (□ a ~> □𝒰)
  □-×-codistr : ∀ {Γ} {a b : TySyntax Γ} → (□ a ‘×’ □ b) ~> □ (a ‘×’ b)
  □-𝟙-codistr : ∀ {Γ} → 𝟙 {Γ} ~> □ 𝟙
  quot : ∀ {Γ} {a : TySyntax Γ} → □ a ~> □ (□ a)
  fst : ∀ {Γ} {a b : TySyntax Γ} → (a ‘×’ b) ~> a
  _‘,Σ’_ : ∀ {Γ X A B} → (a : TmSyntax {Γ} (X ‘→’ A)) → TmSyntax {Γ} (‘Π’ X (a ⨾𝒰 B)) → TmSyntax {Γ} (X ‘→’ ‘Σ’ A B)
  const : ∀ {Γ} {a b : TySyntax Γ} → TmSyntax {Γ} b → (a ~> b)
  _‘’ₐ_ : ∀ {Γ a b} → (a ~> b) → TmSyntax {Γ} a → TmSyntax {Γ} b -- hack :-(
  ‘tt’ : ∀ {Γ} → TmSyntax {Γ} 𝟙
  ⌜_⌝ : ∀ {Γ C} → TySyntax C → TmSyntax {Γ} (‘Π’ 𝟙 (⌜ C ⌝c ⨾𝒰 ‘TySyntax’))
  ⌜_⌝ₜ : ∀ {Γ C A} → TmSyntax {C} A → TmSyntax {Γ} (‘Π’ 𝟙 ((⌜ C ⌝c ‘,Σ’ ⌜ A ⌝) ⨾𝒰 ‘TmSyntax’))
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

open import common

CtxSyntax-code : CtxSyntax → CtxSyntax → Set
CtxSyntax-code ε ε = ⊤
CtxSyntax-code ε (_ ▻ _) = ⊥
CtxSyntax-code (x ▻ y) (x' ▻ y') = Σ (x ≡ x') λ p → sub TySyntax p y ≡ y'
CtxSyntax-code (_ ▻ _) ε = ⊥

CtxSyntax-encode : ∀ {x y : CtxSyntax} → x ≡ y → CtxSyntax-code x y
CtxSyntax-encode {ε} refl = tt
CtxSyntax-encode {x ▻ t} refl = refl , refl

CtxSyntax-decode : ∀ {x y : CtxSyntax} → CtxSyntax-code x y → x ≡ y
CtxSyntax-decode {ε} {ε} tt = refl
CtxSyntax-decode {x ▻ y} {_ ▻ _} (refl , refl) = refl

CtxSyntax-deencode : ∀ {x y : CtxSyntax} {p : x ≡ y} → CtxSyntax-decode (CtxSyntax-encode p) ≡ p
CtxSyntax-deencode {ε} {_} {refl} = refl
CtxSyntax-deencode {x ▻ y} {_} {refl} = refl

CtxSyntax-endecode : ∀ {x y : CtxSyntax} (p : CtxSyntax-code x y) → CtxSyntax-encode {x} {y} (CtxSyntax-decode p) ≡ p
CtxSyntax-endecode {ε} {ε} tt = refl
CtxSyntax-endecode {x ▻ x₁} {_ ▻ _} (refl , refl) = refl

TySyntax-code : ∀ {Γ} → TySyntax Γ → TySyntax Γ → Set
TySyntax-code (a ‘→’ b) (a' ‘→’ b') = (a ≡ a') × (b ≡ b')
TySyntax-code (a ‘×’ b) (a' ‘×’ b') = (a ≡ a') × (b ≡ b')
TySyntax-code 𝟙 𝟙 = ⊤
TySyntax-code ‘CtxSyntax’ ‘CtxSyntax’ = ⊤
TySyntax-code ‘TySyntax’ ‘TySyntax’ = ⊤
TySyntax-code ‘TmSyntax’ ‘TmSyntax’ = ⊤
TySyntax-code (‘Σ’ A B) (‘Σ’ A' B') = Σ (A ≡ A') (λ{ p → sub (λ{ A → TySyntax (_ ▻ A) }) p B ≡ B' })
TySyntax-code (‘Π’ A B) (‘Π’ A' B') = Σ (A ≡ A') (λ{ p → sub (λ{ A → TySyntax (_ ▻ A) }) p B ≡ B' })
TySyntax-code (_⨾𝒰_ {Γ} {a} {b} s T) (_⨾𝒰_ {Γ} {a} {b'} s' T') = Σ (b ≡ b') (λ{ p → (sub (λ{ b → _ }) p s ≡ s') × (sub (λ{ b → _ }) p T ≡ T') })
TySyntax-code (a ‘→’ b) _ = ⊥
TySyntax-code (a ‘×’ b) _ = ⊥
TySyntax-code 𝟙 _ = ⊥
TySyntax-code ‘CtxSyntax’ _ = ⊥
TySyntax-code ‘TySyntax’ _ = ⊥
TySyntax-code ‘TmSyntax’ _ = ⊥
TySyntax-code (‘Σ’ A B) _ = ⊥
TySyntax-code (‘Π’ A B) _ = ⊥
TySyntax-code (s ⨾𝒰 T) _ = ⊥

TySyntax-encode : ∀ {Γ} {x y : TySyntax Γ} → x ≡ y → TySyntax-code x y
TySyntax-encode {x = a ‘→’ b} refl = refl , refl
TySyntax-encode {x = s ⨾𝒰 T} refl = refl , (refl , refl)
TySyntax-encode {x = a ‘×’ b} refl = refl , refl
TySyntax-encode {x = 𝟙} refl = tt
TySyntax-encode {x = ‘Σ’ A B} refl = refl , refl
TySyntax-encode {x = ‘Π’ A B} refl = refl , refl
TySyntax-encode {x = ‘CtxSyntax’} refl = tt
TySyntax-encode {x = ‘TySyntax’} refl = tt
TySyntax-encode {x = ‘TmSyntax’} refl = tt

TySyntax-decode : ∀ {Γ} {x y : TySyntax Γ} → TySyntax-code x y → x ≡ y
TySyntax-decode {x = a ‘→’ b} {.a ‘→’ .b} (refl , refl) = refl
TySyntax-decode {x = s ⨾𝒰 T} {_ ⨾𝒰 _} (refl , (refl , refl)) = refl
TySyntax-decode {x = a ‘×’ b} {y} p = {!!}
TySyntax-decode {x = 𝟙} {y} p = {!!}
TySyntax-decode {x = ‘Σ’ A B} {y} p = {!!}
TySyntax-decode {x = ‘Π’ A B} {y} p = {!!}
TySyntax-decode {x = ‘CtxSyntax’} {y} p = {!!}
TySyntax-decode {x = ‘TySyntax’} {y} p = {!!}
TySyntax-decode {x = ‘TmSyntax’} {y} p = {!!}

TySyntax-deencode : ∀ {Γ} {x y : TySyntax Γ} {p : x ≡ y} → TySyntax-decode (TySyntax-encode p) ≡ p
TySyntax-deencode {x = x} {p = refl} = {!!}

TySyntax-endecode : ∀ {Γ} {x y : TySyntax Γ} (p : TySyntax-code x y) → TySyntax-encode {x = x} {y} (TySyntax-decode p) ≡ p
TySyntax-endecode {x = x} {y} p = {!!}

{-


CtxSyntax-decode {A} {just .x₁} {just x₁} refl = refl
CtxSyntax-decode {A} {just x} {nothing} ()
CtxSyntax-decode {A} {nothing} {just x} ()
CtxSyntax-decode {A} {nothing} {nothing} tt = refl

CtxSyntax-deencode : ∀ {A} {x y : CtxSyntax A} {p : x ≡ y} → CtxSyntax-decode (CtxSyntax-encode p) ≡ p
CtxSyntax-deencode {A} {just x} {.(just x)} {refl} = refl
CtxSyntax-deencode {A} {nothing} {.nothing} {refl} = refl

CtxSyntax-endecode : ∀ {A} {x y : CtxSyntax A} (p : CtxSyntax-code x y) → CtxSyntax-encode {A} {x} {y} (CtxSyntax-decode p) ≡ p
CtxSyntax-endecode {A} {just .x'} {just x'} refl = refl
CtxSyntax-endecode {A} {just x} {nothing} ()
CtxSyntax-endecode {A} {nothing} {just x} ()
CtxSyntax-endecode {A} {nothing} {nothing} tt = refl
-}

CtxSyntax-dec-eq : dec-eq CtxSyntax
TySyntax-dec-eq : ∀ {Γ} → dec-eq (TySyntax Γ)
CtxSyntax-dec-eq ε ε = inj₁ refl
CtxSyntax-dec-eq ε (_ ▻ _) = inj₂ λ()
CtxSyntax-dec-eq (x ▻ y) ε = inj₂ λ()
CtxSyntax-dec-eq (x ▻ y) (x' ▻ y') with (CtxSyntax-dec-eq x x')
...                                | inj₁ refl with TySyntax-dec-eq y y'
...                                            | inj₁ refl = inj₁ refl
...                                            | inj₂ n = inj₂ (λ{ p → n {!!} })
CtxSyntax-dec-eq (x ▻ y) (x' ▻ y') | inj₂ n  = inj₂ (λ{ refl → n refl })

semidec-eq-proj₁-implTy : ∀ {Γ} {a b} {A : TySyntax Γ → Set a} {B : Set b}
  → (v : TySyntax Γ) → (t : A v → B) → (f : B) → Σ (TySyntax Γ) A → B
semidec-eq-proj₁-implTy v t f (u , a) = {!!}

semidec-eq-proj₁-impl : ∀ {a b} {A : CtxSyntax → Set a} {B : Set b}
  → (v : CtxSyntax) → (t : A v → B) → (f : B) → Σ CtxSyntax A → B
semidec-eq-proj₁-impl ε t f (ε , a) = t a
semidec-eq-proj₁-impl ε t f (_ ▻ _ , a) = f
semidec-eq-proj₁-impl (v ▻ x) t f (ε , a) = f
semidec-eq-proj₁-impl {A = A} (v ▻ x) t f (u ▻ y , a)
  = semidec-eq-proj₁-impl {A = λ u → Σ (TySyntax u) (λ y' → A (u ▻ y'))} v (semidec-eq-proj₁-implTy x t f) f (u , (y , a))

max-level : Level
max-level = lsuc lzero

CtxSyntax⇓ : (Γ : CtxSyntax) → Set max-level
TySyntax⇓ : {Γ : CtxSyntax} → TySyntax Γ → CtxSyntax⇓ Γ → Set max-level

CtxSyntax⇓ ε = ⊤
CtxSyntax⇓ (Γ ▻ T) = Σ (CtxSyntax⇓ Γ) (TySyntax⇓ {Γ} T)

TmSyntax⇓-helper : ∀ {Γ : CtxSyntax} {T : TySyntax Γ} → TmSyntax T → (Γ⇓ : CtxSyntax⇓ Γ) → TySyntax⇓ T Γ⇓

TySyntax⇓-‘TmSyntax’ : ∀ {Γ} → CtxSyntax⇓ (Γ ▻ ‘Σ’ ‘CtxSyntax’ ‘TySyntax’) → Set max-level

TySyntax⇓ ‘CtxSyntax’ Γ⇓ = Lifted CtxSyntax
TySyntax⇓ (A ‘→’ B) Γ⇓ = TySyntax⇓ A Γ⇓ → TySyntax⇓ B Γ⇓
TySyntax⇓ (s ⨾𝒰 T) Γ⇓ = TySyntax⇓ T (Σ.proj₁ Γ⇓ , TmSyntax⇓-helper s (Σ.proj₁ Γ⇓) (Σ.proj₂ Γ⇓))
TySyntax⇓ (A ‘×’ B) Γ⇓ = TySyntax⇓ A Γ⇓ × TySyntax⇓ B Γ⇓
TySyntax⇓ 𝟙 Γ⇓ = ⊤
TySyntax⇓ (‘Σ’ A B) Γ⇓ = Σ (TySyntax⇓ A Γ⇓) (λ a → TySyntax⇓ B (Γ⇓ , a))
TySyntax⇓ (‘Π’ A B) Γ⇓ = (a : TySyntax⇓ A Γ⇓) → TySyntax⇓ B (Γ⇓ , a)
TySyntax⇓ ‘TySyntax’ Γ⇓ = Lifted (TySyntax (lower (Σ.proj₂ Γ⇓)))
TySyntax⇓ (‘TmSyntax’ {Γ}) Γ⇓ = TySyntax⇓-‘TmSyntax’ {Γ} Γ⇓

TySyntax⇓-‘TmSyntax’ Γ⇓ = Lifted (TmSyntax (lower (Σ.proj₂ (Σ.proj₂ Γ⇓))))

TmSyntax⇓ : ∀ {Γ : CtxSyntax} {T : TySyntax Γ} → TmSyntax T → (Γ⇓ : CtxSyntax⇓ Γ) → TySyntax⇓ T Γ⇓
TmSyntax⇓-helper {Γ} {T} t Γ⇓ = TmSyntax⇓ {Γ} {T} t Γ⇓

TmSyntax⇓-□-map : ∀ {Γ} {a b : TySyntax Γ} → (a ~> b) → ∀ Γ⇓ → TySyntax⇓ (□ a ‘→’ □ b) Γ⇓
TmSyntax⇓-□-map𝒰 : ∀ {Γ} {a : TySyntax Γ} → (a ~>𝒰) → ∀ Γ⇓ → TySyntax⇓ (□ a ‘→’ □𝒰) Γ⇓
TmSyntax⇓-□-×-codistr : ∀ {Γ} {a b : TySyntax Γ} → ∀ Γ⇓ → TySyntax⇓ ((□ a ‘×’ □ b) ‘→’ □ (a ‘×’ b)) Γ⇓
TmSyntax⇓-□-𝟙-codistr : ∀ {Γ} → ∀ Γ⇓ → TySyntax⇓ (𝟙 {Γ} ‘→’ □ 𝟙) Γ⇓
TmSyntax⇓-quot : ∀ {Γ} {a : TySyntax Γ} → ∀ Γ⇓ → TySyntax⇓ (□ a ‘→’ □ (□ a)) Γ⇓
TmSyntax⇓-‘subst’ : ∀ {Γ A} → ∀ Γ⇓ → TySyntax⇓ (‘Π’ 𝟙 (⌜ Γ ▻ A ⌝c ⨾𝒰 ‘TySyntax’) ‘→’ (□ A ‘→’ ‘Π’ 𝟙 (⌜ Γ ⌝c ⨾𝒰 ‘TySyntax’))) Γ⇓
TmSyntax⇓-‘quote’ : ∀ {Γ} → ∀ Γ⇓ → TySyntax⇓ {Γ} (‘Σ’ ‘CtxSyntax’ ‘TySyntax’ ‘→’ □ (‘Σ’ ‘CtxSyntax’ ‘TySyntax’)) Γ⇓
TmSyntax⇓-semidec-eq-proj₁ : ∀ {Γ A} {B : TySyntax Γ} → (c : TmSyntax {Γ} (𝟙 ‘→’ ‘CtxSyntax’)) → ((‘Π’ 𝟙 (c ⨾𝒰 A)) ~> B) → (𝟙 ~> B) → ∀ Γ⇓ → TySyntax⇓ (‘Σ’ ‘CtxSyntax’ A ‘→’ B) Γ⇓

TmSyntax⇓ ‘id’ Γ⇓ = λ x → x
TmSyntax⇓ (f ⨾ g) Γ⇓ = λ x → TmSyntax⇓ g Γ⇓ (TmSyntax⇓ f Γ⇓ x)
TmSyntax⇓ apply Γ⇓ = λ (f , x) → f x
TmSyntax⇓ (curry f) Γ⇓ = λ a b → TmSyntax⇓ f Γ⇓ (a , b)
TmSyntax⇓ dup Γ⇓ = λ x → x , x
TmSyntax⇓ (f ‘××’ g) Γ⇓ = λ (a , b) → TmSyntax⇓ f Γ⇓ a , TmSyntax⇓ g Γ⇓ b
TmSyntax⇓ ⌜ C ⌝c Γ⇓ = λ _ → lift C
TmSyntax⇓ ‘tt’ Γ⇓ = tt
TmSyntax⇓ (f ‘’ₐ x) Γ⇓ = TmSyntax⇓ f Γ⇓ (TmSyntax⇓ x Γ⇓)
TmSyntax⇓ (□-map {Γ} {a} {b} f) Γ⇓ = TmSyntax⇓-□-map {Γ} {a} {b} f Γ⇓
TmSyntax⇓ (□-map𝒰 {Γ} {a} f) Γ⇓ = TmSyntax⇓-□-map𝒰 {Γ} {a} f Γ⇓
TmSyntax⇓ (□-×-codistr {Γ} {a} {b}) Γ⇓ = TmSyntax⇓-□-×-codistr {Γ} {a} {b} Γ⇓
TmSyntax⇓ (□-𝟙-codistr {Γ}) Γ⇓ = TmSyntax⇓-□-𝟙-codistr {Γ} Γ⇓
TmSyntax⇓ (quot {Γ} {a}) Γ⇓ = TmSyntax⇓-quot {Γ} {a} Γ⇓
TmSyntax⇓ fst Γ⇓ = Σ.proj₁
TmSyntax⇓ (f ‘,Σ’ g) Γ⇓ = λ x → TmSyntax⇓ f Γ⇓ x , TmSyntax⇓ g Γ⇓ x
TmSyntax⇓ (const v) Γ⇓ = λ _ → TmSyntax⇓ v Γ⇓
TmSyntax⇓ ⌜ T ⌝ Γ⇓ = λ _ → lift T
TmSyntax⇓ ⌜ t ⌝ₜ Γ⇓ = λ _ → lift t
TmSyntax⇓ (‘quote’ {Γ}) Γ⇓ = TmSyntax⇓-‘quote’ {Γ} Γ⇓
TmSyntax⇓ (semidec-eq-proj₁ {Γ} {A} {B} v t f) Γ⇓ = TmSyntax⇓-semidec-eq-proj₁ {Γ} {A} {B} v t f Γ⇓
TmSyntax⇓ (‘subst’ {Γ} {A}) Γ⇓ = TmSyntax⇓-‘subst’ {Γ} {A} Γ⇓

TmSyntax⇓-□-map' : ∀ {Γ} {a b : TySyntax Γ} → (a ~> b) → ∀ Γ⇓ → TySyntax⇓ (□ a ‘→’ □ b) Γ⇓
TmSyntax⇓-□-map𝒰' : ∀ {Γ} {a : TySyntax Γ} → (a ~>𝒰) → ∀ Γ⇓ → TySyntax⇓ (□ a ‘→’ □𝒰) Γ⇓
TmSyntax⇓-□-×-codistr' : ∀ {Γ} {a b : TySyntax Γ} → ∀ Γ⇓ → TySyntax⇓ ((□ a ‘×’ □ b) ‘→’ □ (a ‘×’ b)) Γ⇓
TmSyntax⇓-□-𝟙-codistr' : ∀ {Γ} → ∀ Γ⇓ → TySyntax⇓ (𝟙 {Γ} ‘→’ □ 𝟙) Γ⇓
TmSyntax⇓-quot' : ∀ {Γ} {a : TySyntax Γ} → ∀ Γ⇓ → TySyntax⇓ (□ a ‘→’ □ (□ a)) Γ⇓
TmSyntax⇓-‘subst’' : ∀ {Γ A} → ∀ Γ⇓ → TySyntax⇓ (‘Π’ 𝟙 (⌜ Γ ▻ A ⌝c ⨾𝒰 ‘TySyntax’) ‘→’ (□ A ‘→’ ‘Π’ 𝟙 (⌜ Γ ⌝c ⨾𝒰 ‘TySyntax’))) Γ⇓
TmSyntax⇓-‘quote’' : ∀ {Γ} → ∀ Γ⇓ → TySyntax⇓ {Γ} (‘Σ’ ‘CtxSyntax’ ‘TySyntax’ ‘→’ □ (‘Σ’ ‘CtxSyntax’ ‘TySyntax’)) Γ⇓
TmSyntax⇓-semidec-eq-proj₁' : ∀ {Γ A} {B : TySyntax Γ} → (c : TmSyntax {Γ} (𝟙 ‘→’ ‘CtxSyntax’)) → ((‘Π’ 𝟙 (c ⨾𝒰 A)) ~> B) → (𝟙 ~> B) → ∀ Γ⇓ → TySyntax⇓ (‘Σ’ ‘CtxSyntax’ A ‘→’ B) Γ⇓


TmSyntax⇓-□-map {Γ} {a} {b} f Γ⇓ = TmSyntax⇓-□-map' {Γ} {a} {b} f Γ⇓
TmSyntax⇓-□-map𝒰 f Γ⇓ = λ x _ → lift {!‘Π’ 𝟙 ?!} -- λ x _ → lift (𝟙-law (const (lower x) ⨾𝒰 f))
TmSyntax⇓-□-×-codistr Γ⇓ = {!!} -- λ (x , y) → lift ((dup ⨾ (const (lower x) ‘××’ const (lower y))) ‘’ₐ ‘tt’)
TmSyntax⇓-□-𝟙-codistr Γ⇓ = {!!} -- λ _ → lift ‘tt’
-- TmSyntax⇓-‘subst’ {Γ} {A} Γ⇓ = {!λ T a _ → lift (𝟙-law (const (lower a) ⨾𝒰 lower (T tt)))!}
TmSyntax⇓-quot Γ⇓ = {!λ a _ → lift ⌜ {!lower (a tt)!} ⌝ₜ!}
TmSyntax⇓-‘subst’ {Γ} {A} Γ⇓ = {!!}-- sub (λ T → T) (TmSyntax⇓-‘subst’-eq {Γ} {A} Γ⇓) {!!} -- λ T a _ → lift (𝟙-law (const (lower a) ⨾𝒰 lower (T tt)))
TmSyntax⇓-‘quote’ {Γ} Γ⇓ = {!!} -- λ (C , T) _ → lift {!? ‘’ₐ ‘tt’!} -- lift {!? ‘’ₐ ‘tt’!}
TmSyntax⇓-semidec-eq-proj₁ {Γ} {A} {B} v t f Γ⇓ = let f' = TmSyntax⇓ f Γ⇓ tt in let t' = λ a → TmSyntax⇓ t Γ⇓ λ{ _ → a } in let v' = TmSyntax⇓ v Γ⇓ tt in {!? v' f' t' !}

TmSyntax⇓-□-map' f Γ⇓ = λ a _ → lift {!f ‘’ₐ ?!} -- ({!f!} ‘’ₐ {!lower a!}) -- λ a → lift {!!} -- ({!f!} ‘’ₐ {!lower a!})
TmSyntax⇓-□-map𝒰' f Γ⇓ = {!!} -- λ x _ → lift (𝟙-law (const (lower x) ⨾𝒰 f))
TmSyntax⇓-□-×-codistr' Γ⇓ = {!!} -- λ (x , y) → lift ((dup ⨾ (const (lower x) ‘××’ const (lower y))) ‘’ₐ ‘tt’)
TmSyntax⇓-□-𝟙-codistr' Γ⇓ = {!!} -- λ _ → lift ‘tt’
-- TmSyntax⇓-‘subst’ {Γ} {A} Γ⇓ = {!λ T a _ → lift (𝟙-law (const (lower a) ⨾𝒰 lower (T tt)))!}
TmSyntax⇓-quot' Γ⇓ = {!λ a _ → lift ⌜ {!lower (a tt)!} ⌝ₜ!}
TmSyntax⇓-‘subst’' {Γ} {A} Γ⇓ = {!!}-- λ T a _ → lift (𝟙-law (const (lower a) ⨾𝒰 lower (T tt)))
TmSyntax⇓-‘quote’' {Γ} Γ⇓ = {!!} -- λ (C , T) _ → lift {!? ‘’ₐ ‘tt’!} -- lift {!? ‘’ₐ ‘tt’!}
TmSyntax⇓-semidec-eq-proj₁' {Γ} {A} {B} v t f Γ⇓ = {!!}

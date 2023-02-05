{-# OPTIONS --without-K #-}
module mini-diagonal-from-lawvere.eq-dec where
open import mini-diagonal-from-lawvere.core
open import common

tag-ctx : CtxSyntax → ℕ
tag-ctx ε = 0
tag-ctx (Γ ▻ x) = 1

tag-ty : ∀ {Γ} → TySyntax Γ → ℕ
tag-ty (t ‘→’ t₁) = 0
tag-ty (x ⨾𝒰 x₁) = 1
tag-ty (t ‘×’ t₁) = 2
tag-ty 𝟙 = 3
tag-ty (‘Σ’ t t₁) = 4
tag-ty (‘Π’ t t₁) = 5
tag-ty ‘CtxSyntax’ = 6
tag-ty ‘TySyntax’ = 7
tag-ty ‘TmSyntax’ = 8

tag-tm : ∀ {Γ T} → TmSyntax {Γ} T → ℕ
tag-tm ‘id’ = 0
tag-tm (x ⨾ x₁) = 1
tag-tm apply = 2
tag-tm (curry x) = 3
tag-tm dup = 4
tag-tm (x ‘××’ x₁) = 5
tag-tm ⌜ x ⌝c = 6
tag-tm (□-map x) = 7
tag-tm (□-map𝒰 x) = 8
tag-tm □-×-codistr = 9
tag-tm □-𝟙-codistr = 10
tag-tm quot = 11
tag-tm fst = 12
tag-tm (t ‘,Σ’ t₁) = 13
tag-tm (const t) = 14
tag-tm (x ‘’ₐ t) = 15
tag-tm ‘tt’ = 16
tag-tm ⌜ x ⌝ = 17
tag-tm ⌜ t ⌝ₜ = 18
tag-tm ‘quote’ = 19
tag-tm (semidec-eq-proj₁ t x x₁) = 20
tag-tm ‘subst’ = 21

args-of-tag-ctx : ℕ → Set
args-of-tag-ctx 0 = ⊤
args-of-tag-ctx 1 = Σ CtxSyntax TySyntax
args-of-tag-ctx _ = ⊥

reconstruct-ctx : ∀ n → args-of-tag-ctx n → CtxSyntax
reconstruct-ctx 0 a = ε
reconstruct-ctx 1 (Γ , T) = Γ ▻ T

deconstruct-ctx : ∀ Γ → args-of-tag-ctx (tag-ctx Γ)
deconstruct-ctx ε = tt
deconstruct-ctx (Γ ▻ T) = Γ , T

reconstruct-ctx-eq : ∀ Γ → reconstruct-ctx (tag-ctx Γ) (deconstruct-ctx Γ) ≡ Γ
reconstruct-ctx-eq ε = refl
reconstruct-ctx-eq (Γ ▻ x) = refl

args-of-tag-ty : ℕ → Set
args-of-tag-ty 0 = Σ _ λ{ Γ → TySyntax Γ × TySyntax Γ }
args-of-tag-ty 1 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ) λ{ (a , b) → TmSyntax (a ‘→’ b) × (b ~>𝒰) } }
args-of-tag-ty 2 = Σ _ λ{ Γ → TySyntax Γ × TySyntax Γ }
args-of-tag-ty 3 = CtxSyntax
args-of-tag-ty 4 = Σ _ λ{ Γ → Σ (TySyntax Γ) λ{ A → TySyntax (Γ ▻ A) } }
args-of-tag-ty 5 = Σ _ λ{ Γ → Σ (TySyntax Γ) λ{ A → TySyntax (Γ ▻ A) } }
args-of-tag-ty 6 = CtxSyntax
args-of-tag-ty 7 = CtxSyntax
args-of-tag-ty 8 = CtxSyntax
args-of-tag-ty _ = ⊥

reconstruct-ty : ∀ n → args-of-tag-ty n → Σ _ TySyntax
reconstruct-ty 0 (Γ , (A , B)) = _ , (A ‘→’ B)
reconstruct-ty 1 (Γ , ((a , b) , (s , T))) = _ , s ⨾𝒰 T
reconstruct-ty 2 (Γ , (A , B)) = _ , A ‘×’ B
reconstruct-ty 3 Γ = _ , 𝟙 {Γ}
reconstruct-ty 4 (Γ , (A , B)) = _ , ‘Σ’ A B
reconstruct-ty 5 (Γ , (A , B)) = _ , ‘Π’ A B
reconstruct-ty 6 Γ = _ , ‘CtxSyntax’ {Γ}
reconstruct-ty 7 Γ = _ , ‘TySyntax’ {Γ}
reconstruct-ty 8 Γ = _ , ‘TmSyntax’ {Γ}

deconstruct-ty : ∀ {Γ} T → args-of-tag-ty (tag-ty {Γ} T)
deconstruct-ty (A ‘→’ B) = _ , (A , B)
deconstruct-ty (s ⨾𝒰 T) = _ , ((_ , _) , (s , T))
deconstruct-ty (A ‘×’ B) = _ , (A , B)
deconstruct-ty (𝟙 {Γ}) = Γ
deconstruct-ty (‘Σ’ A B) = _ , (A , B)
deconstruct-ty (‘Π’ A B) = _ , (A , B)
deconstruct-ty (‘CtxSyntax’ {Γ}) = Γ
deconstruct-ty (‘TySyntax’ {Γ}) = Γ
deconstruct-ty (‘TmSyntax’ {Γ}) = Γ

reconstruct-ty-eq : ∀ {Γ} T → reconstruct-ty (tag-ty T) (deconstruct-ty T) ≡ (Γ , T)
reconstruct-ty-eq (A ‘→’ B) = refl
reconstruct-ty-eq (s ⨾𝒰 T) = refl
reconstruct-ty-eq (A ‘×’ B) = refl
reconstruct-ty-eq 𝟙 = refl
reconstruct-ty-eq (‘Σ’ A B) = refl
reconstruct-ty-eq (‘Π’ A B) = refl
reconstruct-ty-eq ‘CtxSyntax’ = refl
reconstruct-ty-eq ‘TySyntax’ = refl
reconstruct-ty-eq ‘TmSyntax’ = refl
{-
args-of-tag-tm : ℕ → Set
args-of-tag-tm 0 = Σ _ λ{ Γ → TmSyntax Γ × TmSyntax Γ }
args-of-tag-tm 1 = Σ _ λ{ Γ → Σ (TmSyntax Γ × TmSyntax Γ) λ{ (a , b) → TmSyntax (a ‘→’ b) × (b ~>𝒰) } }
args-of-tag-tm 2 = Σ _ λ{ Γ → TmSyntax Γ × TmSyntax Γ }
args-of-tag-tm 3 = CtxSyntax
args-of-tag-tm 4 = Σ _ λ{ Γ → Σ (TmSyntax Γ) λ{ A → TmSyntax (Γ ▻ A) } }
args-of-tag-tm 5 = Σ _ λ{ Γ → Σ (TmSyntax Γ) λ{ A → TmSyntax (Γ ▻ A) } }
args-of-tag-tm 6 = CtxSyntax
args-of-tag-tm 7 = CtxSyntax
args-of-tag-tm 8 = CtxSyntax
args-of-tag-tm _ = ⊥

reconstruct-tm : ∀ n → args-of-tag-tm n → Σ _ TmSyntax
reconstruct-tm 0 (Γ , (A , B)) = _ , (A ‘→’ B)
reconstruct-tm 1 (Γ , ((a , b) , (s , T))) = _ , s ⨾𝒰 T
reconstruct-tm 2 (Γ , (A , B)) = _ , A ‘×’ B
reconstruct-tm 3 Γ = _ , 𝟙 {Γ}
reconstruct-tm 4 (Γ , (A , B)) = _ , ‘Σ’ A B
reconstruct-tm 5 (Γ , (A , B)) = _ , ‘Π’ A B
reconstruct-tm 6 Γ = _ , ‘CtxSyntax’ {Γ}
reconstruct-tm 7 Γ = _ , ‘TmSyntax’ {Γ}
reconstruct-tm 8 Γ = _ , ‘TmSyntax’ {Γ}

deconstruct-tm : ∀ {Γ} T → args-of-tag-tm (tag-tm {Γ} T)
deconstruct-tm (A ‘→’ B) = _ , (A , B)
deconstruct-tm (s ⨾𝒰 T) = _ , ((_ , _) , (s , T))
deconstruct-tm (A ‘×’ B) = _ , (A , B)
deconstruct-tm (𝟙 {Γ}) = Γ
deconstruct-tm (‘Σ’ A B) = _ , (A , B)
deconstruct-tm (‘Π’ A B) = _ , (A , B)
deconstruct-tm (‘CtxSyntax’ {Γ}) = Γ
deconstruct-tm (‘TmSyntax’ {Γ}) = Γ
deconstruct-tm (‘TmSyntax’ {Γ}) = Γ

reconstruct-tm-eq : ∀ {Γ} T → reconstruct-tm (tag-tm T) (deconstruct-tm T) ≡ (Γ , T)
reconstruct-tm-eq (A ‘→’ B) = refl
reconstruct-tm-eq (s ⨾𝒰 T) = refl
reconstruct-tm-eq (A ‘×’ B) = refl
reconstruct-tm-eq 𝟙 = refl
reconstruct-tm-eq (‘Σ’ A B) = refl
reconstruct-tm-eq (‘Π’ A B) = refl
reconstruct-tm-eq ‘CtxSyntax’ = refl
reconstruct-tm-eq ‘TmSyntax’ = refl
reconstruct-tm-eq ‘TmSyntax’ = refl
-}


{-
dec-eqΣ : dec-eq (Σ CtxSyntax (λ Γ → Σ (TySyntax Γ) (λ T → Maybe (TmSyntax {Γ} T))))
dec-eqΣ (Γ , (T , just x)) (Γ' , (T' , just x₁)) = {!!}
dec-eqΣ (Γ , (T , just x)) (Γ' , (T' , nothing)) = inj₂ λ()
dec-eqΣ (Γ , (T , nothing)) (Γ' , (T' , just x)) = inj₂ λ()
dec-eqΣ (_ , ((A ‘→’ B) , nothing)) (_ , (T' , nothing)) = {!!}
dec-eqΣ (_ , ((x ⨾𝒰 x₁) , nothing)) (_ , (T' , nothing)) = {!!}
dec-eqΣ (_ , ((T ‘×’ T₁) , nothing)) (_ , (T' , nothing)) = {!!}
dec-eqΣ (_ , (𝟙 , nothing)) (_ , (T' , nothing)) = {!!}
dec-eqΣ (_ , (‘Σ’ T T₁ , nothing)) (_ , (T' , nothing)) = {!!}
dec-eqΣ (_ , (‘Π’ T T₁ , nothing)) (_ , (T' , nothing)) = {!!}
dec-eqΣ (_ , (‘CtxSyntax’ , nothing)) (_ , (T' , nothing)) = {!!}
dec-eqΣ (_ , (‘TySyntax’ , nothing)) (_ , (T' , nothing)) = {!!}
dec-eqΣ (_ , (‘TmSyntax’ , nothing)) (_ , (T' , nothing)) = {!!}
-}
{-
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
TySyntax-decode {x = a ‘×’ b} {_ ‘×’ _} (refl , refl) = refl
TySyntax-decode {x = 𝟙} {𝟙} tt = refl
TySyntax-decode {x = ‘Σ’ A B} {‘Σ’ _ _} p = {!!}
TySyntax-decode {x = ‘Π’ A B} {‘Π’ _ _} p = {!!}
TySyntax-decode {x = ‘CtxSyntax’} {‘CtxSyntax’} p = {!!}
TySyntax-decode {x = ‘TySyntax’} {‘TySyntax’} p = {!!}
TySyntax-decode {x = ‘TmSyntax’} {‘TmSyntax’} p = {!!}

{-
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

-}
-}

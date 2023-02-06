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

reconstruct-ctx : Σ _ args-of-tag-ctx → CtxSyntax
reconstruct-ctx (0 , a) = ε
reconstruct-ctx (1 , (Γ , T)) = Γ ▻ T

deconstruct-ctx : ∀ Γ → args-of-tag-ctx (tag-ctx Γ)
deconstruct-ctx ε = tt
deconstruct-ctx (Γ ▻ T) = Γ , T

reconstruct-ctx-eq : ∀ Γ → reconstruct-ctx (tag-ctx Γ , deconstruct-ctx Γ) ≡ Γ
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

reconstruct-ty : Σ _ args-of-tag-ty → Σ _ TySyntax
reconstruct-ty (0 , (Γ , (A , B))) = _ , (A ‘→’ B)
reconstruct-ty (1 , (Γ , ((a , b) , (s , T)))) = _ , s ⨾𝒰 T
reconstruct-ty (2 , (Γ , (A , B))) = _ , A ‘×’ B
reconstruct-ty (3 , Γ) = _ , 𝟙 {Γ}
reconstruct-ty (4 , (Γ , (A , B))) = _ , ‘Σ’ A B
reconstruct-ty (5 , (Γ , (A , B))) = _ , ‘Π’ A B
reconstruct-ty (6 , Γ) = _ , ‘CtxSyntax’ {Γ}
reconstruct-ty (7 , Γ) = _ , ‘TySyntax’ {Γ}
reconstruct-ty (8 , Γ) = _ , ‘TmSyntax’ {Γ}

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

reconstruct-ty-eq : ∀ {Γ} T → reconstruct-ty (tag-ty T , deconstruct-ty T) ≡ (Γ , T)
reconstruct-ty-eq (A ‘→’ B) = refl
reconstruct-ty-eq (s ⨾𝒰 T) = refl
reconstruct-ty-eq (A ‘×’ B) = refl
reconstruct-ty-eq 𝟙 = refl
reconstruct-ty-eq (‘Σ’ A B) = refl
reconstruct-ty-eq (‘Π’ A B) = refl
reconstruct-ty-eq ‘CtxSyntax’ = refl
reconstruct-ty-eq ‘TySyntax’ = refl
reconstruct-ty-eq ‘TmSyntax’ = refl

args-of-tag-tm : ℕ → Set
args-of-tag-tm 0 = Σ _ TySyntax
args-of-tag-tm 1 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ × TySyntax Γ) λ{ (a , b , c) → (a ~> b) × (b ~> c) } }
args-of-tag-tm 2 = Σ _ λ{ Γ → TySyntax Γ × TySyntax Γ }
args-of-tag-tm 3 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ × TySyntax Γ) λ{ (a , b , c) → ((a ‘×’ b) ~> c) } }
args-of-tag-tm 4 = Σ _ λ{ Γ → TySyntax Γ }
args-of-tag-tm 5 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ × TySyntax Γ × TySyntax Γ) λ{ (a , b , c , d) → (a ~> b) × (c ~> d) } }
args-of-tag-tm 6 = CtxSyntax × CtxSyntax
args-of-tag-tm 7 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ) λ{ (a , b) → (a ~> b) } }
args-of-tag-tm 8 = Σ _ λ{ Γ → Σ (TySyntax Γ) λ{ a → (a ~>𝒰) } }
args-of-tag-tm 9 = Σ _ λ{ Γ → TySyntax Γ × TySyntax Γ }
args-of-tag-tm 10 = CtxSyntax
args-of-tag-tm 11 = Σ _ λ{ Γ → TySyntax Γ }
args-of-tag-tm 12 = Σ _ λ{ Γ → TySyntax Γ × TySyntax Γ }
args-of-tag-tm 13 = Σ _ λ { Γ → Σ (TySyntax Γ × TySyntax Γ) λ{ (X , A) → Σ _ λ{ B → Σ (TmSyntax {Γ} (X ‘→’ A)) λ{ a → TmSyntax {Γ} (‘Π’ X (a ⨾𝒰 B)) } } } }
args-of-tag-tm 14 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ) λ{ (a , b) → TmSyntax {Γ} b } }
args-of-tag-tm 15 = Σ _ λ{ Γ → Σ (TySyntax Γ × TySyntax Γ) λ{ (a , b) → (a ~> b) × TmSyntax {Γ} a } }
args-of-tag-tm 16 = CtxSyntax
args-of-tag-tm 17 = Σ (CtxSyntax × CtxSyntax) λ{ (Γ , C) → TySyntax C }
args-of-tag-tm 18 = Σ (CtxSyntax × CtxSyntax) λ{ (Γ , C) → Σ _ λ{ A → TmSyntax {C} A } }
args-of-tag-tm 19 = CtxSyntax
args-of-tag-tm 20 = Σ _ λ{ Γ → Σ (_ × TySyntax Γ) λ{ (A , B) → Σ (TmSyntax {Γ} (𝟙 ‘→’ ‘CtxSyntax’)) λ{ c → ((‘Π’ 𝟙 (c ⨾𝒰 A)) ~> B) × (𝟙 ~> B) } } }
args-of-tag-tm (suc 20) = Σ _ λ{ Γ → TySyntax Γ }
args-of-tag-tm _ = ⊥

reconstruct-tm : Σ _ args-of-tag-tm → Σ (Σ _ TySyntax) (λ{ (Γ , T) → TmSyntax {Γ} T })
reconstruct-tm (0 , (Γ , a)) = (_ , _) , ‘id’ {Γ} {a}
reconstruct-tm (1 , (_ , (_ , (f , g)))) = (_ , _) , (f ⨾ g)
reconstruct-tm (2 , (_ , (a , b))) = (_ , _) , apply {_} {a} {b}
reconstruct-tm (3 , (_ , (_ , f))) = (_ , _) , (curry f)
reconstruct-tm (4 , (_ , a)) = (_ , _) , dup {_} {a}
reconstruct-tm (5 , (_ , (_ , (f , g)))) = (_ , _) , (f ‘××’ g)
reconstruct-tm (6 , (Γ , c)) = (_ , _) , ⌜_⌝c {Γ} c
reconstruct-tm (7 , (_ , (_ , f))) = (_ , _) , □-map f
reconstruct-tm (8 , (_ , (_ , f))) = (_ , _) , □-map𝒰 f
reconstruct-tm (9 , (_ , (a , b))) = (_ , _) , □-×-codistr {_} {a} {b}
reconstruct-tm (10 , Γ) = (_ , _) , □-𝟙-codistr {Γ}
reconstruct-tm (11 , (_ , a)) = (_ , _) , quot {_} {a}
reconstruct-tm (12 , (_ , (a , b))) = (_ , _) , fst {_} {a} {b}
reconstruct-tm (13 , (_ , (_ , (_ , (x , y))))) = (_ , _) , (x ‘,Σ’ y)
reconstruct-tm (14 , (_ , ((a , b) , v))) = (_ , _) , (const {_} {a} {b} v)
reconstruct-tm (15 , (_ , (_ , (f , x)))) = (_ , _) , (f ‘’ₐ x)
reconstruct-tm (16 , Γ) = (_ , _) , ‘tt’ {Γ}
reconstruct-tm (17 , ((Γ , C) , T)) = (Γ , _) , ⌜ T ⌝
reconstruct-tm (18 , ((Γ , C) , (T , t))) = (Γ , _) , ⌜ t ⌝ₜ
reconstruct-tm (19 , Γ) = (_ , _) , (‘quote’ {Γ})
reconstruct-tm (20 , (_ , (_ , (c , (t , f))))) = (_ , _) , (semidec-eq-proj₁ c t f)
reconstruct-tm (suc 20 , (Γ , A)) = (_ , _) , ‘subst’ {Γ} {A}

deconstruct-tm : ∀ {Γ T} t → args-of-tag-tm (tag-tm {Γ} {T} t)
deconstruct-tm (‘id’ {Γ} {a}) = _ , a
deconstruct-tm (f ⨾ g) = _ , (_ , _ , _) , f , g
deconstruct-tm (apply {Γ} {a} {b}) = Γ , (a , b)
deconstruct-tm (curry f) = _ , (_ , f)
deconstruct-tm (dup {Γ} {a}) = Γ , a
deconstruct-tm (f ‘××’ g) = _ , (_ , (f , g))
deconstruct-tm (⌜_⌝c {Γ} c) = Γ , c
deconstruct-tm (□-map f) = _ , (_ , f)
deconstruct-tm (□-map𝒰 f) = _ , (_ , f)
deconstruct-tm (□-×-codistr {_} {a} {b}) = _ , (a , b)
deconstruct-tm (□-𝟙-codistr {Γ}) = Γ
deconstruct-tm (quot {_} {a}) = _ , a
deconstruct-tm (fst {_} {a} {b}) = _ , (a , b)
deconstruct-tm (x ‘,Σ’ y) = _ , (_ , (_ , (x , y)))
deconstruct-tm (const {_} {a} {b} t) = _ , ((a , _) , t)
deconstruct-tm (f ‘’ₐ x) = _ , ((_ , _) , (f , x))
deconstruct-tm (‘tt’ {Γ}) = Γ
deconstruct-tm (⌜_⌝ {Γ} T) = (Γ , _) , T
deconstruct-tm (⌜_⌝ₜ {Γ} t) = (Γ , _) , (_ , t)
deconstruct-tm (‘quote’ {Γ}) = Γ
deconstruct-tm (semidec-eq-proj₁ c t f) = _ , ((_ , _) , (c , (t , f)))
deconstruct-tm (‘subst’ {Γ} {A}) = Γ , A

reconstruct-tm-eq : ∀ {Γ T} t → reconstruct-tm (tag-tm t , deconstruct-tm t) ≡ ((Γ , T) , t)
reconstruct-tm-eq ‘id’ = refl
reconstruct-tm-eq (f ⨾ g) = refl
reconstruct-tm-eq apply = refl
reconstruct-tm-eq (curry f) = refl
reconstruct-tm-eq dup = refl
reconstruct-tm-eq (f ‘××’ g) = refl
reconstruct-tm-eq ⌜ c ⌝c = refl
reconstruct-tm-eq (□-map f) = refl
reconstruct-tm-eq (□-map𝒰 f) = refl
reconstruct-tm-eq □-×-codistr = refl
reconstruct-tm-eq □-𝟙-codistr = refl
reconstruct-tm-eq quot = refl
reconstruct-tm-eq fst = refl
reconstruct-tm-eq (x ‘,Σ’ y) = refl
reconstruct-tm-eq (const t) = refl
reconstruct-tm-eq (f ‘’ₐ x) = refl
reconstruct-tm-eq ‘tt’ = refl
reconstruct-tm-eq ⌜ T ⌝ = refl
reconstruct-tm-eq ⌜ t ⌝ₜ = refl
reconstruct-tm-eq ‘quote’ = refl
reconstruct-tm-eq (semidec-eq-proj₁ c t f) = refl
reconstruct-tm-eq ‘subst’ = refl

Ctx-dec-eq : dec-eq CtxSyntax
Ty-dec-eq : dec-eq (Σ _ TySyntax)
Tm-dec-eq : dec-eq (Σ (Σ _ TySyntax) λ{ (Γ , T) → TmSyntax {Γ} T })

Ty-dec-eq-homogenous : ∀ {Γ} → dec-eq (TySyntax Γ)
Ty-dec-eq-homogenous T₁ T₂ with (Ty-dec-eq (_ , T₁) (_ , T₂))
... | inj₁ p = inj₁ (trans (K-from-dec Ctx-dec-eq (λ{ p → T₁ ≡ sub TySyntax p T₁ }) refl) (apD-proj₂ p))
... | inj₂ n = inj₂ λ{ refl → n refl }

Tm-dec-eq-homogenous : ∀ {Γ T} → dec-eq (TmSyntax {Γ} T)
Tm-dec-eq-homogenous T₁ T₂ with (Tm-dec-eq (_ , T₁) (_ , T₂))
... | inj₁ p = inj₁ (trans (K-from-dec Ty-dec-eq (λ{ p → T₁ ≡ sub (λ{ (Γ , T) → TmSyntax {Γ} T }) p T₁ }) refl) (apD-proj₂ p))
... | inj₂ n = inj₂ λ{ refl → n refl }

args-of-tag-ctx-dec-eq : ∀ {n} → dec-eq (args-of-tag-ctx n)
args-of-tag-ctx-dec-eq {0} tt tt = inj₁ refl
args-of-tag-ctx-dec-eq {1} = Ty-dec-eq
args-of-tag-ctx-dec-eq {suc (suc _)} ()

args-of-tag-ty-dec-eq : ∀ {n} → dec-eq (args-of-tag-ty n)
args-of-tag-ty-dec-eq {0} = Σ-dec-eq {!Ctx-dec-eq!} (×-dec-eq {!Ty-dec-eq-homogenous!} {!Ty-dec-eq-homogenous!})
args-of-tag-ty-dec-eq {1} = Σ-dec-eq {!Ctx-dec-eq!} (Σ-dec-eq (×-dec-eq {!!} {!!}) (×-dec-eq {!!} {!!}))
args-of-tag-ty-dec-eq {2} = {!!}
args-of-tag-ty-dec-eq {3} = {!!}
args-of-tag-ty-dec-eq {4} = {!!}
args-of-tag-ty-dec-eq {5} = {!!}
args-of-tag-ty-dec-eq {6} = {!!}
args-of-tag-ty-dec-eq {7} = {!!}
args-of-tag-ty-dec-eq {8} = {!!}
args-of-tag-ty-dec-eq {suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))} ()

args-of-tag-tm-dec-eq : ∀ {n} → dec-eq (args-of-tag-tm n)
args-of-tag-tm-dec-eq {n} = {!!}

Ctx-dec-eq Γ₁ Γ₂ = res
  module Ctx-dec-eq where
    dec-tag : dec-eq-on (tag-ctx Γ₁) (tag-ctx Γ₂)
    dec-tag = ℕ-dec-eq _ _

    dec-args : (p : tag-ctx Γ₁ ≡ tag-ctx Γ₂) → dec-eq-on (sub args-of-tag-ctx p (deconstruct-ctx Γ₁)) (deconstruct-ctx Γ₂)
    dec-args p = args-of-tag-ctx-dec-eq _ _

    res : dec-eq-on Γ₁ Γ₂
    res with dec-tag
    ... | inj₁ p with (dec-args p)
    ...          | inj₁ q = inj₁ (trans (sym (reconstruct-ctx-eq _)) (trans (ap reconstruct-ctx (p ,≡ q)) (reconstruct-ctx-eq _)))
    ...          | inj₂ q = inj₂ (λ{ refl → q (ℕ-K (λ{ p → sub args-of-tag-ctx p (deconstruct-ctx Γ₁) ≡ _ }) refl) })
    res | inj₂ p = inj₂ (λ{ refl → p refl })

Ty-dec-eq ΓT₁@(Γ₁ , T₁) ΓT₂@(Γ₂ , T₂) = res
  module Ty-dec-eq where
    dec-tag : dec-eq-on (tag-ty T₁) (tag-ty T₂)
    dec-tag = ℕ-dec-eq _ _

    dec-args : (p : tag-ty T₁ ≡ tag-ty T₂) → dec-eq-on (sub args-of-tag-ty p (deconstruct-ty T₁)) (deconstruct-ty T₂)
    dec-args p = args-of-tag-ty-dec-eq _ _

    res : dec-eq-on ΓT₁ ΓT₂
    res with dec-tag
    ... | inj₁ p with (dec-args p)
    ...          | inj₁ q = inj₁ (trans (sym (reconstruct-ty-eq _)) (trans (ap reconstruct-ty (p ,≡ q)) (reconstruct-ty-eq _)))
    ...          | inj₂ q = inj₂ (λ{ refl → q (ℕ-K (λ{ p → sub args-of-tag-ty p (deconstruct-ty T₁) ≡ _ }) refl) })
    res | inj₂ p = inj₂ (λ{ refl → p refl })

Tm-dec-eq Γt₁@(_ , t₁) Γt₂@(_ , t₂) = res
  module Tm-dec-eq where
    dec-tag : dec-eq-on (tag-tm t₁) (tag-tm t₂)
    dec-tag = ℕ-dec-eq _ _

    dec-args : (p : tag-tm t₁ ≡ tag-tm t₂) → dec-eq-on (sub args-of-tag-tm p (deconstruct-tm t₁)) (deconstruct-tm t₂)
    dec-args p = args-of-tag-tm-dec-eq _ _

    res : dec-eq-on Γt₁ Γt₂
    res with dec-tag
    ... | inj₁ p with (dec-args p)
    ...          | inj₁ q = inj₁ (trans (sym (reconstruct-tm-eq _)) (trans (ap reconstruct-tm (p ,≡ q)) (reconstruct-tm-eq _)))
    ...          | inj₂ q = inj₂ (λ{ refl → q (ℕ-K (λ{ p → sub args-of-tag-tm p (deconstruct-tm t₁) ≡ _ }) refl) })
    res | inj₂ p = inj₂ (λ{ refl → p refl })


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

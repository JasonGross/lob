{-# OPTIONS --without-K #-}
module mini-diagonal-from-lawvere.interp where
open import mini-diagonal-from-lawvere
open import mini-diagonal-from-lawvere.eq-dec
open import common

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

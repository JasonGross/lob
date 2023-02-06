{-# OPTIONS --without-K #-}
module mini-diagonal-from-lawvere.eq-dec.endecode.Ty where
open import mini-diagonal-from-lawvere.core
open import common

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
TySyntax-decode {x = 𝟙} {𝟙} _ = refl
TySyntax-decode {x = ‘Σ’ A B} {‘Σ’ _ _} (refl , refl) = refl
TySyntax-decode {x = ‘Π’ A B} {‘Π’ _ _} (refl , refl) = refl
TySyntax-decode {x = ‘CtxSyntax’} {‘CtxSyntax’} _ = refl
TySyntax-decode {x = ‘TySyntax’} {‘TySyntax’} _ = refl
TySyntax-decode {x = ‘TmSyntax’} {‘TmSyntax’} _ = refl

TySyntax-deencode : ∀ {Γ} {x y : TySyntax Γ} {p : x ≡ y} → TySyntax-decode (TySyntax-encode p) ≡ p
TySyntax-deencode {x = x ‘→’ x₁} {p = refl} = refl
TySyntax-deencode {x = x ⨾𝒰 x₁} {p = refl} = refl
TySyntax-deencode {x = x ‘×’ x₁} {p = refl} = refl
TySyntax-deencode {x = 𝟙} {p = refl} = refl
TySyntax-deencode {x = ‘Σ’ x x₁} {p = refl} = refl
TySyntax-deencode {x = ‘Π’ x x₁} {p = refl} = refl
TySyntax-deencode {x = ‘CtxSyntax’} {p = refl} = refl
TySyntax-deencode {x = ‘TySyntax’} {p = refl} = refl
TySyntax-deencode {x = ‘TmSyntax’} {p = refl} = refl

TySyntax-endecode : ∀ {Γ} {x y : TySyntax Γ} (p : TySyntax-code x y) → TySyntax-encode {x = x} {y} (TySyntax-decode p) ≡ p
TySyntax-endecode {x = a ‘→’ b} {.a ‘→’ .b} (refl , refl) = refl
TySyntax-endecode {x = s ⨾𝒰 T} {_ ⨾𝒰 _} (refl , (refl , refl)) = refl
TySyntax-endecode {x = a ‘×’ b} {_ ‘×’ _} (refl , refl) = refl
TySyntax-endecode {x = 𝟙} {𝟙} _ = refl
TySyntax-endecode {x = ‘Σ’ A B} {‘Σ’ _ _} (refl , refl) = refl
TySyntax-endecode {x = ‘Π’ A B} {‘Π’ _ _} (refl , refl) = refl
TySyntax-endecode {x = ‘CtxSyntax’} {‘CtxSyntax’} _ = refl
TySyntax-endecode {x = ‘TySyntax’} {‘TySyntax’} _ = refl
TySyntax-endecode {x = ‘TmSyntax’} {‘TmSyntax’} _ = refl

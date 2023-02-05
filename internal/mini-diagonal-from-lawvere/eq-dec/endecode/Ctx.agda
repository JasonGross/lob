{-# OPTIONS --without-K #-}
module mini-diagonal-from-lawvere.eq-dec.endecode.Ctx where
open import mini-diagonal-from-lawvere
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

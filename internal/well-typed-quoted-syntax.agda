{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers public
open import well-typed-quoted-syntax-defs public
open import well-typed-syntax-context-helpers public
open import well-typed-syntax-eq-dec public

infixr 2 _‘‘∘’’_

quote-sigma : (Γv : Σ Context Typ) → Term {ε} (‘Σ’ ‘Context’ ‘Typ’)
quote-sigma (Γ , v) = ‘existT’ ⌜ Γ ⌝c ⌜ v ⌝T

_‘‘∘’’_ : ∀ {A B C}
    → □ (‘□’ ‘’ (C ‘‘→'’’ B))
    → □ (‘□’ ‘’ (A ‘‘→'’’ C))
    → □ (‘□’ ‘’ (A ‘‘→'’’ B))
g ‘‘∘’’ f = (‘‘fcomp-nd’’ ‘'’ₐ f ‘'’ₐ g)

Conv0 : ∀ {qH0 qX} →
    Term {Γ = (ε ▻ ‘□’ ‘’ qH0)}
          (W (‘□’ ‘’ ⌜ ‘□’ ‘’ qH0 ‘→'’ qX ⌝T))
    → Term {Γ = (ε ▻ ‘□’ ‘’ qH0)}
             (W
                (‘□’ ‘’ (⌜ ‘□’ ‘’ qH0 ⌝T ‘‘→'’’ ⌜ qX ⌝T)))
Conv0 {qH0} {qX} x = w→ ⌜→'⌝ ‘'’ₐ x

{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers public
open import well-typed-syntax-context-helpers public
open import well-typed-quoted-syntax-postulates public
open import well-typed-quoted-syntax-defs public

infixr 2 _‘‘∘’’_

‘β’ = qbeta-nd
‘β'’ = qbeta-nd-inv

⌜⌜⌝⌝' = qquote-term-under-app-inv



⌜‘’⌝' = quote-undistr-substTyp


quote-sigma : (Γv : Σ Typ) → Term (‘Σ’ ‘Context’ ‘Typ’)
quote-sigma (Γ , v) = ‘existT’ ⌜ Γ ⌝c ⌜ v ⌝T

⌜→'⌝ = quote-typ-distr-tProd-nd

⌜←'⌝ = quote-typ-undistr-tProd-nd

_‘‘∘’’_ : ∀ {A B C}
    → □ (‘□’ ‘’ (C ‘‘→'’’ B))
    → □ (‘□’ ‘’ (A ‘‘→'’’ C))
    → □ (‘□’ ‘’ (A ‘‘→'’’ B))
g ‘‘∘’’ f = (‘‘fcomp-nd’’ ‘'’ₐ f ‘'’ₐ g)

‘ssw1’ = qsubstTerm-substTerm-weakenTerm1-S₂₀₀W1WW

‘ssw1'’ = qsubstTerm-substTerm-weakenTerm1-S₂₀₀W1WW-inv

‘s→→’ = qsubstTerm-qtApp-nd-qtApp-nd-distr

‘s←←’ = qsubstTerm-qtApp-nd-qtApp-nd-undistr

‘context-pick-if’ : ∀ (dummy : Term (‘Typ’ ‘’ ⌜ (ε ▻ ‘Σ’ ‘Context’ ‘Typ’) ⌝c))
  → □ (‘Context’ ‘→’ ‘Typ’ ‘→'’ W (‘Typ’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c))
‘context-pick-if’ dummy = ‘context-pick-if'’ {ε} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} ‘'’ₐ dummy

‘cast’ : □ (‘Σ’ ‘Context’ ‘Typ’ ‘→'’ ‘Typ’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c)
‘cast’ = ‘λ'∙’ ((SW1W (S₁₀W2W (substTyp-tProd (weakenTyp1-tProd (w1
                                                                          (SW1V
                                                                           (w∀ (‘context-pick-if’ ⌜ W (‘Typ’ ‘’ ‘ε’) ⌝T) ‘’ₐ ‘VAR₀’))) ‘t’ (w→ ‘proj₁’ ‘'’ₐ ‘VAR₀’)) ‘’ₐ ‘proj₂’ ))))


‘cast-refl’ : ∀ {T : Typ (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)} →
    □ (‘□’ ‘’
        ((⌜ T ‘’ quote-sigma (ε ▻ ‘Σ’ ‘Context’ ‘Typ’ , T) ⌝T)
           ‘‘→'’’
           (‘cast’ ‘'’ₐ quote-sigma (ε ▻ ‘Σ’ ‘Context’ ‘Typ’ , T)
             ‘‘’’ (‘quote-sigma’ ‘'’ₐ quote-sigma (ε ▻ ‘Σ’ ‘Context’ ‘Typ’ , T)))))
‘cast-refl’ = ‘cast-refl’₀

‘cast-refl'’ : ∀ {T} →
    □ (‘□’ ‘’
        ((‘cast’ ‘'’ₐ quote-sigma (ε ▻ ‘Σ’ ‘Context’ ‘Typ’ , T)
           ‘‘’’ (‘quote-sigma’ ‘'’ₐ quote-sigma (ε ▻ ‘Σ’ ‘Context’ ‘Typ’ , T)))
           ‘‘→'’’ (⌜ T ‘’ quote-sigma (ε ▻ ‘Σ’ ‘Context’ ‘Typ’ , T) ⌝T)))
‘cast-refl'’ = ⌜‘’⌝' ‘‘∘’’ ‘context-pick-if’-refl ‘‘∘’’ ⌜⌜⌝⌝' ‘‘∘’’ qexistT-iota ‘‘∘’’ substTerm-distr-stuff ‘‘∘’’ ‘β’

Conv0 : ∀ {qH0 qX} →
    Term {Γ = (ε ▻ ‘□’ ‘’ qH0)}
          (W (‘□’ ‘’ ⌜ ‘□’ ‘’ qH0 ‘→'’ qX ⌝T))
    → Term {Γ = (ε ▻ ‘□’ ‘’ qH0)}
             (W
                (‘□’ ‘’ (⌜ ‘□’ ‘’ qH0 ⌝T ‘‘→'’’ ⌜ qX ⌝T)))
Conv0 {qH0} {qX} x = w→ quote-typ-distr-tProd-nd ‘'’ₐ x

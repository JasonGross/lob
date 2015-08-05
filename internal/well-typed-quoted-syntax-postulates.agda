{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax-postulates where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers
open import well-typed-syntax-context-helpers
open import well-typed-quoted-syntax-defs public

postulate
  qsubstTerm-qtApp-nd-qtApp-nd-distr : ∀ {T B}
         {b : Term {ε} (T ‘→'’ ‘Typ’ ‘’ ⌜ ε ▻ B ⌝c)}
         {c : Term {ε} (T ‘→'’ ‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ B ⌝T)}
         {v : Term {ε} T} →
    (Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c
         ‘’ ((SW (((w→ b ‘'’ₐ ‘VAR₀’) w‘‘’’ (w→ c ‘'’ₐ ‘VAR₀’) ‘t’ v)))
               ‘‘→'’’ ((b ‘'’ₐ v) ‘‘’’ (c ‘'’ₐ v)))))
-- qsubstTerm-qtApp-nd-qtApp-nd-distr = {!!}
  qsubstTerm-qtApp-nd-qtApp-nd-undistr : ∀ {T B}
         {b : Term {ε} (T ‘→'’ ‘Typ’ ‘’ ⌜ ε ▻ B ⌝c)}
         {c : Term {ε} (T ‘→'’ ‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ B ⌝T)}
         {v : Term {ε} T} →
    (Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c
         ‘’ (((b ‘'’ₐ v) ‘‘’’ (c ‘'’ₐ v))
               ‘‘→'’’ (SW (((w→ b ‘'’ₐ ‘VAR₀’) w‘‘’’ (w→ c ‘'’ₐ ‘VAR₀’) ‘t’ v))))))
-- qsubstTerm-qtApp-nd-qtApp-nd-undistr = {!!}

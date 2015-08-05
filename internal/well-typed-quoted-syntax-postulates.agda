{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax-postulates where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers
open import well-typed-syntax-context-helpers
open import well-typed-quoted-syntax-defs public

postulate
  ‘context-pick-if’-refl-inv : ∀ {T dummy qqs} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          ((⌜ T ⌝T ‘‘’’ ⌜ qqs ⌝t)
             ‘‘→'’’
             ((S₁₀WW (substTyp-tProd (‘context-pick-if'’ {ε} ‘'’ₐ ⌜ dummy ⌝T ‘’ₐ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c) ‘’ₐ ⌜ T ⌝T))
                ‘‘’’ ⌜ qqs ⌝t)))
  ‘context-pick-if’-refl : ∀ {T dummy qqs} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          ((S₁₀WW (substTyp-tProd (‘context-pick-if'’ {ε} ‘'’ₐ ⌜ dummy ⌝T ‘’ₐ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c) ‘’ₐ ⌜ T ⌝T)
              ‘‘’’ ⌜ qqs ⌝t)
             ‘‘→'’’
             (⌜ T ⌝T ‘‘’’ ⌜ qqs ⌝t)))



postulate
  ‘tApp-nd’ : ∀ {Γ} {A : Term {ε} (‘Typ’ ‘’ Γ)} {B : Term {ε} (‘Typ’ ‘’ Γ)} →
    Term {ε} (‘Term’ ‘’₁ Γ ‘’ (A ‘‘→'’’ B)
        ‘→'’ ‘Term’ ‘’₁ Γ ‘’ A
        ‘→'’ ‘Term’ ‘’₁ Γ ‘’ B)
-- ‘tApp-nd’ = {!!}

  quote-typ-undistr-tProd-nd : ∀ {H X} →
    Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (⌜ H ⌝T ‘‘→'’’ ⌜ X ⌝T)
        ‘→'’ ‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ H ‘→'’ X ⌝T)
-- quote-typ-undistr-tProd-nd = {!!}

  quote-typ-distr-tProd-nd : ∀ {H X} →
    Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ H ‘→'’ X ⌝T
        ‘→'’ ‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (⌜ H ⌝T ‘‘→'’’ ⌜ X ⌝T))
-- quote-typ-distr-tProd-nd = {!!}

  ‘‘fcomp-nd’’ : ∀ {A B C} →
    Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (A ‘‘→'’’ C)
        ‘→'’ ‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (C ‘‘→'’’ B)
        ‘→'’ ‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ (A ‘‘→'’’ B))
-- ‘‘fcomp-nd’’ = {!!}

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

postulate

  quote-distr-substTyp : ∀ {B A} {b : Term {ε} B} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          (⌜ A ‘’ b ⌝T ‘‘→'’’ ⌜ A ⌝T ‘‘’’ ⌜ b ⌝t))
  quote-undistr-substTyp : ∀ {B A} {b : Term {ε} B} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          (⌜ A ⌝T ‘‘’’ ⌜ b ⌝t ‘‘→'’’ ⌜ A ‘’ b ⌝T))

  qquote-term-under-app : ∀ {f} {t : Term {ε} (‘Σ’ ‘Context’ ‘Typ’)} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          (f ‘‘’’ ⌜ t ⌝t ‘‘→'’’ f ‘‘’’ (‘quote-sigma’ ‘'’ₐ t)))

  qquote-term-under-app-inv : ∀ {f} {t : Term {ε} (‘Σ’ ‘Context’ ‘Typ’)} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          (f ‘‘’’ (‘quote-sigma’ ‘'’ₐ t) ‘‘→'’’ f ‘‘’’ ⌜ t ⌝t))

  qbeta-nd-inv : ∀ {T A}
           {f : Term {ε ▻ A} (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c))}
           {x : Term {ε} A}
           {y : Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ T ⌝T)} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          ((((SW (f ‘t’ x))) ‘‘’’ y)
             ‘‘→'’’ ((‘λ'∙’ f ‘'’ₐ x) ‘‘’’ y)))

  qbeta-nd : ∀ {T A}
           {f : Term {ε ▻ A} (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c))}
           {x : Term {ε} A}
           {y : Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ T ⌝T)} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          (((‘λ'∙’ f ‘'’ₐ x) ‘‘’’ y)
             ‘‘→'’’ ((SW (f ‘t’ x)) ‘‘’’ y)))




postulate
  substTerm-distr-stuff : ∀ {B B' T}
           {f : Term {ε} (B ‘→’ B' ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c)))}
           {g : Term {ε} (‘Σ’ B B' ‘→'’ B)}
           {h : Term (W1 B' ‘’ (w→ g ‘'’ₐ ‘VAR₀’))}
           {x : Term {ε} (‘Σ’ B B')}
           {y : Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ T ⌝T)} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          (((SW
                 (SW1W
                    (S₁₀W2W
                       (S∀ (weakenTyp1-tProd
                              (w1 (SW1V (w∀ f ‘’ₐ ‘VAR₀’)))
                              ‘t’ (w→ g ‘'’ₐ ‘VAR₀’)) ‘’ₐ h)) ‘t’ x)) ‘‘’’ y)
             ‘‘→'’’ (((S₁₀WW
                           (S∀ (f ‘’ₐ (g ‘'’ₐ x)) ‘’ₐ β (S₀₀W1 (h ‘t’ x))))) ‘‘’’ y)))

  substTerm-undistr-stuff : ∀ {B B' T}
           {f : Term {ε} (B ‘→’ B' ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c)))}
           {g : Term {ε} (‘Σ’ B B' ‘→'’ B)}
           {h : Term (W1 B' ‘’ (w→ g ‘'’ₐ ‘VAR₀’))}
           {x : Term {ε} (‘Σ’ B B')}
           {y : Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ T ⌝T)} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          ((((S₁₀WW
                  (S∀ (f ‘’ₐ (g ‘'’ₐ x)) ‘’ₐ β (S₀₀W1 (h ‘t’ x))))) ‘‘’’ y)
             ‘‘→'’’
             ((SW
                   (SW1W
                      (S₁₀W2W
                         (S∀ (weakenTyp1-tProd
                                (w1 (SW1V (w∀ f ‘’ₐ ‘VAR₀’)))
                                ‘t’ (w→ g ‘'’ₐ ‘VAR₀’)) ‘’ₐ h)) ‘t’ x)) ‘‘’’ y)))

  qexistT-iota-inv : ∀
           {x : Term {ε} ‘Context’}
           {p : Term {ε} (‘Typ’ ‘’ x)}
           {f : Term
                  (‘Context’ ‘→’
                   ‘Typ’ ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c)))}
           {y : Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ ‘Σ’ ‘Context’ ‘Typ’ ⌝T)} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          (((S₁₀WW (S∀ (f ‘’ₐ x) ‘’ₐ p)) ‘‘’’ y)
             ‘‘→'’’
             ((S₁₀WW (S∀ (f ‘’ₐ (‘proj₁’ ‘'’ₐ ‘existT’ x p)) ‘’ₐ β (S₀₀W1 (‘proj₂’ ‘t’ ‘existT’ x p)))) ‘‘’’ y)))


  qexistT-iota : ∀
           {x : Term {ε} ‘Context’}
           {p : Term {ε} (‘Typ’ ‘’ x)}
           {f : Term
                  (‘Context’ ‘→’
                   ‘Typ’ ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c)))}
           {y : Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ ‘Σ’ ‘Context’ ‘Typ’ ⌝T)} →
      Term {ε} (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’
          (((S₁₀WW (S∀ (f ‘’ₐ (‘proj₁’ ‘'’ₐ ‘existT’ x p)) ‘’ₐ β (S₀₀W1 (‘proj₂’ ‘t’ ‘existT’ x p)))) ‘‘’’ y)
             ‘‘→'’’ ((S₁₀WW (S∀ (f ‘’ₐ x) ‘’ₐ p)) ‘‘’’ y)))

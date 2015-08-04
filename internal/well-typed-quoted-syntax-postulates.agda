{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax-postulates where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers
open import well-typed-syntax-context-helpers
open import well-typed-quoted-syntax-defs public

postulate
  ‘context-pick-if’-refl-inv : ∀ {A T dummy qqs} →
      □ (‘□’ ‘’
          ((⌜ T ⌝T ‘‘’’ ⌜ qqs ⌝t)
             ‘‘→'’’
             ((S₁₀WW (substTyp-tProd (‘context-pick-if'’ {ε} {ε ▻ A} ‘'’ₐ ⌜ dummy ⌝T ‘’ₐ ⌜ ε ▻ A ⌝c) ‘’ₐ ⌜ T ⌝T))
                ‘‘’’ ⌜ qqs ⌝t)))
  ‘context-pick-if’-refl : ∀ {A T dummy qqs} →
      □ (‘□’ ‘’
          ((S₁₀WW (substTyp-tProd (‘context-pick-if'’ {ε} {ε ▻ A} ‘'’ₐ ⌜ dummy ⌝T ‘’ₐ ⌜ ε ▻ A ⌝c) ‘’ₐ ⌜ T ⌝T)
              ‘‘’’ ⌜ qqs ⌝t)
             ‘‘→'’’
             (⌜ T ⌝T ‘‘’’ ⌜ qqs ⌝t)))



postulate

  qsubstTerm-substTerm-weakenTerm1-S₂₀₀W1WW : ∀ {T' C B}
         {b : Term {Γ = ε} (B ‘’ ‘ε’)}
         {c : Term {Γ = (ε ▻ T')} (W (C ‘’ ‘ε’))}
         {d : Term {Γ = (ε ▻ C ‘’ ‘ε’ ▻ W B ‘’₁ ‘ε’)} (W (W ‘Typ’) ‘’₂ ‘ε’)}
         {e : Term {Γ = ε} T'} →
    □ (‘□’ ‘’ (SW (S₂₀₀W1WW (w1 (d ‘t’ S₁W' (w b)) ‘t’ c) ‘t’ e))
        ‘→'’ ‘□’ ‘’ (S₂₁₀WW (d ‘t’₁ SW (c ‘t’ e) ‘t’ S₁₀W' b)))
-- qsubstTerm-substTerm-weakenTerm1-S₂₀₀W1WW = {!!}

  qsubstTerm-substTerm-weakenTerm1-S₂₀₀W1WW-inv : ∀ {T' C B}
         {b : Term {Γ = ε} (B ‘’ ‘ε’)}
         {c : Term {Γ = (ε ▻ T')} (W (C ‘’ ‘ε’))}
         {d : Term {Γ = (ε ▻ C ‘’ ‘ε’ ▻ W B ‘’₁ ‘ε’)} (W (W ‘Typ’) ‘’₂ ‘ε’)}
         {e : Term {Γ = ε} T'} →
    □ (‘□’ ‘’ (S₂₁₀WW (d ‘t’₁ SW (c ‘t’ e) ‘t’ S₁₀W' b))
        ‘→'’ ‘□’ ‘’ (SW (S₂₀₀W1WW (w1 (d ‘t’ S₁W' (w b)) ‘t’ c) ‘t’ e)))
-- qsubstTerm-substTerm-weakenTerm1-S₂₀₀W1WW-inv = {!!}

  ‘tApp-nd’ : ∀ {Γ} {A : □ (‘Typ’ ‘’ Γ)} {B : □ (‘Typ’ ‘’ Γ)} →
    □ (‘Term’ ‘’₁ Γ ‘’ (A ‘‘→'’’ B)
        ‘→'’ ‘Term’ ‘’₁ Γ ‘’ A
        ‘→'’ ‘Term’ ‘’₁ Γ ‘’ B)
-- ‘tApp-nd’ = {!!}

  quote-typ-undistr-tProd-nd : ∀ {H X} →
    □ (‘□’ ‘’ (⌜ H ⌝T ‘‘→'’’ ⌜ X ⌝T)
        ‘→'’ ‘□’ ‘’ ⌜ H ‘→'’ X ⌝T)
-- quote-typ-undistr-tProd-nd = {!!}

  quote-typ-distr-tProd-nd : ∀ {H X} →
    □ (‘□’ ‘’ ⌜ H ‘→'’ X ⌝T
        ‘→'’ ‘□’ ‘’ (⌜ H ⌝T ‘‘→'’’ ⌜ X ⌝T))
-- quote-typ-distr-tProd-nd = {!!}

  ‘‘fcomp-nd’’ : ∀ {A B C} →
    □ (‘□’ ‘’ (A ‘‘→'’’ C)
        ‘→'’ ‘□’ ‘’ (C ‘‘→'’’ B)
        ‘→'’ ‘□’ ‘’ (A ‘‘→'’’ B))
-- ‘‘fcomp-nd’’ = {!!}

  qsubstTerm-qtApp-nd-qtApp-nd-distr : ∀ {T B C}
         {a : Term {Γ = ε} (B ‘→'’ C ‘→'’ ‘Typ’ ‘’ ‘ε’)}
         {b : Term {Γ = ε} (T ‘→'’ B)}
         {c : Term {Γ = ε} (T ‘→'’ C)}
         {v : Term {Γ = ε} T} →
    (□ (‘□’
         ‘’ ((SW ((w→→ a ‘'’ₐ (w→ b ‘'’ₐ ‘VAR₀’) ‘'’ₐ (w→ c ‘'’ₐ ‘VAR₀’) ‘t’ v)))
               ‘‘→'’’ (a ‘'’ₐ (b ‘'’ₐ v) ‘'’ₐ (c ‘'’ₐ v)))))
-- qsubstTerm-qtApp-nd-qtApp-nd-distr = {!!}
  qsubstTerm-qtApp-nd-qtApp-nd-undistr : ∀ {T B C}
         {a : Term {Γ = ε} (B ‘→'’ C ‘→'’ ‘Typ’ ‘’ ‘ε’)}
         {b : Term {Γ = ε} (T ‘→'’ B)}
         {c : Term {Γ = ε} (T ‘→'’ C)}
         {v : Term {Γ = ε} T} →
    (□ (‘□’
         ‘’ ((a ‘'’ₐ (b ‘'’ₐ v) ‘'’ₐ (c ‘'’ₐ v))
               ‘‘→'’’ (SW ((w→→ a ‘'’ₐ (w→ b ‘'’ₐ ‘VAR₀’) ‘'’ₐ (w→ c ‘'’ₐ ‘VAR₀’) ‘t’ v))))))
-- qsubstTerm-qtApp-nd-qtApp-nd-undistr = {!!}

postulate

  quote-distr-substTyp : ∀ {B A} {b : □ B} →
      □ (‘□’ ‘’
          (⌜ A ‘’ b ⌝T ‘‘→'’’ ⌜ A ⌝T ‘‘’’ ⌜ b ⌝t))
  quote-undistr-substTyp : ∀ {B A} {b : □ B} →
      □ (‘□’ ‘’
          (⌜ A ⌝T ‘‘’’ ⌜ b ⌝t ‘‘→'’’ ⌜ A ‘’ b ⌝T))

  qquote-term-under-app-inv : ∀ {f} {t : □ (‘Σ’ ‘Context’ ‘Typ’)} →
      □ (‘□’ ‘’
          (f ‘‘’’ (‘quote-sigma’ ‘'’ₐ t) ‘‘→'’’ f ‘‘’’ ⌜ t ⌝t))

  qbeta-nd-inv : ∀ {T A}
           {f : Term {ε ▻ A} (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c))}
           {x : □ A}
           {y : □ (‘□’ ‘’ ⌜ T ⌝T)} →
      □ (‘□’ ‘’
          ((((SW (f ‘t’ x))) ‘‘’’ y)
             ‘‘→'’’ ((‘λ'∙’ f ‘'’ₐ x) ‘‘’’ y)))

  qbeta-nd : ∀ {T A}
           {f : Term {ε ▻ A} (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c))}
           {x : □ A}
           {y : □ (‘□’ ‘’ ⌜ T ⌝T)} →
      □ (‘□’ ‘’
          (((‘λ'∙’ f ‘'’ₐ x) ‘‘’’ y)
             ‘‘→'’’ ((SW (f ‘t’ x)) ‘‘’’ y)))




postulate
  substTerm-distr-stuff : ∀ {B B' T}
           {f : □ (B ‘→’ B' ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c)))}
           {g : □ (‘Σ’ B B' ‘→'’ B)}
           {h : Term (W1 B' ‘’ (w→ g ‘'’ₐ ‘VAR₀’))}
           {x : □ (‘Σ’ B B')}
           {y : □ (‘□’ ‘’ ⌜ T ⌝T)} →
      □ (‘□’ ‘’
          (((SW
                 (SW1W
                    (S₁₀W2W
                       (S∀ (weakenTyp1-tProd
                              (w1 (SW1V (w∀ f ‘’ₐ ‘VAR₀’)))
                              ‘t’ (w→ g ‘'’ₐ ‘VAR₀’)) ‘’ₐ h)) ‘t’ x)) ‘‘’’ y)
             ‘‘→'’’ (((S₁₀WW
                           (S∀ (f ‘’ₐ (g ‘'’ₐ x)) ‘’ₐ β (S₀₀W1 (h ‘t’ x))))) ‘‘’’ y)))

  substTerm-undistr-stuff : ∀ {B B' T}
           {f : □ (B ‘→’ B' ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c)))}
           {g : □ (‘Σ’ B B' ‘→'’ B)}
           {h : Term (W1 B' ‘’ (w→ g ‘'’ₐ ‘VAR₀’))}
           {x : □ (‘Σ’ B B')}
           {y : □ (‘□’ ‘’ ⌜ T ⌝T)} →
      □ (‘□’ ‘’
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
           {x : □ ‘Context’}
           {p : □ (‘Typ’ ‘’ x)}
           {f : Term
                  (‘Context’ ‘→’
                   ‘Typ’ ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c)))}
           {y : □ (‘□’ ‘’ ⌜ ‘Σ’ ‘Context’ ‘Typ’ ⌝T)} →
      □ (‘□’ ‘’
          (((S₁₀WW (S∀ (f ‘’ₐ x) ‘’ₐ p)) ‘‘’’ y)
             ‘‘→'’’
             ((S₁₀WW (S∀ (f ‘’ₐ (‘proj₁’ ‘'’ₐ ‘existT’ x p)) ‘’ₐ β (S₀₀W1 (‘proj₂’ ‘t’ ‘existT’ x p)))) ‘‘’’ y)))


  qexistT-iota : ∀
           {x : □ ‘Context’}
           {p : □ (‘Typ’ ‘’ x)}
           {f : Term
                  (‘Context’ ‘→’
                   ‘Typ’ ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c)))}
           {y : □ (‘□’ ‘’ ⌜ ‘Σ’ ‘Context’ ‘Typ’ ⌝T)} →
      □ (‘□’ ‘’
          (((S₁₀WW (S∀ (f ‘’ₐ (‘proj₁’ ‘'’ₐ ‘existT’ x p)) ‘’ₐ β (S₀₀W1 (‘proj₂’ ‘t’ ‘existT’ x p)))) ‘‘’’ y)
             ‘‘→'’’ ((S₁₀WW (S∀ (f ‘’ₐ x) ‘’ₐ p)) ‘‘’’ y)))

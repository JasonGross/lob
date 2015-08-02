{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax-postulates where
open import common
open import well-typed-syntax
open import well-typed-initial-context
open import well-typed-syntax-helpers
open import well-typed-syntax-context-helpers
open import well-typed-quoted-syntax-defs public

postulate
  ‘quote-sigma’ : □ (‘Σ’ ‘Context’ ‘Typ’ ‘→'’ ‘□’ ‘’ ⌜ ‘Σ’ ‘Context’ ‘Typ’ ⌝T)
-- ‘quote-sigma’ = {!!}

  ‘quote-term’ : ∀ {A} → □ (‘□’ ‘’ A ‘→'’ ‘□’ ‘’ ⌜ ‘□’ ‘’ A ⌝T)
-- ‘quote-term’ = {!!}

  ‘context-pick-if’ : ∀ {P : Typ (ε ▻ ‘Context’)}
           (dummy : Term (P ‘’ ⌜ (ε ▻ ‘Σ’ ‘Context’ ‘Typ’) ⌝c)) →
      □ (‘Context’ ‘→’ P ‘→'’ W (P ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c))

postulate
  Wquote-distr-qcontext-extend : ∀ {Γ T T'}
      → Term {ε ▻ T'} (W (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝c))
      → Term {ε ▻ T'} (W (‘Typ’ ‘’ (⌜ Γ ⌝c ‘▻’ ⌜ T ⌝T)))
  Wquote-undistr-qcontext-extend : ∀ {Γ T T'}
      → Term {ε ▻ T'} (W (‘Typ’ ‘’ (⌜ Γ ⌝c ‘▻’ ⌜ T ⌝T)))
      → Term {ε ▻ T'} (W (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝c))

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

  quote-typ-distr-tProd-nd : ∀ {H X} →
    □ (‘□’ ‘’ ⌜ H ‘→'’ X ⌝T
        ‘→'’ ‘□’ ‘’ (⌜ H ⌝T ‘‘→'’’ ⌜ X ⌝T))
-- quote-typ-distr-tProd-nd = {!!}


⌜W‘▻’⌝ = Wquote-distr-qcontext-extend
⌜W‘◅’⌝ = Wquote-undistr-qcontext-extend

quote-distr-qcontext-extend : ∀ {Γ T}
      → □ (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝c)
      → □ (‘Typ’ ‘’ (⌜ Γ ⌝c ‘▻’ ⌜ T ⌝T))
quote-distr-qcontext-extend x = SW (Wquote-distr-qcontext-extend (w x) ‘t’ ‘ε’)

quote-undistr-qcontext-extend : ∀ {Γ T}
      → □ (‘Typ’ ‘’ (⌜ Γ ⌝c ‘▻’ ⌜ T ⌝T))
      → □ (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝c)
quote-undistr-qcontext-extend x = SW (Wquote-undistr-qcontext-extend (w x) ‘t’ ‘ε’)

⌜‘▻’⌝ = quote-distr-qcontext-extend
⌜‘◅’⌝ = quote-undistr-qcontext-extend

postulate

  quote-distr-substTyp : ∀ {B A} {b : □ B} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (⌜ A ‘’ b ⌝T ‘‘→'’’ ⌜‘▻’⌝ ⌜ A ⌝T ‘‘’’ ⌜ b ⌝t))
  quote-undistr-substTyp : ∀ {B A} {b : □ B} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (⌜‘▻’⌝ ⌜ A ⌝T ‘‘’’ ⌜ b ⌝t ‘‘→'’’ ⌜ A ‘’ b ⌝T))

  ‘context-pick-if’-refl-inv : ∀ {T dummy qqs} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜‘▻’⌝ ⌜ T ⌝T ‘‘’’ qqs)
             ‘‘→'’’
             (⌜‘▻’⌝ (S₁₀WW (substTyp-tProd (‘context-pick-if’ {‘Typ’} dummy ‘’ₐ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c) ‘’ₐ ⌜ T ⌝T))
                ‘‘’’ qqs)))
  ‘context-pick-if’-refl : ∀ {T dummy qqs} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜‘▻’⌝ (S₁₀WW (substTyp-tProd (‘context-pick-if’ {‘Typ’} dummy ‘’ₐ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c) ‘’ₐ ⌜ T ⌝T))
              ‘‘’’ qqs)
             ‘‘→'’’
             (⌜‘▻’⌝ ⌜ T ⌝T ‘‘’’ qqs)))

  qquote-term-under-app : ∀ {f} {t : □ (‘Σ’ ‘Context’ ‘Typ’)} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (f ‘‘’’ ⌜ t ⌝t ‘‘→'’’ f ‘‘’’ (‘quote-sigma’ ‘'’ₐ t)))

  qquote-term-under-app-inv : ∀ {f} {t : □ (‘Σ’ ‘Context’ ‘Typ’)} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (f ‘‘’’ (‘quote-sigma’ ‘'’ₐ t) ‘‘→'’’ f ‘‘’’ ⌜ t ⌝t))

  qbeta-nd-inv : ∀ {T A}
           {f : Term {ε ▻ A} (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c))}
           {x : □ A}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝T)} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (((⌜‘▻’⌝ (SW (f ‘t’ x))) ‘‘’’ y)
             ‘‘→'’’ ((‘λ'∙’ (⌜W‘▻’⌝ f) ‘'’ₐ x) ‘‘’’ y)))

  qbeta-nd : ∀ {T A}
           {f : Term {ε ▻ A} (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c))}
           {x : □ A}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝T)} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (((‘λ'∙’ (⌜W‘▻’⌝ f) ‘'’ₐ x) ‘‘’’ y)
             ‘‘→'’’ ((⌜‘▻’⌝ (SW (f ‘t’ x))) ‘‘’’ y)))




postulate
  substTerm-distr-stuff : ∀ {B B' T}
           {f : □ (B ‘→’ B' ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c)))}
           {g : □ (‘Σ’ B B' ‘→'’ B)}
           {h : Term (W1 B' ‘’ (w→ g ‘'’ₐ ‘VAR₀’))}
           {x : □ (‘Σ’ B B')}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝T)} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜‘▻’⌝
              (SW
                 (SW1W
                    (S₁₀W2W
                       (S∀ (weakenTyp1-tProd
                              (w1 (SW1V (w∀ f ‘’ₐ ‘VAR₀’)))
                              ‘t’ (w→ g ‘'’ₐ ‘VAR₀’)) ‘’ₐ h)) ‘t’ x)) ‘‘’’ y)
             ‘‘→'’’ ((⌜‘▻’⌝
                        (S₁₀WW
                           (S∀ (f ‘’ₐ (g ‘'’ₐ x)) ‘’ₐ β (S₀₀W1 (h ‘t’ x))))) ‘‘’’ y)))

  substTerm-undistr-stuff : ∀ {B B' T}
           {f : □ (B ‘→’ B' ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝c)))}
           {g : □ (‘Σ’ B B' ‘→'’ B)}
           {h : Term (W1 B' ‘’ (w→ g ‘'’ₐ ‘VAR₀’))}
           {x : □ (‘Σ’ B B')}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝T)} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (((⌜‘▻’⌝
               (S₁₀WW
                  (S∀ (f ‘’ₐ (g ‘'’ₐ x)) ‘’ₐ β (S₀₀W1 (h ‘t’ x))))) ‘‘’’ y)
             ‘‘→'’’
             (⌜‘▻’⌝
                (SW
                   (SW1W
                      (S₁₀W2W
                         (S∀ (weakenTyp1-tProd
                                (w1 (SW1V (w∀ f ‘’ₐ ‘VAR₀’)))
                                ‘t’ (w→ g ‘'’ₐ ‘VAR₀’)) ‘’ₐ h)) ‘t’ x)) ‘‘’’ y)))

  qexistT-iota-inv : ∀ {T A P}
           {x : □ A}
           {p : □ (P ‘’ x)}
           {f}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝T)} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜‘▻’⌝ (S₁₀WW (S∀ (f ‘’ₐ x) ‘’ₐ p)) ‘‘’’ y)
             ‘‘→'’’
             (⌜‘▻’⌝ (S₁₀WW (S∀ (f ‘’ₐ (‘proj₁’ ‘'’ₐ ‘existT’ x p)) ‘’ₐ β (S₀₀W1 (‘proj₂’ ‘t’ ‘existT’ x p)))) ‘‘’’ y)))


  qexistT-iota : ∀ {T A P}
           {x : □ A}
           {p : □ (P ‘’ x)}
           {f}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝T)} →
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜‘▻’⌝ (S₁₀WW (S∀ (f ‘’ₐ (‘proj₁’ ‘'’ₐ ‘existT’ x p)) ‘’ₐ β (S₀₀W1 (‘proj₂’ ‘t’ ‘existT’ x p)))) ‘‘’’ y)
             ‘‘→'’’ (⌜‘▻’⌝ (S₁₀WW (S∀ (f ‘’ₐ x) ‘’ₐ p)) ‘‘’’ y)))

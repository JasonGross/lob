{-# OPTIONS --without-K #-}
module lob where
open import common
open import well-typed-syntax
open import well-typed-quoted-syntax
open import well-typed-syntax-interpreter-full

module inner (‘X’ : Typ ε) (‘f’ : Term {Γ = ε ▻ (‘□’ ‘’ ⌜ ‘X’ ⌝T)} (W ‘X’)) where
  X : Set _
  X = Typε⇓ ‘X’

  f'' : (x : Typε⇓ (‘□’ ‘’ ⌜ ‘X’ ⌝T)) → Typε▻⇓ {‘□’ ‘’ ⌜ ‘X’ ⌝T} (W ‘X’) x
  f'' = Termε▻⇓ ‘f’

  {-f : □ ‘X’ → X
  f □‘X’ = un▻-Typε▻⇓ (Termε▻⇓ ‘f’ helper)
    where helper : {!.well-typed-syntax-interpreter.Typ⇓
                     (transfer-Typ (‘□’ ‘’ ⌜ ‘X’ ⌝T))
                     .well-typed-syntax-interpreter-full.Contextε⇓!}
          helper = {!!}-}

  dummy : Typ ε
  dummy = ‘Context’

  cast : (Γv : Σ Typ) → Typ (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
  cast (Γ , v) = context-pick-if {P = Typ} {Γ} (W dummy) v

  Hf : (h : Σ Typ) → Typ ε
  Hf h = (cast h ‘’ quote-sigma h ‘→'’ ‘X’)

  qh : Term {Γ = (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)} (W (‘Typ’ ‘’ ‘ε’))
  qh = f' w‘‘’’ x
    where
      f' : Term (W (‘Typ’ ‘’ ⌜ ε ▻ ‘Σ’ ‘Context’ ‘Typ’ ⌝c))
      f' = w→ ‘cast’ ‘'’ₐ ‘VAR₀’

      x : Term (W (‘Term’ ‘’₁ ⌜ ε ⌝c ‘’ ⌜ ‘Σ’ ‘Context’ ‘Typ’ ⌝T))
      x = (w→ ‘quote-sigma’ ‘'’ₐ ‘VAR₀’)

  h2 : Typ (ε ▻ ‘Σ’ ‘Context’ ‘Typ’)
  h2 = (W1 ‘□’ ‘’ S₂₀₀W1WW (w1 (‘tProd-nd’ ‘t’₂ ‘ε’ ‘t’ S₁W' (w ⌜ ‘X’ ⌝T)) ‘t’ qh))

  h : Σ Typ
  h = ((ε ▻ ‘Σ’ ‘Context’ ‘Typ’) , h2)

  H0 : Typ ε
  H0 = Hf h

  H : Set
  H = Term {Γ = ε} H0

  ‘H0’ : □ (‘Typ’ ‘’ ⌜ ε ⌝c)
  ‘H0’ = ⌜ H0 ⌝T

  ‘H’ : Typ ε
  ‘H’ = ‘□’ ‘’ ‘H0’

  H0' : Typ ε
  H0' = ‘H’ ‘→'’ ‘X’

  H' : Set
  H' = Term {Γ = ε} H0'

  ‘H0'’ : □ (‘Typ’ ‘’ ⌜ ε ⌝c)
  ‘H0'’ = ⌜ H0' ⌝T

  ‘H'’ : Typ ε
  ‘H'’ = ‘□’ ‘’ ‘H0'’

  toH-helper-helper : ∀ {k} → h2 ≡ k
    → □ (h2 ‘’ quote-sigma h ‘→'’ ‘□’ ‘’ ⌜ h2 ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T)
    → □ (k ‘’ quote-sigma h ‘→'’ ‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T)
  toH-helper-helper p x = transport (λ k → □ (k ‘’ quote-sigma h ‘→'’ ‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T)) p x

  toH-helper : □ (cast h ‘’ quote-sigma h ‘→'’ ‘H’)
  toH-helper = toH-helper-helper
    {k = context-pick-if {P = Typ} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} (W dummy) h2}
    (sym (context-pick-if-refl {P = Typ} {W dummy} {h2}))
    (S₀₀W1'→ ((‘ssw1’ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (‘s←←’ ‘‘∘’’ ‘cast-refl’ ‘‘∘’’ ⌜→'⌝ ‘'’ₐ ⌜ ‘λ∙’ ‘VAR₀’ ⌝t)) ‘∘’ ⌜←'⌝))

  ‘toH’ : □ (‘H'’ ‘→'’ ‘H’)
  ‘toH’ = ⌜→'⌝ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ toH-helper ⌝t) ‘∘’ ⌜←'⌝

  toH : H' → H
  toH h' = toH-helper ‘∘’ h'

  fromH-helper-helper : ∀ {k} → h2 ≡ k
    → □ (‘□’ ‘’ ⌜ h2 ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T ‘→'’ h2 ‘’ quote-sigma h)
    → □ (‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T ‘→'’ k ‘’ quote-sigma h)
  fromH-helper-helper p x = transport (λ k → □ (‘□’ ‘’ ⌜ k ‘’ quote-sigma h ‘→'’ ‘X’ ⌝T ‘→'’ k ‘’ quote-sigma h)) p x

  fromH-helper : □ (‘H’ ‘→'’ cast h ‘’ quote-sigma h)
  fromH-helper = fromH-helper-helper {k = context-pick-if {P = Typ} {ε ▻ ‘Σ’ ‘Context’ ‘Typ’} (W dummy) h2}
                                     (sym (context-pick-if-refl {P = Typ} {W dummy} {h2}))
                                     (S₀₀W1'← (⌜→'⌝ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ
                                                          (⌜→'⌝ ‘'’ₐ ⌜ ‘λ∙’ ‘VAR₀’ ⌝t ‘‘∘’’ ‘cast-refl'’ ‘‘∘’’ ‘s→→’) ‘∘’ ‘ssw1'’))
  {--}
  ‘fromH’ : □ (‘H’ ‘→'’ ‘H'’)
  ‘fromH’ = ⌜→'⌝ ‘∘’ ‘‘fcomp-nd’’ ‘'’ₐ (⌜→'⌝ ‘'’ₐ ⌜ fromH-helper ⌝t) ‘∘’ ⌜←'⌝

  fromH : H → H'
  fromH h' = fromH-helper ‘∘’ h'

  lob : □ ‘X’
  lob = fromH h' ‘'’ₐ ⌜ h' ⌝t
    where
      f' : Term {ε ▻ ‘□’ ‘’ ‘H0’} (W (‘□’ ‘’ (⌜ ‘□’ ‘’ ‘H0’ ⌝T ‘‘→'’’ ⌜ ‘X’ ⌝T)))
      f' = Conv0 {‘H0’} {‘X’} (SW1W (w∀ ‘fromH’ ‘’ₐ ‘VAR₀’))

      x : Term {ε ▻ ‘□’ ‘’ ‘H0’} (W (‘□’ ‘’ ⌜ ‘H’ ⌝T))
      x = w→ ‘quote-term’ ‘'’ₐ ‘VAR₀’

      h' : H
      h' = toH (‘λ∙’ (w→ (‘λ∙’ ‘f’) ‘'’ₐ (w→→ ‘tApp-nd’ ‘'’ₐ f' ‘'’ₐ x)))

lob : {‘X’ : Typ ε} → □ ((‘□’ ‘’ ⌜ ‘X’ ⌝T) ‘→'’ ‘X’) → □ ‘X’
lob {‘X’} ‘f’ = inner.lob ‘X’ (un‘λ∙’ ‘f’)

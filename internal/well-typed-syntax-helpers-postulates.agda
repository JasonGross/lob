module well-typed-syntax-helpers-postulates where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers

postulate
  SWW1W1W1w∀→₂ : ∀ {Γ A B C D E f x} -- ewwww
    → Term {Γ ▻ A ▻ W B ▻ W1 C ▻ D} (W (W1 (W1 (W1 f)) ‘’ un‘λ'∙’ (un‘λ∙’ (w∀→₂ x))))
    → Term {Γ ▻ A ▻ W B ▻ W1 C ▻ D} (W (W2 (W1 (W1 {Γ} {B} {E} f) ‘’ un‘λ'∙’ (un‘λ∙’ x))))

weakenTyp-tProd-tProd-tProd-substTyp-tProd-nd-weakenTyp : ∀ {Γ X Y A B f x C}
  → Term {Γ ▻ X} (W (A ‘→’ B ‘→’ W1 (W1 {Γ} {A} {Y} f) ‘’ un‘λ'∙’ (un‘λ∙’ x) ‘→'’ W C))
  → Term {Γ ▻ X} (W A ‘→’ W1 B ‘→’ W1 (W1 (W1 f)) ‘’ un‘λ'∙’ (un‘λ∙’ (w∀→₂ x)) ‘→'’ W (W1 C))
weakenTyp-tProd-tProd-tProd-substTyp-tProd-nd-weakenTyp t
  = ‘λ∙’
      (‘λ∙’
       (‘λ'∙’
        (WW2W
         (SW
          (w→
           (weakenTyp2-tProd-nd
            (SW1V
             (w∀ (weakenTyp1-tProd (SW1V (w∀ (weakenTyp-tProd t) ‘’ₐ ‘VAR₀’)))
              ‘’ₐ ‘VAR₀’)))
           ‘’ₐ SWW1W1W1w∀→₂ ‘VAR₀’)))))

weaken-tProd-tProd-tProd-substTyp-tProd-nd-weakenTyp : ∀ {Γ X Y A B f x C}
  → Term {Γ} (A ‘→’ B ‘→’ W1 (W1 {Γ} {A} {Y} f) ‘’ un‘λ'∙’ (un‘λ∙’ x) ‘→'’ W C)
  → Term {Γ ▻ X} (W A ‘→’ W1 B ‘→’ W1 (W1 (W1 f)) ‘’ un‘λ'∙’ (un‘λ∙’ (w∀→₂ x)) ‘→'’ W (W1 C))
weaken-tProd-tProd-tProd-substTyp-tProd-nd-weakenTyp t = weakenTyp-tProd-tProd-tProd-substTyp-tProd-nd-weakenTyp (w t)

w∀∀‘’→ = weaken-tProd-tProd-tProd-substTyp-tProd-nd-weakenTyp

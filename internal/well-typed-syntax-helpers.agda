{-# OPTIONS --without-K #-}
module well-typed-syntax-helpers where
open import common
open import well-typed-syntax

infixl 3 _‘'’ₐ_
infixr 1 _‘→'’_
infixl 3 _‘t’_
infixl 3 _‘t’₁_
infixl 3 _‘t’₂_
infixr 2 _‘∘’_

WS∀ : ∀ {Γ T T' A B} {a : Term {Γ = Γ} T} → Term {Γ = Γ ▻ T'} (W ((A ‘→’ B) ‘’ a)) → Term {Γ ▻ T'} (W ((A ‘’ a) ‘→’ (B ‘’₁ a)))
WS∀ = weakenTyp-substTyp-tProd

_‘→'’_ : ∀ {Γ} → Typ Γ → Typ Γ → Typ Γ
_‘→'’_ {Γ = Γ} A B = _‘→’_ {Γ = Γ} A (W {Γ = Γ} {A = A} B)

_‘'’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→'’ B) → Term A → Term B
_‘'’ₐ_ {Γ} {A} {B} f x = SW (_‘’ₐ_ {Γ} {A} {W B} f x)

_‘t’_ : ∀ {Γ A} {B : Typ (Γ ▻ A)} → (b : Term {Γ = Γ ▻ A} B) → (a : Term {Γ} A) → Term {Γ} (B ‘’ a)
b ‘t’ a = ‘λ∙’ b ‘’ₐ a

substTyp-tProd : ∀ {Γ T A B} {a : Term {Γ} T} →
                         Term {Γ} ((A ‘→’ B) ‘’ a)
                         → Term {Γ} (_‘→’_ {Γ = Γ} (A ‘’ a) (B ‘’₁ a))
substTyp-tProd {Γ} {T} {A} {B} {a} x = SW ((WS∀ (w x)) ‘t’ a)

S∀ = substTyp-tProd

‘λ'∙’ : ∀ {Γ A B} → Term {Γ ▻ A} (W B) -> Term (A ‘→'’ B)
‘λ'∙’ f = ‘λ∙’ f

SW1V : ∀ {Γ A T} → Term {Γ ▻ A} (W1 T ‘’ ‘VAR₀’) → Term {Γ ▻ A} T
SW1V = substTyp-weakenTyp1-VAR₀

S₁∀ : ∀ {Γ T T' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a} ((A ‘→’ B) ‘’₁ a) → Term {Γ ▻ T' ‘’ a} ((A ‘’₁ a) ‘→’ (B ‘’₂ a))
S₁∀ = substTyp1-tProd

un‘λ∙’ : ∀ {Γ A B} → Term (A ‘→’ B) → Term {Γ ▻ A} B
un‘λ∙’ f = SW1V (weakenTyp-tProd (w f) ‘’ₐ ‘VAR₀’)

weakenProd : ∀ {Γ A B C} →
                          Term {Γ} (A ‘→’ B)
                          → Term {Γ = Γ ▻ C} (W A ‘→’ W1 B)
weakenProd {Γ} {A} {B} {C} x = weakenTyp-tProd (w x)
w∀ = weakenProd

w1 : ∀ {Γ A B C} → Term {Γ = Γ ▻ B} C → Term {Γ = Γ ▻ A ▻ W {Γ = Γ} {A = A} B} (W1 {Γ = Γ} {A = A} {B = B} C)
w1 x = un‘λ∙’ (weakenTyp-tProd (w (‘λ∙’ x)))

_‘t’₁_ : ∀ {Γ A B C} → (c : Term {Γ = Γ ▻ A ▻ B} C) → (a : Term {Γ} A) → Term {Γ = Γ ▻ B ‘’ a} (C ‘’₁ a)
f ‘t’₁ x = un‘λ∙’ (S∀ (‘λ∙’ (‘λ∙’ f) ‘’ₐ x))
_‘t’₂_ : ∀ {Γ A B C D} → (c : Term {Γ = Γ ▻ A ▻ B ▻ C} D) → (a : Term {Γ} A) → Term {Γ = Γ ▻ B ‘’ a ▻ C ‘’₁ a} (D ‘’₂ a)
f ‘t’₂ x = un‘λ∙’ (S₁∀ (un‘λ∙’ (S∀ (‘λ∙’ (‘λ∙’ (‘λ∙’ f)) ‘’ₐ x))))

S₁₀W' : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (A ‘’ a) → Term {Γ} (W A ‘’₁ a ‘’ b)
S₁₀W' = substTyp1-substTyp-weakenTyp-inv

S₁₀W : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (W A ‘’₁ a ‘’ b) → Term {Γ} (A ‘’ a)
S₁₀W = substTyp1-substTyp-weakenTyp

substTyp1-substTyp-weakenTyp-weakenTyp : ∀ {Γ T A} {B : Typ (Γ ▻ A)}
    → {a : Term {Γ} A}
    → {b : Term {Γ} (B ‘’ a)}
    → Term {Γ} (W (W T) ‘’₁ a ‘’ b)
    → Term {Γ} T
substTyp1-substTyp-weakenTyp-weakenTyp x = SW (S₁₀W x)

S₁₀WW = substTyp1-substTyp-weakenTyp-weakenTyp


S₂₁₀W : ∀ {Γ A B C T} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
      → Term {Γ} (W T ‘’₂ a ‘’₁ b ‘’ c)
      → Term {Γ} (T ‘’₁ a ‘’ b)
S₂₁₀W = substTyp2-substTyp1-substTyp-weakenTyp

substTyp2-substTyp1-substTyp-weakenTyp-weakenTyp : ∀ {Γ A B C T}
         {a : Term {Γ} A}
         {b : Term {Γ} (B ‘’ a)}
         {c : Term {Γ} (C ‘’₁ a ‘’ b)} →
    Term {Γ} (W (W T) ‘’₂ a ‘’₁ b ‘’ c)
    → Term {Γ} (T ‘’ a)
substTyp2-substTyp1-substTyp-weakenTyp-weakenTyp x = S₁₀W (S₂₁₀W x)

S₂₁₀WW = substTyp2-substTyp1-substTyp-weakenTyp-weakenTyp

W1W : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W1 (W C)) → Term {Γ ▻ A ▻ W B} (W (W C))
W1W = weakenTyp1-weakenTyp

W1W1W : ∀ {Γ A B C T} → Term {Γ ▻ A ▻ B ▻ W (W C)} (W1 (W1 (W T))) → Term {Γ ▻ A ▻ B ▻ W (W C)} (W1 (W (W T)))
W1W1W = weakenTyp1-weakenTyp1-weakenTyp

weakenTyp-tProd-nd : ∀ {Γ A B C} →
                          Term {Γ = Γ ▻ C} (W (A ‘→'’ B))
                          → Term {Γ = Γ ▻ C} (W A ‘→'’ W B)
weakenTyp-tProd-nd x = ‘λ'∙’ (W1W (SW1V (weakenTyp-tProd (w (weakenTyp-tProd x)) ‘’ₐ ‘VAR₀’)))

weakenProd-nd : ∀ {Γ A B C} →
                             Term (A ‘→'’ B)
                             → Term {Γ = Γ ▻ C} (W A ‘→'’ W B)
weakenProd-nd {Γ} {A} {B} {C} x = weakenTyp-tProd-nd (w x)
w→ = weakenProd-nd




weakenTyp-tProd-nd-tProd-nd : ∀ {Γ A B C D} →
    Term {Γ = Γ ▻ D} (W (A ‘→'’ B ‘→'’ C))
    → Term {Γ = Γ ▻ D} (W A ‘→'’ W B ‘→'’ W C)
weakenTyp-tProd-nd-tProd-nd x = ‘λ∙’ (weakenTyp-tProd-inv (‘λ∙’ (W1W1W (SW1V (w∀ (weakenTyp-tProd (weakenTyp-weakenTyp-tProd (w→ (weakenTyp-tProd-nd x) ‘'’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’)))))

weakenProd-nd-Prod-nd : ∀ {Γ A B C D} →
    Term (A ‘→'’ B ‘→'’ C)
    → Term {Γ = Γ ▻ D} (W A ‘→'’ W B ‘→'’ W C)
weakenProd-nd-Prod-nd {Γ} {A} {B} {C} {D} x = weakenTyp-tProd-nd-tProd-nd (w x)
w→→ = weakenProd-nd-Prod-nd

S₁W1 : ∀ {Γ A B C} {a : Term {Γ} A} → Term {Γ ▻ W B ‘’ a} (W1 C ‘’₁ a) → Term {Γ ▻ B} C
S₁W1 = substTyp1-weakenTyp1


W1S₁W' : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W (T ‘’ a)))
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W T ‘’₁ a))
W1S₁W' = weakenTyp1-substTyp-weakenTyp1-inv


substTyp-weakenTyp1-inv : ∀ {Γ A T' T}
         {a : Term {Γ} A} →
    Term {Γ = (Γ ▻ T' ‘’ a)} (W (T ‘’ a))
    → Term {Γ = (Γ ▻ T' ‘’ a)} (W T ‘’₁ a)
substTyp-weakenTyp1-inv {a = a} x = S₁W1 (W1S₁W' (w1 x) ‘t’₁ a)

S₁W' = substTyp-weakenTyp1-inv

_‘∘’_ : ∀ {Γ A B C}
    → Term {Γ} (A ‘→'’ B)
    → Term {Γ} (B ‘→'’ C)
    → Term {Γ} (A ‘→'’ C)
g ‘∘’ f = ‘λ∙’ (w→ f ‘'’ₐ (w→ g ‘'’ₐ ‘VAR₀’))


WS₀₀W1 : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
      → Term {Γ ▻ T'} (W (T ‘’ (SW (a ‘t’ b))))
WS₀₀W1 = weakenTyp-substTyp-substTyp-weakenTyp1

WS₀₀W1' : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (T ‘’ (SW (a ‘t’ b))))
      → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
WS₀₀W1' = weakenTyp-substTyp-substTyp-weakenTyp1-inv

substTyp-substTyp-weakenTyp1-inv-arr : ∀ {Γ B A}
         {b : Term {Γ} B}
         {a : Term {Γ ▻ B} (W A)}
         {T : Typ (Γ ▻ A)}
         {X} →
    Term {Γ} (T ‘’ (SW (a ‘t’ b)) ‘→'’ X)
    → Term {Γ} (W1 T ‘’ a ‘’ b ‘→'’ X)
substTyp-substTyp-weakenTyp1-inv-arr x = ‘λ∙’ (w→ x ‘'’ₐ WS₀₀W1 ‘VAR₀’)

S₀₀W1'→ = substTyp-substTyp-weakenTyp1-inv-arr

substTyp-substTyp-weakenTyp1-arr-inv : ∀ {Γ B A}
         {b : Term {Γ} B}
         {a : Term {Γ ▻ B} (W A)}
         {T : Typ (Γ ▻ A)}
         {X} →
    Term {Γ} (X ‘→'’ T ‘’ (SW (a ‘t’ b)))
    → Term {Γ} (X ‘→'’ W1 T ‘’ a ‘’ b)
substTyp-substTyp-weakenTyp1-arr-inv x = ‘λ∙’ (WS₀₀W1' (un‘λ∙’ x))

S₀₀W1'← = substTyp-substTyp-weakenTyp1-arr-inv


substTyp-substTyp-weakenTyp1 : ∀ {Γ B A}
         {b : Term {Γ} B}
         {a : Term {Γ ▻ B} (W A)}
         {T : Typ (Γ ▻ A)} →
    Term {Γ} (W1 T ‘’ a ‘’ b)
    → Term {Γ} (T ‘’ (SW (a ‘t’ b)))
substTyp-substTyp-weakenTyp1 x = (SW (WS₀₀W1 (w x) ‘t’ x))
S₀₀W1 = substTyp-substTyp-weakenTyp1

SW1W : ∀ {Γ T} {A : Typ Γ} {B : Typ Γ}
      → {a : Term {Γ = Γ ▻ T} (W {Γ = Γ} {A = T} B)}
      → Term {Γ = Γ ▻ T} (W1 (W A) ‘’ a)
      → Term {Γ = Γ ▻ T} (W A)
SW1W = substTyp-weakenTyp1-weakenTyp


S₂₀₀W1WW : ∀ {Γ A} {T : Typ (Γ ▻ A)} {T' C B} {a : Term {Γ} A} {b : Term {Γ = (Γ ▻ C ‘’ a)} (B ‘’₁ a)}
         {c : Term {Γ = (Γ ▻ T')} (W (C ‘’ a))}
         → Term {Γ = (Γ ▻ T')} (W1 (W (W T) ‘’₂ a ‘’ b) ‘’ c)
         → Term {Γ = (Γ ▻ T')} (W (T ‘’ a))
S₂₀₀W1WW = substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp


S₁₀W2W : ∀ {Γ T' A B T} {a : Term {Γ ▻ T'} (W A)} {b : Term {Γ ▻ T'} (W1 B ‘’ a)}
      → Term {Γ ▻ T'} (W2 (W T) ‘’₁ a ‘’ b)
      → Term {Γ ▻ T'} (W1 T ‘’ a)
S₁₀W2W = substTyp1-substTyp-weakenTyp2-weakenTyp

β : ∀ {Γ A B B'}
  {g : Term {Γ} (A ‘→'’ B)}
  {x : Term {Γ} A}
  → Term {Γ} (B' ‘’ SW (w→ g ‘'’ₐ ‘VAR₀’ ‘t’ x))
  → Term {Γ} (B' ‘’ (g ‘'’ₐ x))
β = beta-under-subst

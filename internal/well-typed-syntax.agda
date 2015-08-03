{-# OPTIONS --without-K #-}
module well-typed-syntax where

infixl 2 _▻_
infixl 3 _‘’_
infixl 3 _‘’₁_
infixl 3 _‘’₂_
infixl 3 _‘’₃_
infixl 3 _‘’ₐ_
infixr 1 _‘→’_

mutual
  data Context : Set where
    ε₀ : Context
    _▻_ : (Γ : Context) → Typ Γ → Context

  data Typ : Context → Set where
    _‘’_ : ∀ {Γ A} → Typ (Γ ▻ A) → Term {Γ} A → Typ Γ
    _‘’₁_ : ∀ {Γ A B} → (C : Typ (Γ ▻ A ▻ B)) → (a : Term {Γ} A) → Typ (Γ ▻ B ‘’ a)
    _‘’₂_ : ∀ {Γ A B C} → (D : Typ (Γ ▻ A ▻ B ▻ C)) → (a : Term {Γ} A) → Typ (Γ ▻ B ‘’ a ▻ C ‘’₁ a)
    _‘’₃_ : ∀ {Γ A B C D} → (E : Typ (Γ ▻ A ▻ B ▻ C ▻ D)) → (a : Term {Γ} A) → Typ (Γ ▻ B ‘’ a ▻ C ‘’₁ a ▻ D ‘’₂ a)
    W : ∀ {Γ A} → Typ Γ → Typ (Γ ▻ A)
    W1 : ∀ {Γ A B} → Typ (Γ ▻ B) → Typ (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B))
    W2 : ∀ {Γ A B C} → Typ (Γ ▻ B ▻ C) → Typ (Γ ▻ A ▻ W B ▻ W1 C)
    _‘→’_ : ∀ {Γ} (A : Typ Γ) → Typ (Γ ▻ A) → Typ Γ
    ‘Set’ : ∀ {Γ} → Typ Γ
    El : ∀ {Γ} → Term {Γ} ‘Set’ → Typ Γ
    ‘Σ'’ : ∀ {Γ} (T : Typ Γ) → Typ (Γ ▻ T) → Typ Γ
    ‘Context’ : ∀ {Γ} → Typ Γ
    ‘Typ’ : ∀ {Γ} → Typ (Γ ▻ ‘Context’)
    ‘Term’ : ∀ {Γ} → Typ (Γ ▻ ‘Context’ ▻ ‘Typ’)


  data Term : ∀ {Γ} → Typ Γ → Set where
    w : ∀ {Γ A B} → Term {Γ} B → Term {Γ = Γ ▻ A} (W {Γ = Γ} {A = A} B)
    ‘λ∙’ : ∀ {Γ A B} → Term {Γ = (Γ ▻ A)} B → Term {Γ} (A ‘→’ B)
    _‘’ₐ_ : ∀ {Γ A B} → (f : Term {Γ} (A ‘→’ B)) → (x : Term {Γ} A) → Term {Γ} (B ‘’ x)
    ‘VAR₀’ : ∀ {Γ T} → Term {Γ = Γ ▻ T} (W T)
    ⌜_⌝c : ∀ {Γ} → Context → Term {Γ} ‘Context’
    ⌜_⌝T : ∀ {Γ Γ'} → Typ Γ' → Term {Γ} (‘Typ’ ‘’ ⌜ Γ' ⌝c)
    ⌜_⌝t : ∀ {Γ Γ'} {T : Typ Γ'} → Term T → Term {Γ} (‘Term’ ‘’₁ ⌜ Γ' ⌝c ‘’ ⌜ T ⌝T)
    ‘quote-term’ : ∀ {Γ Γ'} {A : Typ Γ'} → Term {Γ} (‘Term’ ‘’₁ ⌜ Γ' ⌝c ‘’ ⌜ A ⌝T ‘→’ W (‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ ‘Term’ ‘’₁ ⌜ Γ' ⌝c ‘’ ⌜ A ⌝T ⌝T))
    ‘quote-sigma’ : ∀ {Γ Γ'} → Term {Γ} (‘Σ'’ ‘Context’ ‘Typ’ ‘→’ W (‘Term’ ‘’₁ ⌜ Γ' ⌝c ‘’ ⌜ ‘Σ'’ ‘Context’ ‘Typ’ ⌝T))
    ‘substTyp’ : ∀ {Γ' Γ} {A : Typ Γ}
      → Term {Γ'} (‘Typ’ ‘’ ⌜ Γ ▻ A ⌝c
                  ‘→’ W (‘Term’ ‘’₁ ⌜ Γ ⌝c ‘’ ⌜ A ⌝T
                  ‘→’ W (‘Typ’ ‘’ ⌜ Γ ⌝c)))
    ‘tProd-nd’ : ∀ {Γ} → Term {Γ ▻ ‘Context’ ▻ ‘Typ’ ▻ W ‘Typ’} (W (W ‘Typ’))
    ‘context-pick-if'’ : ∀ {Γ} → Term {Γ} (‘Context’ ‘→’ ‘Typ’ ‘→’ W (W ‘Context’ ‘→’ W1 ‘Typ’ ‘→’ W (W ‘Typ’)))
    -- Ty : ∀ {Γ} → Typ Γ → Term {Γ} ‘Set’
    WSet : ∀ {Γ A} → Term {Γ ▻ A} (W ‘Set’) → Term {Γ ▻ A} ‘Set’
    WWSet : ∀ {Γ A B} → Term {Γ ▻ A ▻ B} (W (W ‘Set’)) → Term {Γ ▻ A ▻ B} ‘Set’
    WWWSet : ∀ {Γ A B C} → Term {Γ ▻ A ▻ B ▻ C} (W (W (W ‘Set’))) → Term {Γ ▻ A ▻ B ▻ C} ‘Set’
    substTyp-weakenTyp : ∀ {Γ A B} {a : Term {Γ} A} → Term {Γ} (W B ‘’ a) → Term {Γ} B
    weakenTyp-substTyp-weakenTyp : ∀ {Γ A B C} {a : Term {Γ} A} → Term {Γ ▻ C} (W (W B ‘’ a)) → Term {Γ ▻ C} (W B)
    weakenTyp-weakenTyp-substTyp-weakenTyp-inv : ∀ {Γ A B C D} {a : Term {Γ} A} → Term {Γ ▻ C ▻ D} (W (W B)) → Term {Γ ▻ C ▻ D} (W (W (W B ‘’ a)))
    weakenTyp-substTyp-tProd : ∀ {Γ T T' A B} {a : Term {Γ} T} → Term {Γ = Γ ▻ T'} (W ((A ‘→’ B) ‘’ a)) → Term {Γ ▻ T'} (W ((A ‘’ a) ‘→’ (B ‘’₁ a)))
    substTyp-weakenTyp1-VAR₀ : ∀ {Γ A T} → Term {Γ ▻ A} (W1 T ‘’ ‘VAR₀’) → Term {Γ ▻ A} T
    weakenTyp-tProd : ∀ {Γ A B C} → Term {Γ = Γ ▻ C} (W (A ‘→’ B)) → Term {Γ = Γ ▻ C} (W A ‘→’ W1 B)
    weakenTyp-tProd-inv : ∀ {Γ A B C} → Term {Γ = Γ ▻ C} (W A ‘→’ W1 B) → Term {Γ = Γ ▻ C} (W (A ‘→’ B))
    weakenTyp-weakenTyp-tProd : ∀ {Γ A B C D} → Term {Γ ▻ C ▻ D} (W (W (A ‘→’ B))) → Term {Γ ▻ C ▻ D} (W (W A ‘→’ W1 B))
    substTyp1-tProd : ∀ {Γ T T' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a} ((A ‘→’ B) ‘’₁ a) → Term {Γ ▻ T' ‘’ a} ((A ‘’₁ a) ‘→’ (B ‘’₂ a))
    weakenTyp-substTyp1-tProd-nd : ∀ {Γ T T' A B} {a : Term {Γ} T} {C} → Term {Γ ▻ T' ‘’ a ▻ C} (W ((A ‘→’ W B) ‘’₁ a)) → Term {Γ ▻ T' ‘’ a ▻ C} (W (A ‘’₁ a) ‘→’ W (W (B ‘’₁ a)))
    weakenTyp1-substTyp1-tProd-nd : ∀ {Γ T T' C A B} {a : Term {Γ} T} → Term {Γ ▻ T' ▻ W (C ‘’ a)} (W1 ((A ‘→’ W B) ‘’₁ a)) → Term {Γ ▻ T' ▻ W (C ‘’ a)} (W1 (A ‘’₁ a) ‘→’ W (W1 (B ‘’₁ a)))
    weakenTyp1-tProd : ∀ {Γ C D A B} → Term {Γ ▻ C ▻ W D} (W1 (A ‘→’ B)) → Term {Γ ▻ C ▻ W D} (W1 A ‘→’ W2 B)
    weakenTyp1-tProd-inv : ∀ {Γ C D A B} → Term {Γ ▻ C ▻ W D} (W1 A ‘→’ W2 B) → Term {Γ ▻ C ▻ W D} (W1 (A ‘→’ B))
    weakenTyp2-tProd-nd : ∀ {Γ C D E A B} → Term {Γ ▻ C ▻ W D ▻ W1 E} (W2 (A ‘→’ W B)) → Term {Γ ▻ C ▻ W D ▻ W1 E} (W2 A ‘→’ W (W2 B))
    substTyp-tProd-nd-weakenTyp-tProd-weakenTyp1-tProd-nd-weakenTyp : ∀ {Γ T A B C D} {a : Term T}
         → Term {Γ} ((A ‘→’ W (W B ‘→’ W1 C ‘→’ W (W D))) ‘’ a)
         → Term {Γ} ((A ‘’ a) ‘→’ W (B ‘→’ C ‘→’ W (W (D ‘’ a))))
    weakenTyp-weakenTyp2-tProd-nd : ∀ {Γ C D E F A B} → Term {Γ ▻ C ▻ W D ▻ W1 E ▻ F} (W (W2 (A ‘→’ W B))) → Term {Γ ▻ C ▻ W D ▻ W1 E ▻ F} (W (W2 A) ‘→’ W (W (W2 B)))
    weakenTyp-weakenTyp-weakenTyp2-weakenTyp : ∀ {Γ A B C D E R} → Term {Γ ▻ A ▻ W B ▻ W1 C ▻ D ▻ E} (W (W (W2 (W R)))) → Term {Γ ▻ A ▻ W B ▻ W1 C ▻ D ▻ E} (W (W (W (W1 R))))
    substTyp2-tProd : ∀ {Γ T T' T'' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a ▻ T'' ‘’₁ a} ((A ‘→’ B) ‘’₂ a) → Term {Γ ▻ T' ‘’ a ▻ T'' ‘’₁ a} ((A ‘’₂ a) ‘→’ (B ‘’₃ a))
    substTyp1-substTyp-weakenTyp-inv : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (A ‘’ a) → Term {Γ} (W A ‘’₁ a ‘’ b)
    substTyp1-substTyp-weakenTyp : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (W A ‘’₁ a ‘’ b) → Term {Γ} (A ‘’ a)
    weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp-inv : ∀ {Γ C T A D E} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ ▻ D ▻ E} (W (W (A ‘’ a))) → Term {Γ ▻ D ▻ E} (W (W (W A ‘’₁ a ‘’ b)))
    weakenTyp-weakenTyp-substTyp1-substTyp-weakenTyp : ∀ {Γ C T A D E} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ ▻ D ▻ E} (W (W (W A ‘’₁ a ‘’ b))) → Term {Γ ▻ D ▻ E} (W (W (A ‘’ a)))
    substTyp2-weakenTyp-inv : ∀ {Γ A B C T} {a : Term {Γ} A} → Term {Γ ▻ B ‘’ a ▻ C ‘’₁ a} (W T ‘’₂ a) → Term {Γ ▻ B ‘’ a ▻ C ‘’₁ a} (W (T ‘’₁ a))
    weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp-inv : ∀ {Γ A B C T T'} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
      → Term {Γ ▻ T'} (W (T ‘’₁ a ‘’ b))
      → Term {Γ ▻ T'} (W (W T ‘’₂ a ‘’₁ b ‘’ c))
    substTyp2-substTyp1-substTyp-weakenTyp : ∀ {Γ A B C T} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
      → Term {Γ} (W T ‘’₂ a ‘’₁ b ‘’ c)
      → Term {Γ} (T ‘’₁ a ‘’ b)
    weakenTyp-substTyp2-substTyp1-substTyp-tProd : ∀ {Γ T T' T'' T''' A B} {a : Term {Γ} T} {b : Term {Γ} (T' ‘’ a)} {c : Term {Γ} (T'' ‘’₁ a ‘’ b)}
      → Term {Γ ▻ T'''} (W ((A ‘→’ B) ‘’₂ a ‘’₁ b ‘’ c))
      → Term {Γ ▻ T'''} ((W (A ‘’₂ a ‘’₁ b ‘’ c)) ‘→’ (W1 (B ‘’₃ a ‘’₂ b ‘’₁ c)))
    weakenTyp2-weakenTyp1 : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ W B ▻ W1 C} (W2 (W D)) → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W1 D))
    weakenTyp2-weakenTyp1-inv : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W1 D)) → Term {Γ ▻ A ▻ W B ▻ W1 C} (W2 (W D))
    weakenTyp-weakenTyp2-weakenTyp : ∀ {Γ A B C D E} → Term {Γ ▻ A ▻ W B ▻ W1 C ▻ D} (W (W2 (W E))) → Term {Γ ▻ A ▻ W B ▻ W1 C ▻ D} (W (W (W1 E)))
    weakenTyp-weakenTyp2-weakenTyp-inv : ∀ {Γ A B C D E} → Term {Γ ▻ A ▻ W B ▻ W1 C ▻ D} (W (W (W1 E))) → Term {Γ ▻ A ▻ W B ▻ W1 C ▻ D} (W (W2 (W E)))
    weakenTyp1-weakenTyp : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W1 (W C)) → Term {Γ ▻ A ▻ W B} (W (W C))
    weakenTyp1-weakenTyp-inv : ∀ {Γ A B C} → Term {Γ ▻ A ▻ W B} (W (W C)) → Term {Γ ▻ A ▻ W B} (W1 (W C))
    weakenTyp1-weakenTyp1-weakenTyp : ∀ {Γ A B C T} → Term {Γ ▻ A ▻ B ▻ W (W C)} (W1 (W1 (W T))) → Term {Γ ▻ A ▻ B ▻ W (W C)} (W1 (W (W T)))
    substTyp1-weakenTyp1 : ∀ {Γ A B C} {a : Term {Γ} A} → Term {Γ ▻ W B ‘’ a} (W1 C ‘’₁ a) → Term {Γ ▻ B} C
    weakenTyp1-substTyp-weakenTyp1-inv : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W (T ‘’ a)))
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W T ‘’₁ a))
    weakenTyp1-substTyp-weakenTyp1 : ∀ {Γ A T'' T' T} {a : Term {Γ} A}
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W T ‘’₁ a))
      → Term {Γ ▻ T'' ▻ W (T' ‘’ a)} (W1 (W (T ‘’ a)))
    weakenTyp-substTyp-substTyp-weakenTyp1 : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
      → Term {Γ ▻ T'} (W (T ‘’ (substTyp-weakenTyp ((‘λ∙’ a) ‘’ₐ b))))
    weakenTyp-substTyp-substTyp-weakenTyp1-inv : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (T ‘’ (substTyp-weakenTyp ((‘λ∙’ a) ‘’ₐ b))))
      → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
    substTyp-weakenTyp1-weakenTyp : ∀ {Γ T} {A : Typ Γ} {B : Typ Γ}
      → {a : Term {Γ = Γ ▻ T} (W {Γ = Γ} {A = T} B)}
      → Term {Γ = Γ ▻ T} (W1 (W A) ‘’ a)
      → Term {Γ = Γ ▻ T} (W A)
    substTyp3-substTyp2-substTyp1-substTyp-weakenTyp : ∀ {Γ A B C D T T'} {a : Term {Γ} A} {b : Term {Γ} (B ‘’ a)} {c : Term {Γ} (C ‘’₁ a ‘’ b)}
         {d : Term {Γ = (Γ ▻ T')} (W (D ‘’₂ a ‘’₁ b ‘’ c))}
         → Term {Γ = (Γ ▻ T')} (W1 (W T ‘’₃ a ‘’₂ b ‘’₁ c) ‘’ d)
         → Term {Γ = (Γ ▻ T')} (W (T ‘’₂ a ‘’₁ b ‘’ c))
    weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 : ∀ {Γ A B C T T'} {a : Term {Γ} A} {b : Term (B ‘’ a)} {c : Term (C ‘’ a)}
      → Term {Γ = (Γ ▻ T')} (W (W1 T ‘’₂ a ‘’₁ b ‘’ substTyp1-substTyp-weakenTyp-inv c))
      → Term {Γ = (Γ ▻ T')} (W (T ‘’₁ a ‘’ c))
    substTyp1-substTyp-tProd : ∀ {Γ T T' A B a b} → Term ((_‘→’_ {Γ = Γ ▻ T ▻ T'} A B) ‘’₁ a ‘’ b) → Term (_‘→’_ {Γ = Γ} (A ‘’₁ a ‘’ b) (B ‘’₂ a ‘’₁ b))
    substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp : ∀ {Γ A} {T : Typ (Γ ▻ A)} {T' C B} {a : Term {Γ} A} {b : Term {Γ = (Γ ▻ C ‘’ a)} (B ‘’₁ a)}
         {c : Term {Γ = (Γ ▻ T')} (W (C ‘’ a))}
         → Term {Γ = (Γ ▻ T')} (W1 (W (W T) ‘’₂ a ‘’ b) ‘’ c)
         → Term {Γ = (Γ ▻ T')} (W (T ‘’ a))
    substTyp1-substTyp-weakenTyp2-weakenTyp : ∀ {Γ T' A B T} {a : Term {Γ ▻ T'} (W A)} {b : Term {Γ ▻ T'} (W1 B ‘’ a)}
      → Term {Γ ▻ T'} (W2 (W T) ‘’₁ a ‘’ b)
      → Term {Γ ▻ T'} (W1 T ‘’ a)
    weakenTyp-weakenTyp1-weakenTyp : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W1 (W D))) → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W (W D)))
    weakenTyp-tProd-tProd-tProd-nd-weakenTyp-tProd-weakenTyp1-tProd-nd-weakenTyp : ∀ {Γ A B C D E X}
      → Term {Γ ▻ X} (W (A ‘→’ B ‘→’ W (W C ‘→’ W1 D ‘→’ W (W E))))
      → Term {Γ ▻ X} (W A ‘→’ W1 B ‘→’ W (W (W C) ‘→’ W1 (W1 D) ‘→’ W (W (W1 E))))
    beta-under-subst : ∀ {Γ A B B'} {g : Term {Γ} (A ‘→’ W B)} {x : Term {Γ} A}
      → Term (B' ‘’ substTyp-weakenTyp (‘λ∙’ (substTyp-weakenTyp (‘λ∙’ (weakenTyp1-weakenTyp (substTyp-weakenTyp1-VAR₀ (weakenTyp-tProd (w (weakenTyp-tProd (w g))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’)) ‘’ₐ x))
      → Term (B' ‘’ substTyp-weakenTyp (g ‘’ₐ x))
    beta-under-subst-inv : ∀ {Γ A B B'} {g : Term {Γ} (A ‘→’ W B)} {x : Term {Γ} A}
      → Term (B' ‘’ substTyp-weakenTyp (g ‘’ₐ x))
      → Term (B' ‘’ substTyp-weakenTyp (‘λ∙’ (substTyp-weakenTyp (‘λ∙’ (weakenTyp1-weakenTyp (substTyp-weakenTyp1-VAR₀ (weakenTyp-tProd (w (weakenTyp-tProd (w g))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’)) ‘’ₐ x))
    ‘proj₁'’ : ∀ {Γ} {T : Typ Γ} {P : Typ (Γ ▻ T)} → Term (‘Σ'’ T P ‘→’ W T)
    ‘proj₂'’ : ∀ {Γ} {T : Typ Γ} {P : Typ (Γ ▻ T)} → Term {Γ ▻ ‘Σ'’ T P} (W1 P ‘’ substTyp-weakenTyp (‘λ∙’ (weakenTyp1-weakenTyp (substTyp-weakenTyp1-VAR₀ (weakenTyp-tProd (w (weakenTyp-tProd (w ‘proj₁'’))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’))
    ‘existT'’ : ∀ {Γ T P} → Term (T ‘→’ P ‘→’ W (W (‘Σ'’ {Γ} T P)))

ε = ε₀

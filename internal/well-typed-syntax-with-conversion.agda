module well-typed-syntax-with-conversion where
open import common

-- infixl 1 _≣T_
infixr 1 _‘→’_
infixl 2 _▻_
infixl 3 _‘’_
{-infixl 2 _▻Typ_-}
{-infixl 3 _‘’_-}
{-infixl 3 _‘t’_
infixl 3 _‘’₁_
infixl 3 _‘’₂_
infixl 3 _‘’₃_
infixl 3 _‘’ₐ_
infixr 1 _‘→’_-}

mutual
  data Context : Set where
    ε₀ : Context
    _▻_ : (Γ : Context) → {i : ℕ} → Typ Γ i → Context

  data Typ : Context → ℕ → Set where
    ‘Type’ : ∀ {Γ} → (i : ℕ) → Typ Γ (suc i)
    W : ∀ {Γ i} {A : Typ Γ i} {j} → Typ Γ j → Typ (Γ ▻ A) j
    W₁ : ∀ {Γ i j k} {A : Typ Γ i} {B : Typ Γ j} → Typ (Γ ▻ B) k → Typ (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B)) k
    _‘→’_ : ∀ {Γ i j} (A : Typ Γ i) → Typ (Γ ▻ A) j → Typ Γ (max i j)
    ‘Σ'’ : ∀ {Γ i j} (T : Typ Γ i) → Typ (Γ ▻ T) j → Typ Γ (max i j)
    of-term : ∀ {Γ i} → Term {Γ} (‘Type’ i) → Typ Γ i

  _▻'_ : (Γ : Context) {i : ℕ} → Typ Γ i → Context
  _▻'_ = _▻_

  data Term : ∀ {Γ i} → Typ Γ i → Set where
    ‘VAR₀’ : ∀ {Γ i} {T : Typ Γ i} → Term {Γ = Γ ▻ T} (W T)
    w : ∀ {Γ i} {T : Typ Γ i} → Term T → Term {Γ ▻ T} (W T)
    ‘λ∙’ : ∀ {Γ i j} {A : Typ Γ i} {B : Typ (Γ ▻ A) j} → Term B → Term (A ‘→’ B)
    ‘proj₁'’ : ∀ {Γ i j} {T : Typ Γ i} {P : Typ (Γ ▻ T) j} → Term {Γ ▻ ‘Σ'’ T P} (W T)
    ‘proj₂'’ : ∀ {Γ i j} {T : Typ Γ i} {P : Typ (Γ ▻ T) j} → Term {Γ ▻ ‘Σ'’ T P} (W₁ P ‘’ ‘proj₁'’)
    ‘existT'’ : ∀ {Γ i j} {T : Typ Γ i} {P : Typ (Γ ▻ T) j} (x : Term T) (p : Term (P ‘’ x)) → Term (‘Σ'’ {Γ} T P)
    of-typ : ∀ {Γ i} → Typ Γ i → Term {Γ} (‘Type’ i)

  _‘→’'_ : ∀ {Γ i j} (A : Typ Γ i) → Typ (Γ ▻' A) j → Typ Γ (max i j)
  _‘→’'_ = _‘→’_

  _‘’_ : ∀ {Γ i} {A : Typ Γ i} {j} → Typ (Γ ▻' A) j → Term {Γ} A → Typ Γ j
  ‘Type’ ℓ ‘’ a = ‘Type’ ℓ
  W B ‘’ a = B
  W₁ B₂ ‘’ a = {!!}
  (A ‘→’ B) ‘’ a = A ‘’ a ‘→’ {!B ‘’ a!}
  ‘Σ'’ A B ‘’ a = ‘Σ'’ (A ‘’ a) {!!}
  of-term x ‘’ a = {!(‘λ∙’ x) ‘’ₐ a!}

  _‘’ₐ_ : ∀ {Γ i j} {A : Typ Γ i} {B : Typ (Γ ▻' A) j} → Term (A ‘→’' B) → (a : Term A) → Term (B ‘’ a)
  _‘’ₐ_ = {!!}
{-
mutual


--    resp-≣ : ∀ {Γ i} {T U : Typ Γ i} → Term T → T ≣T U → Term U

  data _≣T_ : ∀ {Γ i} → Typ Γ i → Typ Γ i → Set where
    ≣T-refl : ∀ {Γ i} {x : Typ Γ i} → x ≣T x
    ≣T-sym : ∀ {Γ i} {x y : Typ Γ i} → x ≣T y → y ≣T x
    ≣T-trans : ∀ {Γ i} {x y z : Typ Γ i} → x ≣T y → y ≣T z → x ≣T z
    WST : ∀ {Γ i A j B a} → _‘’_ {Γ} {i} {A} {j} (W B) a ≣T B
    of-typ-term : ∀ {Γ i} {T : Typ Γ i} → of-term (of-typ T) ≣T T
    resp-≣t : ∀ {Γ i} {T U : Term {Γ} (‘Type’ i)} → T ≣t U → of-term T ≣T of-term U
    ‘’≣ : ∀ {Γ i} {A : Typ Γ i} {j} (B B' : Typ (Γ ▻ A) j) (a a' : Term {Γ} A) → B ≣T B' → a ≣t a' → (B ‘’ a) ≣T (B' ‘’ a')
    W≣ : ∀ {Γ i} {A : Typ Γ i} {j} {B B' : Typ Γ j} → W {Γ} {i} {A} {j} B ≣T W B'
    W₁≣ : ∀ {Γ i j k} {A : Typ Γ i} {B : Typ Γ j} {C C' : Typ (Γ ▻ B) k} → W₁ {Γ} {i} {j} {k} {A} {B} C ≣T W₁ C'
    ‘→’≣ : ∀ {Γ i j} {A : Typ Γ i} {B B' : Typ (Γ ▻ A) j} → (A ‘→’ B) ≣T (A ‘→’ B')
    ‘Σ'’≣ : ∀ {Γ i j} {A : Typ Γ i} {B B' : Typ (Γ ▻ A) j} → (‘Σ'’ A B) ≣T (‘Σ'’ A B')

  data _≣t_ : ∀ {Γ i} {T : Typ Γ i} → Term T → Term T → Set where
    ≣t-refl : ∀ {Γ i} {T : Typ Γ i} {x : Term T} → x ≣t x
    ≣t-sym : ∀ {Γ i} {T : Typ Γ i} {x y : Term T} → x ≣t y → y ≣t x
    ≣t-trans : ∀ {Γ i} {T : Typ Γ i} {x y z : Term T} → x ≣t y → y ≣t z → x ≣t z
    of-term-typ : ∀ {Γ i} {T : Term {Γ} (‘Type’ i)} → of-typ (of-term T) ≣t T
    of-typ-≣T : ∀ {Γ i} {T U : Typ Γ i} → T ≣T U → of-typ T ≣t of-typ U
    resp-≣T : ∀ {Γ i} {T U : Typ Γ i} ( → T ≣T U → of-typ T ≣t of-typ U

-}
{-mutual
  _‘’ₐ_ : ∀ {Γ i j} {A : Typ Γ i} {B : Typ (Γ ▻ A) j} → (f : Term (A ‘→’ B)) → (x : Term A) → Term (B ‘’ x)
  ‘λ∙’ ‘VAR₀’ ‘’ₐ x = {!!}
  ‘λ∙’ (‘λ∙’ f) ‘’ₐ x = {!!}
  ‘λ∙’ ‘proj₁'’ ‘’ₐ x = {!!}
  ‘λ∙’ (‘existT'’ f f₁) ‘’ₐ x = {!!}
  ‘λ∙’ (of-typ x) ‘’ₐ x₁ = {!!}
  ‘λ∙’ (resp-≣ f x) ‘’ₐ x₁ = {!!}
  ‘proj₁'’ ‘’ₐ x = {!!}
  resp-≣ f x ‘’ₐ x₁ = {!!}
-}



{-    _‘t’_ : ∀ {Γ A} {B : Typ (Γ ▻ A)} → (b : Term {Γ = Γ ▻ A} B) → (a : Term {Γ = Γ} A) → Term {Γ = Γ} (B ‘’ a)
    w : ∀ {Γ A B} → Term {Γ = Γ} B → Term {Γ = Γ ▻ A} (W {Γ = Γ} {A = A} B)
    ‘λ∙’ : ∀ {Γ A B} → Term {Γ = (Γ ▻ A)} B → Term {Γ = Γ} (A ‘→’ B)
    _‘’ₐ_ : ∀ {Γ A B} → (f : Term {Γ = Γ} (A ‘→’ B)) → (x : Term {Γ = Γ} A) → Term {Γ = Γ} (B ‘’ x)
    ‘VAR₀’ : ∀ {Γ T} → Term {Γ = Γ ▻ T} (W T)
    substTyp-weakenTyp : ∀ {Γ A B} {a : Term {Γ = Γ} A} → Term {Γ = Γ} (W B ‘’ a) → Term {Γ = Γ} B
    weakenTyp-substTyp-tProd : ∀ {Γ T T' A B} {a : Term {Γ = Γ} T} → Term {Γ = Γ ▻ T'} (W ((A ‘→’ B) ‘’ a)) → Term {Γ ▻ T'} (W ((A ‘’ a) ‘→’ (B ‘’₁ a)))
    substTyp-weakenTyp1-VAR₀ : ∀ {Γ A T} → Term {Γ ▻ A} (W1 T ‘’ ‘VAR₀’) → Term {Γ ▻ A} T
    weakenTyp-tProd : ∀ {Γ A B C} → Term {Γ = Γ ▻ C} (W (A ‘→’ B)) → Term {Γ = Γ ▻ C} (W A ‘→’ W1 B)
    weakenTyp-tProd-inv : ∀ {Γ A B C} → Term {Γ = Γ ▻ C} (W A ‘→’ W1 B) → Term {Γ = Γ ▻ C} (W (A ‘→’ B))
    weakenTyp-weakenTyp-tProd : ∀ {Γ A B C D} → Term {Γ ▻ C ▻ D} (W (W (A ‘→’ B))) → Term {Γ ▻ C ▻ D} (W (W A ‘→’ W1 B))
    substTyp1-tProd : ∀ {Γ T T' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a} ((A ‘→’ B) ‘’₁ a) → Term {Γ ▻ T' ‘’ a} ((A ‘’₁ a) ‘→’ (B ‘’₂ a))
    weakenTyp1-tProd : ∀ {Γ C D A B} → Term {Γ ▻ C ▻ W D} (W1 (A ‘→’ B)) → Term {Γ ▻ C ▻ W D} (W1 A ‘→’ W2 B)
    substTyp2-tProd : ∀ {Γ T T' T'' A B} {a : Term {Γ} T} → Term {Γ ▻ T' ‘’ a ▻ T'' ‘’₁ a} ((A ‘→’ B) ‘’₂ a) → Term {Γ ▻ T' ‘’ a ▻ T'' ‘’₁ a} ((A ‘’₂ a) ‘→’ (B ‘’₃ a))
    substTyp1-substTyp-weakenTyp-inv : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (A ‘’ a) → Term {Γ} (W A ‘’₁ a ‘’ b)
    substTyp1-substTyp-weakenTyp : ∀ {Γ C T A} {a : Term {Γ} C} {b : Term {Γ} (T ‘’ a)} → Term {Γ} (W A ‘’₁ a ‘’ b) → Term {Γ} (A ‘’ a)
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
      → Term {Γ ▻ T'} (W (T ‘’ (substTyp-weakenTyp (a ‘t’ b))))
    weakenTyp-substTyp-substTyp-weakenTyp1-inv : ∀ {Γ T' B A} {b : Term {Γ} B} {a : Term {Γ ▻ B} (W A)} {T : Typ (Γ ▻ A)}
      → Term {Γ ▻ T'} (W (T ‘’ (substTyp-weakenTyp (a ‘t’ b))))
      → Term {Γ ▻ T'} (W (W1 T ‘’ a ‘’ b))
    substTyp-weakenTyp1-weakenTyp : ∀ {Γ T} {A : Typ Γ} {B : Typ Γ}
      → {a : Term {Γ = Γ ▻ T} (W {Γ = Γ} {A = T} B)}
      → Term {Γ = Γ ▻ T} (W1 (W A) ‘’ a)
      → Term {Γ = Γ ▻ T} (W A)
    substTyp3-substTyp2-substTyp1-substTyp-weakenTyp : ∀ {Γ A B C D T T'} {a : Term {Γ = Γ} A} {b : Term {Γ = Γ} (B ‘’ a)} {c : Term {Γ = Γ} (C ‘’₁ a ‘’ b)}
         {d : Term {Γ = (Γ ▻ T')} (W (D ‘’₂ a ‘’₁ b ‘’ c))}
         → Term {Γ = (Γ ▻ T')} (W1 (W T ‘’₃ a ‘’₂ b ‘’₁ c) ‘’ d)
         → Term {Γ = (Γ ▻ T')} (W (T ‘’₂ a ‘’₁ b ‘’ c))
    weakenTyp-substTyp2-substTyp1-substTyp-weakenTyp1 : ∀ {Γ A B C T T'} {a : Term {Γ = Γ} A} {b : Term (B ‘’ a)} {c : Term (C ‘’ a)}
      → Term {Γ = (Γ ▻ T')} (W (W1 T ‘’₂ a ‘’₁ b ‘’ substTyp1-substTyp-weakenTyp-inv c))
      → Term {Γ = (Γ ▻ T')} (W (T ‘’₁ a ‘’ c))
    substTyp1-substTyp-tProd : ∀ {Γ T T' A B a b} → Term ((_‘→’_ {Γ = Γ ▻ T ▻ T'} A B) ‘’₁ a ‘’ b) → Term (_‘→’_ {Γ = Γ} (A ‘’₁ a ‘’ b) (B ‘’₂ a ‘’₁ b))
    substTyp2-substTyp-substTyp-weakenTyp1-weakenTyp-weakenTyp : ∀ {Γ A} {T : Typ (Γ ▻ A)} {T' C B} {a : Term {Γ = Γ} A} {b : Term {Γ = (Γ ▻ C ‘’ a)} (B ‘’₁ a)}
         {c : Term {Γ = (Γ ▻ T')} (W (C ‘’ a))}
         → Term {Γ = (Γ ▻ T')} (W1 (W (W T) ‘’₂ a ‘’ b) ‘’ c)
         → Term {Γ = (Γ ▻ T')} (W (T ‘’ a))
    substTyp1-substTyp-weakenTyp2-weakenTyp : ∀ {Γ T' A B T} {a : Term {Γ ▻ T'} (W A)} {b : Term {Γ ▻ T'} (W1 B ‘’ a)}
      → Term {Γ ▻ T'} (W2 (W T) ‘’₁ a ‘’ b)
      → Term {Γ ▻ T'} (W1 T ‘’ a)
    weakenTyp-weakenTyp1-weakenTyp : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W1 (W D))) → Term {Γ ▻ A ▻ W B ▻ W1 C} (W (W (W D)))
    ‘proj₁'’ : ∀ {Γ} {T : Typ Γ} {P : Typ (Γ ▻ T)} → Term (‘Σ'’ T P ‘→’ W T)
    ‘proj₂'’ : ∀ {Γ} {T : Typ Γ} {P : Typ (Γ ▻ T)} → Term {Γ ▻ ‘Σ'’ T P} (W1 P ‘’ substTyp-weakenTyp (‘λ∙’ (weakenTyp1-weakenTyp (substTyp-weakenTyp1-VAR₀ (weakenTyp-tProd (w (weakenTyp-tProd (w ‘proj₁'’))) ‘’ₐ ‘VAR₀’))) ‘’ₐ ‘VAR₀’))
    ‘existT'’ : ∀ {Γ T P} (x : Term T) (p : Term (P ‘’ x)) → Term (‘Σ'’ {Γ} T P)


  data Typ : Context → ℕ → Set where
    _‘’_ : ∀ {Γ A} → Typ (Γ ▻ A) → Term {Γ = Γ} A → Typ Γ
    _‘’₁_ : ∀ {Γ A B} → (C : Typ (Γ ▻ A ▻ B)) → (a : Term {Γ = Γ} A) → Typ (Γ ▻ B ‘’ a)
    _‘’₂_ : ∀ {Γ A B C} → (D : Typ (Γ ▻ A ▻ B ▻ C)) → (a : Term {Γ = Γ} A) → Typ (Γ ▻ B ‘’ a ▻ C ‘’₁ a)
    _‘’₃_ : ∀ {Γ A B C D} → (E : Typ (Γ ▻ A ▻ B ▻ C ▻ D)) → (a : Term {Γ = Γ} A) → Typ (Γ ▻ B ‘’ a ▻ C ‘’₁ a ▻ D ‘’₂ a)
    W : ∀ {Γ A} → Typ Γ → Typ (Γ ▻ A)
    W1 : ∀ {Γ A B} → Typ (Γ ▻ B) → Typ (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B))
    W2 : ∀ {Γ A B C} → Typ (Γ ▻ B ▻ C) → Typ (Γ ▻ A ▻ W B ▻ W1 C)
    _‘→’_ : ∀ {Γ} (A : Typ Γ) → Typ (Γ ▻ A) → Typ Γ
    WT : ∀ {Γ A} → Typ Γ → Typ (Γ ▻Typ A)
    WT₁ : ∀ {Γ A B} → Typ (Γ ▻ B) → Typ (Γ ▻Typ A ▻ WT B)
    WT₂ : ∀ {Γ A B C} → Typ (Γ ▻ B ▻ C) → Typ (Γ ▻Typ A ▻ WT B ▻ WT₁ C)
    ‘TVAR₀₀’ : ∀ {Γ} → Typ (Γ ▻Typ Γ)
    ‘TVAR₀₁’ : ∀ {Γ T} → Typ (Γ ▻Typ (Γ ▻ T) ▻ WT T)
    ‘TVAR₀₂’ : ∀ {Γ A B} → Typ (Γ ▻Typ (Γ ▻ A ▻ B) ▻ WT A ▻ WT₁ B)
    {-‘cstTVAR₀’ : ∀ {Γ Γ'} → Term {Γ ▻Typ Γ'} ‘TVAR₀’ → Typ Γ'-}
    ‘Σ'’ : ∀ {Γ} (T : Typ Γ) → Typ (Γ ▻ T) → Typ Γ
    {-‘Context’ : Typ ε₀
    ‘Typ’ : Typ (ε₀ ▻ ‘Context’)-}
    {-
-}
-}

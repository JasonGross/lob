module well-typed-initial-context where
open import well-typed-syntax
open import common

pattern ε₀▻‘Typ’ = ε₀
  ▻Typ ε₀ {- ‘Context’ : Typ ε -}
pattern ε₀▻‘Typ’▻‘Context’ = ε₀▻‘Typ’
  ▻Typ (ε₀▻‘Typ’ ▻ ‘TVAR₀₀’) {- ‘Typ’ : Typ (ε ▻ ‘Context’)-}
pattern ε₀▻‘Typ’▻‘Context’▻‘Term’ = ε₀▻‘Typ’▻‘Context’
  ▻Typ (ε₀▻‘Typ’▻‘Context’ ▻ WT ‘TVAR₀₀’ ▻ ‘TVAR₀₁’) {- ‘Typ’ : Typ (ε ▻ ‘Context’)-}
{-  ▻ {!!} {- record Σ {A : Set} (P : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : P proj₁ -}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}
  ▻ {!!}-}
{-postulate
  ‘Context’ : Typ ε
  ‘Typ’ : Typ (ε ▻ ‘Context’)-}


arrow-tower : Set → Set → ℕ → Set
arrow-tower T R 0 = R
arrow-tower T R (suc n) = T → (arrow-tower T R n)

lambda-tower : ∀ {T} → (T → T → T) → (n : ℕ) → T → arrow-tower T T n
lambda-tower F 0 = λ x → x
lambda-tower F (suc n) = λ x y → lambda-tower F n (F x y)

arrow-tower-to-arrow : ∀ {T} {R} → (R → Set) → (n : ℕ) → arrow-tower T R n → Set
arrow-tower-to-arrow {T} f 0 X = f X
arrow-tower-to-arrow {T} f (suc n) X = {x : T} → arrow-tower-to-arrow f n (X x)

lambda-tower-to-lambda : ∀ {T}
  → (F : T → T → T)
  → (P : T → Set)
  → (f : ∀ {a b : T} → P a → P (F a b))
  → (n : ℕ)
  → (x : T)
  → (y : T)
  → (p : P (F x y))
  → arrow-tower-to-arrow P n (lambda-tower F n (F x y))
lambda-tower-to-lambda {T} F P f 0 x y p = p
lambda-tower-to-lambda {T} F P f (suc n) x y p = λ {z} → lambda-tower-to-lambda F P f n (F x y) z (f p)

Context-Tower : (n : ℕ) → arrow-tower Context Context (suc n)
Context-Tower = lambda-tower _▻Typ_

Typ-Context-Tower : (n : ℕ) → Set
Typ-Context-Tower n = {Γ : Context} → arrow-tower-to-arrow {Context} {Context} Typ n (Context-Tower (suc n) Γ Γ)

‘TVAR_₀’ : (n : ℕ) → Typ-Context-Tower n
‘TVAR_₀’ n = λ {Γ} → lambda-tower-to-lambda {Context} _▻Typ_ Typ WT n Γ Γ ‘TVAR₀₀’

{-‘TVAR_₁’ : (n : ℕ) → Typ-Context-Tower n
‘TVAR_₁’ n = λ {Γ} {Γ'} → {!lambda-tower-to-lambda {Context} _▻Typ_ Typ WT n Γ Γ' {!!} {-‘TVAR₀₀’-}!}-}

abstract
  pattern εp = ε₀▻‘Typ’▻‘Context’▻‘Term’

  ε : Context
  ε = εp

  ‘Context’ : Typ ε
  ‘Context’ = ‘TVAR 2 ₀’ {ε₀}

  pattern ‘Typ’p = WT₁ ‘TVAR₀₁’

  ‘Typ’ : Typ (ε ▻ ‘Context’)
  ‘Typ’ = ‘Typ’p

  ‘Term’ : Typ (ε ▻ ‘Context’ ▻ ‘Typ’)
  ‘Term’ = ‘TVAR₀₂’
  {-context-pick-if-ε▻T : ∀ {P : Context → Set}
    → {Γ : Context}
    → {T : Typ ε}
    → (recase : ∀ {T'} → P (ε ▻ T') → P (ε ▻ T))
    → (dummy : P (ε ▻ T))
    → (val : P Γ)
    → P (ε ▻ T)
  context-pick-if-ε▻T {P} {εp ▻ T'} {T} recase dummy val = recase val
  context-pick-if-ε▻T {P} {Γ} recase dummy val = dummy

  context-pick-if-ε▻T-refl : ∀ {P : Context → Set}
    → {T : Typ ε}
    → {recase : ∀ {T''} → P (ε ▻ T'') → P (ε ▻ T)}
    → {dummy : P (ε ▻ T)}
    → {val : P (ε ▻ T)}
    → recase {T} val ≡ val
    → context-pick-if-ε▻T {P} {ε ▻ T} {T} recase dummy val ≡ val
  context-pick-if-ε▻T-refl H = H-}

  context-pick-if' : ∀ {P : Context → Set}
    → {Γ : Context}
    → (dummy : P (ε ▻ ‘Σ'’ ‘Context’ ‘Typ’))
    → (val : P Γ)
    → P (ε ▻ ‘Σ'’ ‘Context’ ‘Typ’)
  context-pick-if' {P} {εp ▻ ‘Σ'’ ._ ‘Typ’p} dummy val = val
  context-pick-if' {P} {_} dummy val = dummy

  context-pick-if-refl' : ∀ {P dummy val} →
    context-pick-if' {P} {ε ▻ ‘Σ'’ ‘Context’ ‘Typ’} dummy val ≡ val
  context-pick-if-refl' = refl


  {-


-}
{-

infixr 1 _,_

record Σ {A : Set} (P : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : P proj₁

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

sym : {A : Set} → {x : A} → {y : A} → x ≡ y → y ≡ x
sym refl = refl

transport : ∀ {A : Set} {x : A} {y : A} → (P : A → Set) → x ≡ y → P x → P y
transport P refl v = v
-}

{-
infixl 2 _▻_
infixl 3 _‘’_
infixl 3 _‘t’_
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
    _‘’_ : ∀ {Γ A} → Typ (Γ ▻ A) → Term {Γ = Γ} A → Typ Γ
    _‘’₁_ : ∀ {Γ A B} → (C : Typ (Γ ▻ A ▻ B)) → (a : Term {Γ = Γ} A) → Typ (Γ ▻ B ‘’ a)
    _‘’₂_ : ∀ {Γ A B C} → (D : Typ (Γ ▻ A ▻ B ▻ C)) → (a : Term {Γ = Γ} A) → Typ (Γ ▻ B ‘’ a ▻ C ‘’₁ a)
    _‘’₃_ : ∀ {Γ A B C D} → (E : Typ (Γ ▻ A ▻ B ▻ C ▻ D)) → (a : Term {Γ = Γ} A) → Typ (Γ ▻ B ‘’ a ▻ C ‘’₁ a ▻ D ‘’₂ a)
    W : ∀ {Γ A} → Typ Γ → Typ (Γ ▻ A)
    W1 : ∀ {Γ A B} → Typ (Γ ▻ B) → Typ (Γ ▻ A ▻ (W {Γ = Γ} {A = A} B))
    W2 : ∀ {Γ A B C} → Typ (Γ ▻ B ▻ C) → Typ (Γ ▻ A ▻ W B ▻ W1 C)
    _‘→’_ : ∀ {Γ} (A : Typ Γ) → Typ (Γ ▻ A) → Typ Γ
    {-‘Σ’ : ∀ (T : Typ ε₀) → Typ (ε₀ ▻ T) → Typ ε₀
    ‘Context’ : Typ ε₀
    ‘Typ’ : Typ (ε₀ ▻ ‘Context’)-}


  data Term : ∀ {Γ} → Typ Γ → Set where
    _‘t’_ : ∀ {Γ A} {B : Typ (Γ ▻ A)} → (b : Term {Γ = Γ ▻ A} B) → (a : Term {Γ = Γ} A) → Term {Γ = Γ} (B ‘’ a)
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

ε = ε₀
-}

open import Relation.Binary.PropositionalEquality

{-# NON_TERMINATING #-}
undefined : ∀ {A : Set} → A
undefined = undefined

infixl 4 _,_
infixr 1 _‘→’_
infix 5 _++
infix 5 ++_
infixl 10 _cw_

data Con : Set
data _++ : Con → Set

data Ty (Γ : Con) : Set
data Var : ∀ Γ → Ty Γ → Set
data Tm (Γ : Con) : Ty Γ → Set

_▻'_ : ∀ Γ → Ty Γ → Con
ε' : ∀ Γ → Γ ++

++_ : ∀ {Γ} → Γ ++ → Con
_cw_ : ∀ {Γ} A → Γ ++ → (Γ ▻' A) ++

_▻_ : ∀ {Γ} (Δ : Γ ++) → Ty (++ Δ) → Γ ++

lem-cw-ε : ∀ Γ → Γ ≡ ++ ε' Γ
lem-cw-ε-++ : ∀ {Γ} (Δ : Γ ++) X → ++ X cw ε' (++ Δ) ≡ ++ (Δ ▻ X)
lem-cw-ε-++-2 : ∀ {Γ} (Δ : Γ ++) → ++ Δ ≡ ++ ε' (++ Δ)

Wₙ : ∀ {Γ} (Δ : Γ ++) (A : Ty Γ) → Ty (++ Δ) → Ty (++ A cw Δ)
wₙ : ∀ {Γ} (Δ : Γ ++) (B : Ty Γ) {A} → Tm (++ Δ) A → Tm (++ B cw Δ) (Wₙ Δ B A)
vₙ : ∀ {Γ} (Δ : Γ ++) (B : Ty Γ) {A} → Var (++ Δ) A → Var (++ B cw Δ) (Wₙ Δ B A)

lem-cw-Wₙ : ∀ {Γ} (Δ : Γ ++) A X → ++ A cw (Δ ▻ X) ≡ ++ (Wₙ Δ A X cw ε' (++ A cw Δ))

lem-Wₙ-1 : ∀ {Γ} (Δ : Γ ++) A X → Wₙ (ε' (++ A cw Δ)) (Wₙ Δ A X) (subst Ty (lem-cw-ε _) (Wₙ Δ A X)) ≡ subst Ty (lem-cw-Wₙ _ _ _) (Wₙ (Δ ▻ X) A (subst Ty (lem-cw-ε-++ _ _) (Wₙ (ε' (++ Δ)) X (subst Ty (lem-cw-ε-++-2 _) X))))
lem-Wₙ-2 : ∀ {Γ} (Δ : Γ ++) A (B : Ty (++ Δ)) X → Wₙ (ε' (++ A cw Δ)) (Wₙ Δ A X) (subst Ty (lem-cw-ε _) (Wₙ Δ A B)) ≡ subst Ty (lem-cw-Wₙ _ _ _) (Wₙ (Δ ▻ X) A (subst Ty (lem-cw-ε-++ _ _) (Wₙ (ε' (++ Δ)) X (subst Ty (lem-cw-ε-++-2 _) B))))

data Con where
  ∅ : Con
  _,_ : ∀ Γ → Ty Γ → Con

_▻'_ = _,_

data _++ where
  ε : ∀ Γ → Γ ++
  _,_ : ∀ {Γ} (Δ : Γ ++) → Ty (++ Δ) → Γ ++

_▻_ = _,_
ε' = ε

++ ε Γ = Γ
++ (Δ , x) = ++ Δ , x

A cw ε Γ = ε (Γ , A)
A cw (Δ , x) = A cw Δ , Wₙ Δ A x

lem-cw-ε = λ _ → refl
lem-cw-ε-++ = λ _ _ → refl
lem-cw-ε-++-2 = λ _ → refl
lem-cw-Wₙ = λ _ _ _ → refl

data Ty (Γ : Con) where
  U : Ty Γ
--  El : Tm Γ U → Ty Γ -- this constructor causes problems for termination of weakening
  _‘→’_ : Ty Γ → Ty Γ → Ty Γ
--  ‘Σ’ : ∀ A → Ty (Γ , A) → Ty Γ

data Var where
  vz : ∀ {Γ A}             → Var (Γ , A) (Wₙ (ε Γ) A A)
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ , B) (Wₙ (ε Γ) B A)

data Tm (Γ : Con) where
  ‘λ’ : ∀ {A B} → Tm (Γ , A) (Wₙ (ε _) A B) → Tm Γ (A ‘→’ B)
  var : ∀ {A} → Var Γ A → Tm Γ A

-- Wₙ Δ A (El x) = El (wₙ Δ A x)
-- Wₙ Δ A (‘Π’ ty ty') = ‘Π’ (Wₙ Δ A ty) (Wₙ (Δ , ty) A ty')

-- wₙ Δ A (‘λ’ tm) = ‘λ’ (wₙ (Δ , _) A tm)
-- wₙ Δ A (var v) = var (vₙ Δ A v)

Wₙ Δ A U = U
-- Wₙ Δ A (El x) = El (wₙ Δ A x)
Wₙ Δ A (ty ‘→’ ty') = (Wₙ Δ A ty) ‘→’ (Wₙ Δ A ty')

wₙ {Γ} Δ A (‘λ’ {X} {Y} tm) = ‘λ’ helper'
  where helper : Tm (++ A cw (Δ , _)) (Wₙ (Δ , X) A (Wₙ (ε (++ Δ)) X Y))
        helper = wₙ (Δ , _) A tm

        helper' : Tm (++ A cw Δ , Wₙ Δ A X)
                      (Wₙ (ε (++ A cw Δ)) (Wₙ Δ A X) (Wₙ Δ A Y))
        helper' = subst (Tm (++ A cw Δ , Wₙ Δ A _)) (sym (lem-Wₙ-2 Δ A Y X)) helper
wₙ Δ A (var v) = var (vₙ Δ A v)

vₙ (ε Γ) A v = vs v
vₙ (Δ , X) A vz = subst (λ t → Var (++ A cw Δ , Wₙ Δ A X) t) (lem-Wₙ-1 _ _ _) vz -- ACK!
vₙ (Δ , X) A (vs {A = B} v) = subst (λ t → Var (++ A cw Δ , Wₙ Δ A X) t) (lem-Wₙ-2 _ _ _ _) (vs (vₙ Δ A v))

lem-Wₙ-1 Δ A X = lem-Wₙ-2 Δ A X X
lem-Wₙ-2 Δ A U X = refl
lem-Wₙ-2 Δ A (B ‘→’ B₁) X = {!!}

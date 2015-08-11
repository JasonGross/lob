open import Relation.Binary.PropositionalEquality

infixl 4 _,_
infix 5 _++
--infix 5 ++_
infixl 5 _+++_
infixl 10 _cw_
infixr 4 _▻'_
infixr 4 _▻_

data Con : Set
data _++ : Con → Set

data Ty (Γ : Con) : Set
data Var : ∀ Γ → Ty Γ → Set
data Tm (Γ : Con) : Ty Γ → Set

_▻'_ : ∀ Γ → Ty Γ → Con
ε' : ∀ Γ → Γ ++

_+++_ : ∀ Γ → Γ ++ → Con

--++_ : ∀ {Γ} → Γ ++ → Con
_cw_ : ∀ {Γ} A → Γ ++ → (Γ ▻' A) ++

--++_ {Γ} Δ = Γ +++ Δ

_▻_ : ∀ {Γ} (Δ : Γ ++) → Ty (Γ +++ Δ) → Γ ++

lem-cw-ε : ∀ Γ → Γ ≡ Γ +++ ε' Γ
lem-cw-ε-++ : ∀ {Γ} (Δ : Γ ++) X → (Γ +++ Δ ▻' X) +++ X cw ε' (Γ +++ Δ) ≡ Γ +++ (Δ ▻ X)
lem-cw-ε-++-2 : ∀ {Γ} (Δ : Γ ++) → Γ +++ Δ ≡ Γ +++ Δ +++ ε' (Γ +++ Δ)

Wₙ : ∀ {Γ} (Δ : Γ ++) (A : Ty Γ) → Ty (Γ +++ Δ) → Ty ((Γ ▻' A) +++ A cw Δ)
wₙ : ∀ {Γ} (Δ : Γ ++) (B : Ty Γ) {A} → Tm (Γ +++ Δ) A → Tm ((Γ ▻' B) +++ B cw Δ) (Wₙ Δ B A)
vₙ : ∀ {Γ} (Δ : Γ ++) (B : Ty Γ) {A} → Var (Γ +++ Δ) A → Var ((Γ ▻' B) +++ B cw Δ) (Wₙ Δ B A)

lem-cw-Wₙ : ∀ {Γ} (Δ : Γ ++) A X → (Γ ▻' A) +++ A cw (Δ ▻ X) ≡ ((Γ ▻' A) +++ A cw Δ ▻' Wₙ Δ A X) +++ (Wₙ Δ A X cw ε' ((Γ ▻' A) +++ A cw Δ))

lem-Wₙ-1 : ∀ {Γ} (Δ : Γ ++) A X → Wₙ (ε' ((Γ ▻' A) +++ A cw Δ)) (Wₙ Δ A X) (subst Ty (lem-cw-ε _) (Wₙ Δ A X)) ≡ subst Ty (lem-cw-Wₙ _ _ _) (Wₙ (Δ ▻ X) A (subst Ty (lem-cw-ε-++ _ _) (Wₙ (ε' (Γ +++ Δ)) X (subst Ty (lem-cw-ε-++-2 _) X))))
lem-Wₙ-2 : ∀ {Γ} (Δ : Γ ++) A (B : Ty (Γ +++ Δ)) X → Wₙ (ε' ((Γ ▻' A) +++ A cw Δ)) (Wₙ Δ A X) (subst Ty (lem-cw-ε _) (Wₙ Δ A B)) ≡ subst Ty (lem-cw-Wₙ _ _ _) (Wₙ (Δ ▻ X) A (subst Ty (lem-cw-ε-++ _ _) (Wₙ (ε' (Γ +++ Δ)) X (subst Ty (lem-cw-ε-++-2 _) B))))

data Con where
  ∅ : Con
  _,_ : ∀ Γ → Ty Γ → Con

_▻'_ = _,_

data _++ where
  ε : ∀ Γ → Γ ++
  _,_ : ∀ {Γ} (Δ : Γ ++) → Ty (Γ +++ Δ) → Γ ++

_▻_ = _,_
ε' = ε

._ +++ (ε Γ) = Γ
._ +++ (Δ , x) = _ +++ Δ , x

A cw ε Γ = ε (Γ , A)
A cw (Δ , x) = A cw Δ , Wₙ Δ A x

lem-cw-ε = λ _ → refl
lem-cw-ε-++ = λ _ _ → refl
lem-cw-ε-++-2 = λ _ → refl
lem-cw-Wₙ = λ _ _ _ → refl

data Ty (Γ : Con) where
  U : Ty Γ
--  El : Tm Γ U → Ty Γ -- this constructor causes problems for termination of weakening
  ‘Π’ : ∀ A → Ty (Γ , A) → Ty Γ
--  ‘Σ’ : ∀ A → Ty (Γ , A) → Ty Γ

data Var where
  vz : ∀ {Γ A}             → Var (Γ , A) (Wₙ (ε Γ) A A)
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ , B) (Wₙ (ε Γ) B A)

data Tm (Γ : Con) where
  ‘λ’ : ∀ {A B} → Tm (Γ , A) B → Tm Γ (‘Π’ A B)
  var : ∀ {A} → Var Γ A → Tm Γ A

-- Wₙ Δ A (El x) = El (wₙ Δ A x)
-- Wₙ Δ A (‘Π’ ty ty') = ‘Π’ (Wₙ Δ A ty) (Wₙ (Δ , ty) A ty')

-- wₙ Δ A (‘λ’ tm) = ‘λ’ (wₙ (Δ , _) A tm)
-- wₙ Δ A (var v) = var (vₙ Δ A v)

Wₙ Δ A U = U
-- Wₙ Δ A (El x) = El (wₙ Δ A x)
Wₙ Δ A (‘Π’ ty ty') = ‘Π’ (Wₙ Δ A ty) (Wₙ (Δ , ty) A ty')

wₙ Δ A (‘λ’ tm) = ‘λ’ (wₙ (Δ , _) A tm)
wₙ Δ A (var v) = var (vₙ Δ A v)

vₙ (ε Γ) A v = vs v
vₙ (Δ , X) A vz = subst (λ t → Var ((_ ▻' A) +++ A cw Δ , Wₙ Δ A X) t) (lem-Wₙ-1 _ _ _) vz -- ACK!
vₙ (Δ , X) A (vs {A = B} v) = subst (λ t → Var ((_ ▻' A) +++ A cw Δ , Wₙ Δ A X) t) (lem-Wₙ-2 _ _ _ _) (vs (vₙ Δ A v))

lem-Wₙ-1 Δ A U = refl
lem-Wₙ-1 Δ A (‘Π’ X X₁) = {!!}
lem-Wₙ-2 Δ A B X = {!!}

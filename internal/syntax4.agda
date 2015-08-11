{-# OPTIONS --without-K #-}
module syntax4 where
open import Relation.Binary.PropositionalEquality

cong₂-dep : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
            (f : (x : A) → B x → C) {x y u v} → (H : x ≡ y) → subst _ H u ≡ v → f x u ≡ f y v
cong₂-dep f refl refl = refl

infixl 4 _▻_
infixl 4 _▻'_
infixl 4 _◅++_
infixl 4 _▻++_
--infixl 4 _▻+++_
infixl 3 _+++_
infixl 3 _++++_
infix 5 _++
-- infix 5 ++_
--infixl 4 _,_
--infix 5 _++
--infix 5 ++_
--infixl 10 _cw_

mutual
  data Context : Set where
    ε : Context
    _▻'_ : (Γ : Context) → Type Γ → Context

  data _++ : Context → Set where
    ε++ : ∀ Γ → Γ ++
    _▻++_ : ∀ {Γ} (Δ : Γ ++) → Type (Γ +++ Δ) → Γ ++

  _+++_ : ∀ Γ → Γ ++ → Context
  Γ +++ ε++ .Γ = Γ
  Γ +++ (Δ ▻++ x) = (Γ +++ Δ) ▻ x

  data Type (Γ : Context) : Set where
    U : Type Γ
    ‘Π’ : ∀ A → Type (Γ ▻ A) → Type Γ

  _▻_ : (Γ : Context) → Type Γ → Context
  _▻_ = _▻'_

  _◅++_ : ∀ {Γ} (A : Type Γ) (Δ : (Γ ▻ A) ++) → Γ ++
  A ◅++ ε++ ._ = ε++ _ ▻++ A
  A ◅++ (Δ ▻++ x) = A ◅++ Δ ▻++ subst Type (◅++-≡ _ A Δ) x

  ◅++-≡ : ∀ Γ A Δ → ((Γ ▻ A) +++ Δ) ≡ (Γ +++ A ◅++ Δ)
  ◅++-≡ Γ A (ε++ .(Γ ▻' A)) = refl
  ◅++-≡ Γ A (Δ ▻++ x) = cong₂-dep _▻_ (◅++-≡ Γ A Δ) refl

  _▻+++_ : ∀ {Γ Δ} (Δ' : (Γ +++ Δ) ++) → Type (Γ +++ Δ +++ Δ') → Γ ++
  _▻+++_ {Δ = ε++ ._} Δ' T = Δ' ▻++ T
  _▻+++_ {Δ = Δ ▻++ x} Δ' T = _▻+++_ {Δ = Δ} (x ◅++ Δ') (subst Type (◅++-≡ _ x Δ') T)

  _++++_ : ∀ {Γ} → (Δ : Γ ++) → (Γ +++ Δ) ++ → Γ ++
  --Δ ++++ ε++ ._ = Δ
  --_++++_ {Γ} Δ (Δ' ▻++ x) = {!!}
  ε++ Γ ++++ Δ' = Δ'
  Δ ▻++ x ++++ Δ' = Δ ++++ x ◅++ Δ'

  Wcₙ : ∀ {Γ A} → Γ ++ → (Γ ▻ A) ++
  Wcₙ {Γ} {A} (ε++ .Γ) = ε++ (Γ ▻ A)
  Wcₙ {Γ} {A} (Δ ▻++ T) = Wcₙ {Γ} {A} Δ ▻++ Wₙ {Γ} {A} {Δ} T

  Wₙ : ∀ {Γ A} {Δ : Γ ++} → Type (Γ +++ Δ) → Type (Γ ▻ A +++ Wcₙ {Γ} {A} Δ)
  Wₙ U = U
  Wₙ {Γ} {A} {Δ} (‘Π’ T T₁) = ‘Π’ (Wₙ {Γ} {A} {Δ} T) (Wₙ {Γ} {A} {Δ ▻++ T} T₁)

  {-Wₙ-exch : ∀ {Γ₀ A Γ₁ B Γ₂} {T : Type (Γ₀ +++ (Γ₁ ++++ Γ₂))}
    → let WTa : Type (Γ₀ ▻ A +++ Wcₙ (Γ₁ ++++ Γ₂))
          WTa = Wₙ {Γ₀} {A} {Γ₁ ++++ Γ₂} T
          WTba : Type ((Γ₀ ▻ A +++ Wcₙ Γ₁) ▻ B +++ Wcₙ {!!})
          WTba = Wₙ {Γ₀ ▻ A +++ Wcₙ Γ₁} {B} {{!!}} {!!}
 -- Wₙ {Γ₀ +++ Γ₁} {B} {Γ₂} T
          k : Type ((Γ₀ +++ Γ₁) ▻ {!!} +++ Wcₙ {!!})
          k = Wₙ {Γ₀ +++ Γ₁} {{!!}} {{!!}} {!!}
      in k ≡ k
  Wₙ-exch {Γ₀} {A} {Γ₁} {B} {Γ₂} {T} = {!!}-}

  data Var : ∀ Γ → Type Γ → Set where
    vz : ∀ {Γ T}             → Var (Γ ▻ T) (Wₙ {Γ} {T} {ε++ Γ} T)
    vs : ∀ {Γ T A} → Var Γ T → Var (Γ ▻ A) (Wₙ {Γ} {A} {ε++ Γ} T)

  data Term : ∀ Γ → Type Γ → Set where
    ‘λ’ : ∀ {Γ A B} → Term (Γ ▻ A) B → Term Γ (‘Π’ A B)
    varₙ : ∀ {Γ A} → Var Γ A → Term Γ A

  Wc* : ∀ {Γ Δ} → Γ ++ → (Γ +++ Δ) ++
  Wc* {Γ} {Δ} (ε++ .Γ) = ε++ (Γ +++ Δ)
  Wc* {Γ} {Δ} (Δ' ▻++ T) = Wc* {Γ} {Δ} Δ' ▻++ {!Wₙ* {Γ} {Δ} {Δ'} T!}

{-  Wₙ : ∀ {Γ} {Δ : Γ ++} {Δ' : Γ ++} → Type (Γ +++ Δ') → Type (Γ +++ Δ +++ Wc Δ')
  Wₙ U = U
  Wₙ {Γ} {Δ} {Δ'} (‘Π’ T T₁) = ‘Π’ (Wₙ* {Γ} {Δ} {Δ'} T) (Wₙ* {Γ} {Δ} {Δ' ▻++ T} T₁)-}

{-  wₙ* : ∀ {Γ} {Δ : Γ ++} {Δ' : Γ ++} {Γ'} {T : Type Γ'}
    → (H : Γ' ≡ (Γ +++ Δ'))
    → Term (Γ') T
    → Term (Γ +++ Δ +++ Wc Δ') (Wₙ* {Γ} {Δ} {Δ'} (subst Type H T))
  wₙ* {Γ} {Δ} {Δ'} {Γ'} {._} H (‘λ’ {.Γ'} {A} {B} t) = helper H t
    where helper : ∀ {Γ} {Δ : Γ ++} {Δ' : Γ ++} {Γ'} {A : Type Γ'} {B : Type (Γ' ▻ A)}
                 → (H : Γ' ≡ (Γ +++ Δ'))
                 → Term (Γ' ▻ A) B
                 → Term (Γ +++ Δ +++ Wc {Γ} {Δ} Δ') (Wₙ* {Γ} {Δ} {Δ'} (subst Type H (‘Π’ A B)))
          helper {Γ} {Δ} {Δ'} {._} {A} {B} refl t = ‘λ’ (wₙ* {Γ} {Δ} {Δ' ▻++ A} {Γ +++ Δ' ▻++ A} {B} refl t)
  wₙ* {Γ} {Δ} {Δ'} {._} {._} H (varₙ {Γ''} {A''} {Δ''}) = helper {Γ} {Δ} {Δ'} {Γ''} {A''} {Δ''} H
    where helper : ∀ {Γ} {Δ : Γ ++} {Δ' : Γ ++} {Γ''} {A''} {Δ''}
                 → (H : (Γ'' ▻ A'' +++ Δ'') ≡ (Γ +++ Δ'))
                 → Term (Γ +++ Δ +++ Wc {Γ} {Δ} Δ') (Wₙ* {Γ} {Δ} {Δ'} (subst Type H (Wₙ {Γ''} {A''} {Δ''} A'')))
          helper {Γ} {Δ} {Δ' = ε++ ._} {Γ''} {A''} {Δ''} H = {!!}
          helper {Δ' = Δ''' ▻++ x} H₁ = {!!}-}





{-
data Con : Set
data _++ : Con → Set

data Ty (Γ : Con) : Set
data Var : ∀ Γ → Ty Γ → Set
data Tm (Γ : Con) : Ty Γ → Set
-}

{-# OPTIONS --without-K #-}
module syntax3 where
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product

cong₂-dep : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
            (f : (x : A) → B x → C) {x y u v} → (H : x ≡ y) → subst _ H u ≡ v → f x u ≡ f y v
cong₂-dep f refl H = cong (f _) H

infixl 4 _▻_
infixl 4 _▻'_
infixl 4 _◅++_
infixl 4 _▻++_
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
    ε++ : ∀ {Γ} → Γ ++
    _▻++_ : ∀ {Γ} (Δ : Γ ++) → Type (Γ +++ Δ) → Γ ++

  ε++' : ∀ {Γ} → Γ ++
  ε++' = ε++

  _+++_ : ∀ Γ → Γ ++ → Context
  Γ +++ ε++ = Γ
  Γ +++ (Δ ▻++ x) = (Γ +++ Δ) ▻ x

  data Type (Γ : Context) : Set where
    U : Type Γ
    ‘Π’ : ∀ A → Type (Γ ▻ A) → Type Γ

  data Term : ∀ Γ → Type Γ → Set where
    ‘λ’ : ∀ {Γ A B} → Term (Γ ▻ A) B → Term Γ (‘Π’ A B)
    varₙ : ∀ {Γ A Δ} → Term ((Γ ▻ A) +++ Δ) (Wₙ {Γ} A Δ A)

  _▻_ : (Γ : Context) → Type Γ → Context
  _▻_ = _▻'_

  _◅++_ : ∀ {Γ} (A : Type Γ) (Δ : (Γ ▻ A) ++) → Γ ++
  A ◅++ ε++ = ε++ ▻++ A
  A ◅++ (Δ ▻++ x) = A ◅++ Δ ▻++ subst Type (◅++-≡ _ A Δ) x

  ◅++-≡ : ∀ Γ A Δ → ((Γ ▻ A) +++ Δ) ≡ (Γ +++ A ◅++ Δ)
  ◅++-≡ Γ A ε++ = refl
  ◅++-≡ Γ A (Δ ▻++ x) = cong₂-dep _▻_ (◅++-≡ Γ A Δ) refl

  _▻+++_ : ∀ {Γ Δ} (Δ' : (Γ +++ Δ) ++) → Type (Γ +++ Δ +++ Δ') → Γ ++
  _▻+++_ {Δ = ε++} Δ' T = Δ' ▻++ T
  _▻+++_ {Δ = Δ ▻++ x} Δ' T = _▻+++_ {Δ = Δ} (x ◅++ Δ') (subst Type (◅++-≡ _ x Δ') T)

  _++++_ : ∀ {Γ} → (Δ : Γ ++) → (Γ +++ Δ) ++ → Γ ++
  Δ ++++ ε++ = Δ
  _++++_ {Γ} Δ (Δ' ▻++ x) = (_++++_ {Γ} Δ Δ') ▻++ subst Type (++++-assoc Δ Δ') x
  --ε++ ++++ Δ' = Δ'
  --Δ ▻++ x ++++ Δ' = Δ ++++ x ◅++ Δ'

  ++++-assoc : ∀ {Γ} Δ Δ' → (Γ +++ Δ +++ Δ') ≡ (Γ +++ (Δ ++++ Δ'))
  ++++-assoc Δ ε++ = refl
  ++++-assoc Δ (Δ' ▻++ x) = cong₂-dep _▻_ (++++-assoc Δ Δ') refl

  Wc : ∀ {Γ} Δ → Γ ++ → (Γ +++ Δ) ++
  Wc {Γ} Δ ε++ = ε++
  Wc {Γ} Δ (Δ' ▻++ T) = Wc {Γ} Δ Δ' ▻++ Wₙ* {Γ} Δ Δ' T

  Wₙ* : ∀ {Γ} (Δ : Γ ++) (Δ' : Γ ++) → Type (Γ +++ Δ') → Type (Γ +++ Δ +++ Wc Δ Δ')
  Wₙ* _ _ U = U
  Wₙ* {Γ} Δ Δ' (‘Π’ T T₁) = ‘Π’ (Wₙ* {Γ} Δ Δ' T) (Wₙ* {Γ} Δ (Δ' ▻++ T) T₁)

  Wₙ : ∀ {Γ} A (Δ : (Γ ▻ A) ++) → Type Γ → Type (Γ ▻ A +++ Δ)
  Wₙ {Γ} A Δ T = let WT : Type (Γ ▻ A)
                     WT = Wₙ* {Γ} (ε++ ▻++ A) ε++ T
                 in Wₙ* {Γ ▻ A} Δ ε++ WT

  invert▻ : ∀ {Γ Γ' x x'} → (Γ ▻ x) ≡ (Γ' ▻ x') → Σ (Γ ≡ Γ') (λ p → subst Type p x ≡ x')
  invert▻ refl = refl , refl

  elim▻≡ : ∀ {ℓ} {Γ x} (P : ∀ Γ' x' → (p : Γ ≡ Γ') → subst Type p x ≡ x' → Set ℓ)
    → P Γ x refl refl
    → ∀ {Γ' x'} → (p : (Γ ▻ x) ≡ (Γ' ▻ x')) → P Γ' x' (Σ.proj₁ (invert▻ p)) (Σ.proj₂ (invert▻ p))
  elim▻≡ P k refl = k

  invert▻≡ : ∀ {Γ Γ' x x'} → (p : (Γ ▻ x) ≡ (Γ' ▻ x')) → cong₂-dep _▻_ (Σ.proj₁ (invert▻ p)) (Σ.proj₂ (invert▻ p)) ≡ p
  invert▻≡ refl = refl

  split-▻-+++ : ∀ Γ A Δ Γ' Δ'
    → (Γ ▻ A +++ Δ) ≡ (Γ' +++ Δ')
    → (Σ _ (λ Δ'' → (Γ ▻ A +++ Δ'') ≡ Γ')) ⊎ Σ _ (λ Δ'' → Γ ≡ (Γ' +++ Δ''))
  split-▻-+++ Γ A Δ .(Γ ▻' A +++ Δ) ε++ refl = inj₁ (Δ , refl)
  split-▻-+++ .(Γ' +++ Δ') A ε++ Γ' (Δ' ▻++ .A) refl = inj₂ (Δ' , refl)
  split-▻-+++ Γ A (Δ ▻++ x) Γ' (Δ' ▻++ x₁) H = split-▻-+++ Γ A Δ Γ' Δ' (Σ.proj₁ (invert▻ H))

  Wₙ*Wₙ*0T : Set _
  Wₙ*Wₙ*0T = ∀ {Γ} Δ Δ' A
    → ((Wₙ* {Γ} Δ Δ' A)
      ≡ (Wₙ* {Γ +++ Δ +++ Wc {Γ} Δ Δ'} ε++ ε++ (Wₙ* {Γ} Δ Δ' A)))

  Wₙ*Wₙ*0 : Wₙ*Wₙ*0T
  Wₙ*Wₙ*0 Δ Δ' U = refl
  Wₙ*Wₙ*0 {Γ} Δ Δ' (‘Π’ A A₁) = cong₂-dep ‘Π’ (Wₙ*Wₙ*0 Δ Δ' A) {!!}
{-    where helper : subst (λ z → Type ((Γ +++ Δ +++ Wc {Γ} {Δ} Δ') ▻ z)) (Wₙ*Wₙ*0 Δ Δ' A)
                   (Wₙ* {Γ} Δ {Δ' ▻++ A} A₁)
                     ≡ Wₙ* {{!!}} {ε++ _} {{!ε++ _!}} (Wₙ* {{!!}} {{!!}} {{!!}} A₁)
          helper = {!!}-}

  wₙ*' : ∀ {Γ} {Δ : Γ ++} {Δ' : Γ ++} {Γ'} {T : Type Γ'}
    → (H : Γ' ≡ (Γ +++ Δ'))
    → Term Γ' T
    → Term (Γ +++ Δ +++ Wc Δ Δ') (Wₙ* {Γ} Δ Δ' (subst Type H T))
  wₙ*' {Γ} {Δ} {Δ'} {Γ'} {._} H (‘λ’ {.Γ'} {A} {B} t) = helper H t
    where helper : ∀ {Γ} {Δ : Γ ++} {Δ' : Γ ++} {Γ'} {A : Type Γ'} {B : Type (Γ' ▻ A)}
                 → (H : Γ' ≡ (Γ +++ Δ'))
                 → Term (Γ' ▻ A) B
                 → Term (Γ +++ Δ +++ Wc {Γ} Δ Δ') (Wₙ* {Γ} Δ Δ' (subst Type H (‘Π’ A B)))
          helper {Γ} {Δ} {Δ'} {._} {A} {B} refl t = ‘λ’ (wₙ*' {Γ} {Δ} {Δ' ▻++ A} {Γ +++ Δ' ▻++ A} {B} refl t)
  {-wₙ*' {Γ} {Δ} {ε++} {._} {._} H (varₙ {Γ''} {A''} {Δ'' ▻++ x}) = {!!}
  wₙ*' {Γ} {Δ} {Δ' ▻++ x} {._} {._} H (varₙ {Γ''} {A''} {Δ'' ▻++ y}) = subst (Term ((Γ +++ Δ +++ Wc Δ Δ') ▻ Wₙ* Δ Δ' x)) {!!} {!helper'!}
    where helper : Term (Γ +++ Δ +++ Wc Δ Δ')
                        (Wₙ* Δ Δ' (subst Type (proj₁ (invert▻ H)) (Wₙ A'' Δ'' A'')))
          helper = wₙ*' {Γ} {Δ} {Δ'} {_} {_} (Σ.proj₁ (invert▻ H)) (varₙ {Γ''} {A''} {Δ''})

          helper' : Term
                      ((Γ +++ Δ +++ Wc Δ Δ') ▻ Wₙ* Δ Δ' x)
                      (Wₙ* (ε++ ▻++ Wₙ* Δ Δ' x) ε++
                       ((Wₙ* Δ Δ' (subst Type (proj₁ (invert▻ H)) (Wₙ A'' Δ'' A'')))))
          helper' = wₙ*' {Γ +++ Δ +++ Wc Δ Δ'} {ε++ ▻++ Wₙ* Δ Δ' x} {ε++} {Γ +++ Δ +++ Wc Δ Δ'} {Wₙ* Δ Δ' (subst Type (proj₁ (invert▻ H)) (Wₙ A'' Δ'' A''))} refl helper
  wₙ*' {Γ} {Δ} {Δ'} {._} {._} H (varₙ {Γ''} {A''} {ε++}) = {!!}-}
  wₙ*' {Γ} {Δ} {Δ'} {._} {._} H (varₙ {Γ''} {A''} {Δ''}) = helper {Γ} {Δ} {Δ'} {Γ''} {A''} {Δ''} ε++ ε++ H (ε++≡ε++ H)
    where ε++≡ε++ : ∀ {A B} (H : A ≡ B) → subst _++ H ε++ ≡ ε++
          ε++≡ε++ refl = refl

          helper' : ∀ {Γ} {Δ : Γ ++} {Δ'} {x} {Γ''} {A''} {Δ''} {x₁}
                  → (H₀ : (Γ'' ▻ A'' +++ Δ'') ≡ (Γ +++ Δ'))
                  → (H₁ : subst Type H₀ x₁ ≡ x)
                  → Term ((Γ +++ Δ +++ Wc {Γ} Δ Δ') ▻ Wₙ* {Γ} Δ Δ' x)
                         (Wₙ* {Γ} Δ (Δ' ▻++ x) (subst Type (cong₂-dep _▻_ H₀ H₁) (Wₙ {Γ''} A'' (Δ'' ▻++ x₁) A'')))
          helper' H₀ refl = {!!}

          make-H : ∀ {Γ} {Δ : Γ ++} {Δ' : Γ ++} {Γ''} {A''} {Δ''}
                 → (extraΔ'' : (Γ'' ▻ A'' +++ Δ'') ++)
                 → (extraΔ' : (Γ +++ Δ') ++)
                 → (H : (Γ'' ▻ A'' +++ Δ'') ≡ (Γ +++ Δ'))
                 → (extraΔ≡ : subst _++ H extraΔ'' ≡ extraΔ')
                 → (Γ'' ▻ A'' +++ (Δ'' ++++ extraΔ'')) ≡ (Γ +++ (Δ' ++++ extraΔ'))
          make-H ε++ ε++ H₁ extraΔ≡ = H₁
          make-H {Δ' = Δ'} {Δ'' = Δ''} extraΔ'' extraΔ' H₁ extraΔ≡ = trans (sym (++++-assoc Δ'' extraΔ'')) (trans (cong₂-dep _+++_ H₁ extraΔ≡) (++++-assoc Δ' extraΔ'))

          helper : ∀ {Γ} {Δ : Γ ++} {Δ' : Γ ++} {Γ''} {A''} {Δ''}
                 → (extraΔ'' : (Γ'' ▻ A'' +++ Δ'') ++)
                 → (extraΔ' : (Γ +++ Δ') ++)
                 → (H : (Γ'' ▻ A'' +++ Δ'') ≡ (Γ +++ Δ'))
                 → (extraΔ≡ : subst _++ H extraΔ'' ≡ extraΔ')
                 → Term (Γ +++ Δ +++ Wc {Γ} Δ (Δ' ++++ extraΔ')) (Wₙ* {Γ} Δ (Δ' ++++ extraΔ') (subst Type (make-H {Γ} {Δ} {Δ'} {Γ''} {A''} {Δ''} extraΔ'' extraΔ' H extraΔ≡) (Wₙ {Γ''} A'' (Δ'' ++++ extraΔ'') A'')))
          helper {._} {Δ} {Δ' = ε++} {Γ''} {A''} {Δ''} extraΔ .extraΔ refl refl = {!!}
            where helper'' : Term (Γ'' ▻ A'' +++ (Δ'' ++++ Δ)) (Wₙ A'' (Δ'' ++++ Δ) A'')
                  helper'' = varₙ {Γ''} {A''} {Δ'' ++++ Δ}
          helper {Γ} {Δ} {Δ' = Δ''' ▻++ A''} {.(Γ +++ Δ''')} {.A''} {Δ'' = ε++} extraΔ .extraΔ refl refl = {!!}
            where helper'' : {!!}
                  helper'' = varₙ {Γ +++ Δ +++ Wc Δ Δ'''} {Wₙ* {Γ} Δ Δ''' A''} {{!!}}
          helper {Γ} {Δ} {Δ' = Δ''' ▻++ x} {Γ''} {A''} {Δ'' = Δ'''' ▻++ x₁} extraΔ'' extraΔ H₁ extraΔ≡
            = {!subst
                (λ H₂ →
                   Term ((Γ +++ Δ +++ Wc {Γ} Δ Δ''') ▻ Wₙ* {Γ} Δ Δ''' x)
                   (Wₙ* {Γ} Δ (Δ''' ▻++ x)
                    (subst Type H₂ (Wₙ {Γ''} A'' (Δ'''' ▻++ x₁) A''))))
                (invert▻≡ H₁)
                (helper' {Γ} {Δ} {Δ'''} {x} {Γ''} {A''} {Δ''''} {x₁}
                 (proj₁ (invert▻ H₁)) (proj₂ (invert▻ H₁)))!}
          {-helper {.(Γ'' ▻ A'' +++ Δ'')} {ε++} {ε++} {Γ''} {A''} {Δ''} refl = helper''' -- varₙ {Γ''} {A''} {Δ''}
            where helper'' : Term (Γ'' ▻ A'' +++ Δ'') (Wₙ _ _ A'')
                  helper'' = varₙ {Γ''} {A''} {Δ''}

                  helper''' : Term
                                (Γ'' ▻ A'' +++ Δ'')
                                (Wₙ* {Γ'' ▻ A'' +++ Δ''} ε++ ε++ (Wₙ {Γ''} A'' Δ'' A''))
                  helper''' = {!!}
          helper {.(Γ'' ▻ A'' +++ Δ'')} {Δ ▻++ X} {ε++} {Γ''} {A''} {Δ''} refl = {!varₙ {Γ''} {A''} {Δ''}!}
            where helper'' : {!!}
                  helper'' = {!!}
          helper {Γ} {Δ} {Δ' = Δ''' ▻++ x} {.(Γ +++ Δ''')} {.x} {Δ'' = ε++} refl = {!!}
            where helper'' : {!!}
                  helper'' = {!!}
          helper {Γ} {Δ} {Δ' = Δ''' ▻++ x} {Γ''} {A''} {Δ'' = Δ'''' ▻++ x₁} H₁
            = subst
                (λ H₂ →
                   Term ((Γ +++ Δ +++ Wc {Γ} Δ Δ''') ▻ Wₙ* {Γ} Δ Δ''' x)
                   (Wₙ* {Γ} Δ (Δ''' ▻++ x) (subst Type H₂ (Wₙ {Γ''} A'' (Δ'''' ▻++ x₁) A''))))
                (invert▻≡ H₁) (helper' {Γ} {Δ} {Δ'''} {x} {Γ''} {A''} {Δ''''} {x₁}
                                 (proj₁ (invert▻ H₁)) (proj₂ (invert▻ H₁)))-}

  wₙ* : ∀ {Γ} {Δ : Γ ++} {Δ' : Γ ++} {T}
    → Term (Γ +++ Δ') T
    → Term (Γ +++ Δ +++ Wc Δ Δ') (Wₙ* {Γ} Δ Δ' T)
  wₙ* t = wₙ*' refl t





{-
data Con : Set
data _++ : Con → Set

data Ty (Γ : Con) : Set
data Var : ∀ Γ → Ty Γ → Set
data Tm (Γ : Con) : Ty Γ → Set
-}

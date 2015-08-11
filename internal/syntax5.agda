{-# OPTIONS --without-K #-}
module syntax5 where
open import Relation.Binary.PropositionalEquality

cong₂-dep : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
            (f : (x : A) → B x → C) {x y u v} → (H : x ≡ y) → subst _ H u ≡ v → f x u ≡ f y v
cong₂-dep f refl H = cong (f _) H

infixl 4 _▻_
infixl 4 _▻'_
infixl 4 _◅++_
infixl 4 _▻++_
infixl 4 _▻++'_
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
    ε++ : ∀ {Γ} → Γ ++
    _▻++_ : ∀ {Γ} (Δ : Γ ++) → Type (Γ +++ Δ) → Γ ++

  _+++_ : ∀ Γ → Γ ++ → Context
  Γ +++ ε++ = Γ
  Γ +++ (Δ ▻++ x) = (Γ +++ Δ) ▻ x

  data Type (Γ : Context) : Set where
    U : Type Γ
    ‘Π’ : ∀ A → Type (Γ ▻ A) → Type Γ

  _▻_ : (Γ : Context) → Type Γ → Context
  _▻_ = _▻'_

  _▻++'_ : ∀ {Γ} (Δ : Γ ++) → Type (Γ +++ Δ) → Γ ++
  _▻++'_ = _▻++_

  subst-Type : ∀ {A B} (H : A ≡ B) → Type A → Type B
  subst-Type H U = U
  subst-Type H (‘Π’ t t₁) = ‘Π’ (subst-Type H t) (subst-Type (cong₂-dep _▻_ H (subst-Type≡ H t)) t₁)

  subst--Type≡ : ∀ {A X Y} (H : X ≡ Y) t
    → subst (λ z → Type (A ▻ z)) H t ≡
      subst Type (cong (λ x → A ▻ x) H) t
  subst--Type≡ refl t = refl

  subst-Type≡ : ∀ {A B} (H : A ≡ B) (t : Type A) → subst Type H t ≡ subst-Type H t
  subst-Type≡ refl U = refl
  subst-Type≡ refl (‘Π’ t t₁) = cong₂-dep ‘Π’ (subst-Type≡ refl t) (trans (subst--Type≡ (subst-Type≡ refl t) t₁) (subst-Type≡ (cong (λ x → _ ▻ x) (subst-Type≡ refl t)) t₁))


  _◅++_ : ∀ {Γ} (A : Type Γ) (Δ : (Γ ▻ A) ++) → Γ ++
  A ◅++ ε++ = ε++ ▻++ A
  A ◅++ (Δ ▻++ x) = A ◅++ Δ ▻++ subst-Type (◅++-≡ _ A Δ) x

  ◅++-≡ : ∀ Γ A Δ → ((Γ ▻ A) +++ Δ) ≡ (Γ +++ A ◅++ Δ)
  ◅++-≡ Γ A ε++ = refl
  ◅++-≡ Γ A (Δ ▻++ x) = cong₂-dep _▻_ (◅++-≡ Γ A Δ) (subst-Type≡ (◅++-≡ Γ A Δ) x)

  _▻+++_ : ∀ {Γ Δ} (Δ' : (Γ +++ Δ) ++) → Type (Γ +++ Δ +++ Δ') → Γ ++
  _▻+++_ {Δ = ε++} Δ' T = Δ' ▻++ T
  _▻+++_ {Δ = Δ ▻++ x} Δ' T = _▻+++_ {Δ = Δ} (x ◅++ Δ') (subst-Type (◅++-≡ _ x Δ') T)

  _++++_ : ∀ {Γ} → (Δ : Γ ++) → (Γ +++ Δ) ++ → Γ ++
  Δ ++++ (ε++) = Δ
  _++++_ {Γ} Δ (Δ' ▻++ x) = (_++++_ {Γ} Δ Δ') ▻++ subst-Type (++++-assoc Δ Δ') x
  --ε++ ++++ Δ' = Δ'
  --Δ ▻++ x ++++ Δ' = Δ ++++ x ◅++ Δ'

  ++++-assoc : ∀ {Γ} Δ Δ' → (Γ +++ Δ +++ Δ') ≡ (Γ +++ (Δ ++++ Δ'))
  ++++-assoc Δ (ε++) = refl
  ++++-assoc Δ (Δ' ▻++ x) = cong₂-dep _▻_ (++++-assoc Δ Δ') (subst-Type≡ (++++-assoc Δ Δ') x)

  Wcₙ : ∀ {Γ A} → Γ ++ → (Γ ▻ A) ++
  Wcₙ {Γ} {A} ε++ = ε++
  Wcₙ {Γ} {A} (Δ ▻++ T) = Wcₙ {Γ} {A} Δ ▻++ Wₙ {Γ} A Δ T

  Wc+ₙ : ∀ {Γ} A Δ → (Γ +++ Δ) ++ → (Γ ▻ A +++ Wcₙ Δ) ++
  Wc+ₙ {Γ} A Δ (ε++) = ε++
  Wc+ₙ {Γ} A Δ (Δ' ▻++ T) = (Wc+ₙ {Γ} A Δ Δ') ▻++ subst-Type (WcₙWc+ₙ≡ A Δ Δ') (Wₙ {Γ} A (Δ ++++ Δ') (subst-Type (++++-assoc Δ Δ') T))

  WcₙWc+ₙ≡ : ∀ {Γ} A Δ Δ' → (Γ ▻ A +++ Wcₙ {Γ} {A} (Δ ++++ Δ')) ≡ (Γ ▻ A +++ Wcₙ {Γ} {A} Δ +++ Wc+ₙ {Γ} A Δ Δ')
  WcₙWc+ₙ≡ A Δ (ε++) = refl
  WcₙWc+ₙ≡ A Δ (Δ' ▻++ x) = cong₂-dep _▻_ (WcₙWc+ₙ≡ A Δ Δ') (subst-Type≡ (WcₙWc+ₙ≡ A Δ Δ') _)

  Wₙ : ∀ {Γ} A (Δ : Γ ++) → Type (Γ +++ Δ) → Type (Γ ▻ A +++ Wcₙ {Γ} {A} Δ)
  Wₙ _ _ U = U
  Wₙ {Γ} A Δ (‘Π’ T T₁) = ‘Π’ (Wₙ {Γ} A Δ T) (Wₙ {Γ} A (Δ ▻++ T) T₁)

  U' : ∀ {Γ} → Type Γ
  U' = U

  ‘Π’' : ∀ {Γ} → ∀ A → Type (Γ ▻ A) → Type Γ
  ‘Π’' = ‘Π’

  subst-Type-U : ∀ {Γ Γ'} (f : Context → Context) (H : Γ ≡ Γ') → subst (λ t → Type (f t)) H U' ≡ U'
  subst-Type-U f refl = refl

  subst-Type-Π : ∀ {Γ Γ' A B} (H : Γ ≡ Γ') → subst Type H (‘Π’' A B) ≡ ‘Π’' (subst Type H A) (subst Type (cong₂-dep _▻_ H refl) B)
  subst-Type-Π refl = refl

  Wₙ-exch≡T : Set _
  Wₙ-exch≡T = ∀ {Γ₀} A Γ₁ B Γ₂
    → ((Γ₀ ▻ A +++ Wcₙ Γ₁) ▻ Wₙ {Γ₀} A Γ₁ B +++ Wcₙ (Wc+ₙ {Γ₀} A Γ₁ Γ₂))
      ≡ (Γ₀ ▻ A +++ Wcₙ (Γ₁ ▻++ B ++++ Wcₙ Γ₂))

  Wₙ-exch≡ : Wₙ-exch≡T
  Wₙ-exch≡ A Γ₁ B ε++ = refl
  Wₙ-exch≡ A Γ₁ B (Γ₂ ▻++ x) = cong₂-dep _▻_ (Wₙ-exch≡ A Γ₁ B Γ₂) (trans (subst-Type≡ (Wₙ-exch≡ A Γ₁ B Γ₂) _) (helper'''' Γ₂ x))
    where
      helper'''' : ∀ Γ₃ x → subst-Type (Wₙ-exch≡ A Γ₁ B Γ₃)
                                  (Wₙ (Wₙ A Γ₁ B) (Wc+ₙ A Γ₁ Γ₃)
                                  (subst-Type (WcₙWc+ₙ≡ A Γ₁ Γ₃)
                                  (Wₙ A (Γ₁ ++++ Γ₃) (subst-Type (++++-assoc Γ₁ Γ₃) x))))
                                  ≡
                                  Wₙ A (Γ₁ ▻++ B ++++ Wcₙ Γ₃)
                                  (subst-Type (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₃)) (Wₙ B Γ₃ x))
      helper'''' Γ₃ U = refl
      helper'''' Γ₃ (‘Π’ x x₁)
        = (cong₂-dep ‘Π’ (helper'''' Γ₃ x) ({!!}))
        {-where helper''''' : subst (λ z → Type ((.Γ₀ ▻ A +++ Wcₙ (Γ₁ ▻++ B ++++ Wcₙ Γ₃)) ▻ z))
(helper'''' Γ₃ x)
(subst-Type
 (cong₂-dep _▻_ (Wₙ-exch≡ A Γ₁ B Γ₃)
  (subst-Type≡ (Wₙ-exch≡ A Γ₁ B Γ₃)
   (Wₙ (Wₙ A Γ₁ B) (Wc+ₙ A Γ₁ Γ₃)
    (subst-Type (WcₙWc+ₙ≡ A Γ₁ Γ₃)
     (Wₙ A (Γ₁ ++++ Γ₃) (subst-Type (++++-assoc Γ₁ Γ₃) x))))))
 (Wₙ (Wₙ A Γ₁ B)
  (Wc+ₙ A Γ₁ Γ₃ ▻++
   subst-Type (WcₙWc+ₙ≡ A Γ₁ Γ₃)
   (Wₙ A (Γ₁ ++++ Γ₃) (subst-Type (++++-assoc Γ₁ Γ₃) x)))
  (subst-Type
   (cong₂-dep _▻_ (WcₙWc+ₙ≡ A Γ₁ Γ₃)
    (subst-Type≡ (WcₙWc+ₙ≡ A Γ₁ Γ₃)
     (Wₙ A (Γ₁ ++++ Γ₃) (subst-Type (++++-assoc Γ₁ Γ₃) x))))
   (Wₙ A ((Γ₁ ++++ Γ₃) ▻++ subst-Type (++++-assoc Γ₁ Γ₃) x)
    (subst-Type
     (cong₂-dep _▻_ (++++-assoc Γ₁ Γ₃)
      (subst-Type≡ (++++-assoc Γ₁ Γ₃) x))
     x₁)))))
≡
Wₙ A
((Γ₁ ▻++ B ++++ Wcₙ Γ₃) ▻++
 subst-Type (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₃)) (Wₙ B Γ₃ x))
(subst-Type
 (cong₂-dep _▻_ (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₃))
  (subst-Type≡ (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₃)) (Wₙ B Γ₃ x)))
 (Wₙ B (Γ₃ ▻++ x) x₁))-}
{-subst-Type (cong₂-dep _▻_ (Wₙ-exch≡ A Γ₁ B Γ₃) (trans (subst-Type≡ (Wₙ-exch≡ A Γ₁ B Γ₃) _) (helper'''' Γ₃ x)))
                              (Wₙ (Wₙ A Γ₁ B) (Wc+ₙ A Γ₁ (Γ₃ ▻++ x))
                               (subst-Type (WcₙWc+ₙ≡ A Γ₁ (Γ₃ ▻++ x))
                                (Wₙ A (Γ₁ ++++ Γ₃ ▻++ x)
                                 (subst-Type (++++-assoc Γ₁ (Γ₃ ▻++ x)) x₁))))
                              ≡
                              Wₙ A (Γ₁ ▻++ B ++++ Wcₙ (Γ₃ ▻++ x))
                              (subst-Type (++++-assoc (Γ₁ ▻++ B) (Wcₙ (Γ₃ ▻++ x)))
                               (Wₙ B (Γ₃ ▻++ x) x₁))
              helper''''' = helper'''' (Γ₃ ▻++ x) x₁-}

  Wₙ-exchT : Set _
  Wₙ-exchT = ∀ {Γ₀} A Γ₁ B Γ₂ (T : Type (Γ₀ +++ Γ₁ +++ Γ₂))
    → let WTa : Type (Γ₀ ▻ A +++ Wcₙ (Γ₁ ++++ Γ₂))
          WTa = Wₙ {Γ₀} A (Γ₁ ++++ Γ₂) (subst Type (++++-assoc Γ₁ Γ₂) T)
          WTba : Type ((Γ₀ ▻ A +++ Wcₙ Γ₁) ▻ Wₙ {Γ₀} A Γ₁ B +++ Wcₙ (Wc+ₙ {Γ₀} A Γ₁ Γ₂))
          WTba = Wₙ {Γ₀ ▻ A +++ Wcₙ {Γ₀} {A} Γ₁} (Wₙ {Γ₀} A Γ₁ B) (Wc+ₙ {Γ₀} A Γ₁ Γ₂) (subst Type (WcₙWc+ₙ≡ {Γ₀} A Γ₁ Γ₂) WTa)

          WTb : Type (Γ₀ +++ (Γ₁ ▻++ B) +++ Wcₙ Γ₂)
          WTb = Wₙ {Γ₀ +++ Γ₁} B Γ₂ T
          WTb' : Type (Γ₀ +++ (Γ₁ ▻++ B ++++ Wcₙ Γ₂))
          WTb' = subst Type (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₂)) WTb
          WTab : Type (Γ₀ ▻ A +++ Wcₙ (Γ₁ ▻++ B ++++ Wcₙ Γ₂))
          WTab = Wₙ {Γ₀} A (Γ₁ ▻++ B ++++ Wcₙ Γ₂) WTb'
      in subst Type (Wₙ-exch≡ A Γ₁ B Γ₂) WTba ≡ WTab

  Wₙ-exchT' : Set _
  Wₙ-exchT' = ∀ {Γ₀} A Γ₁ B Γ₂ (T : Type (Γ₀ +++ Γ₁ +++ Γ₂))
    → let WTa : Type (Γ₀ ▻ A +++ Wcₙ (Γ₁ ++++ Γ₂))
          WTa = Wₙ {Γ₀} A (Γ₁ ++++ Γ₂) (subst-Type (++++-assoc Γ₁ Γ₂) T)
          WTba : Type ((Γ₀ ▻ A +++ Wcₙ Γ₁) ▻ Wₙ {Γ₀} A Γ₁ B +++ Wcₙ (Wc+ₙ {Γ₀} A Γ₁ Γ₂))
          WTba = Wₙ {Γ₀ ▻ A +++ Wcₙ {Γ₀} {A} Γ₁} (Wₙ {Γ₀} A Γ₁ B) (Wc+ₙ {Γ₀} A Γ₁ Γ₂) (subst-Type (WcₙWc+ₙ≡ {Γ₀} A Γ₁ Γ₂) WTa)

          WTb : Type (Γ₀ +++ (Γ₁ ▻++ B) +++ Wcₙ Γ₂)
          WTb = Wₙ {Γ₀ +++ Γ₁} B Γ₂ T
          WTb' : Type (Γ₀ +++ (Γ₁ ▻++ B ++++ Wcₙ Γ₂))
          WTb' = subst-Type (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₂)) WTb
          WTab : Type (Γ₀ ▻ A +++ Wcₙ (Γ₁ ▻++ B ++++ Wcₙ Γ₂))
          WTab = Wₙ {Γ₀} A (Γ₁ ▻++ B ++++ Wcₙ Γ₂) WTb'
      in subst-Type (Wₙ-exch≡ A Γ₁ B Γ₂) WTba ≡ WTab

  {-helperT : Set _
  helperT = ∀ {Γ₀} A Γ₁ B Γ₂ T T₁
    → let k : Type (Γ₀ ▻ A +++ Wcₙ (Γ₁ ▻++ B ++++ Wcₙ (Γ₂ ▻++ T)))
          k = Wₙ {Γ₀} A
            ((Γ₁ ▻++ B ++++ Wcₙ (Γ₂ ▻++ T)))
            (subst-Type (++++-assoc (Γ₁ ▻++ B) (Wcₙ (Γ₂ ▻++ T)))
            (Wₙ B (Γ₂ ▻++ T) T₁))
      in subst
           (λ t →
              Type
              ((Γ₀ ▻ A +++ Wcₙ (Γ₁ ▻++ B ++++ Wcₙ Γ₂)) ▻
               Wₙ A (Γ₁ ▻++ B ++++ Wcₙ Γ₂) t))
           (subst-Type≡ (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₂)) (Wₙ B Γ₂ T)) k
        ≡
        Wₙ {Γ₀} A
        ((Γ₁ ▻++ B ++++ Wcₙ Γ₂) ▻++
         subst-Type (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₂)) (Wₙ B Γ₂ T))
        (subst-Type (cong₂-dep _▻_ (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₂)) (subst-Type≡ (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₂)) (Wₙ B Γ₂ T)))
         (Wₙ B (Γ₂ ▻++ T) T₁))
  helper-Wₙ : helperT
  helper-Wₙ A Γ₁ B Γ₂ T U = {!!}
  helper-Wₙ A Γ₁ B Γ₂ T (‘Π’ T₁ T₂) = {!!}-}

  Wₙ-exch' : Wₙ-exchT'
  Wₙ-exch' A Γ₁ B Γ₂ U = refl
  Wₙ-exch' A Γ₁ B Γ₂ (‘Π’ T T₁) = cong₂-dep ‘Π’ (Wₙ-exch' A Γ₁ B Γ₂ T) {!!}

  {-Wₙ-exch : Wₙ-exchT
  Wₙ-exch {Γ₀} A Γ₁ B Γ₂ U
    = trans (cong
               (λ U'' →
                  subst Type (Wₙ-exch≡ A Γ₁ B Γ₂)
                  (Wₙ (Wₙ A Γ₁ B) (Wc+ₙ A Γ₁ Γ₂)
                   (subst Type (WcₙWc+ₙ≡ A Γ₁ Γ₂) (Wₙ A (Γ₁ ++++ Γ₂) U''))))
               (subst-Type-U (++++-assoc Γ₁ Γ₂)))
            (trans (cong
                      (λ U'' →
                         subst Type (Wₙ-exch≡ A Γ₁ B Γ₂)
                         (Wₙ (Wₙ A Γ₁ B) (Wc+ₙ A Γ₁ Γ₂) U''))
                      (subst-Type-U (WcₙWc+ₙ≡ A Γ₁ Γ₂)))
                   (trans (subst-Type-U (Wₙ-exch≡ A Γ₁ B Γ₂))
                          (sym (trans (cong (λ U'' → Wₙ A (Γ₁ ▻++ B ++++ Wcₙ Γ₂) U'') (subst-Type-U (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₂))))
                                      refl))))
  --Wₙ-exch A Γ₁ B ε++ (‘Π’ T T₁) = cong₂-dep ‘Π’ (Wₙ-exch A Γ₁ B ε++ T) (trans {!!} (Wₙ-exch A Γ₁ B (ε++ ▻++ T) T₁))
  Wₙ-exch {Γ₀} A Γ₁ B Γ₂ (‘Π’ T T₁) = sym (trans (cong (λ p → Wₙ A (Γ₁ ▻++ B ++++ Wcₙ Γ₂) p)
                    (subst-Type-Π (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₂))))
      (trans
         (sym
          (cong₂-dep ‘Π’ (Wₙ-exch A Γ₁ B Γ₂ T) (trans (helper T₁) (Wₙ-exch A Γ₁ B (Γ₂ ▻++ T) T₁))))
      (sym (trans (cong
                     (λ p →
                        subst Type (Wₙ-exch≡ A Γ₁ B Γ₂)
                        (Wₙ (Wₙ A Γ₁ B) (Wc+ₙ A Γ₁ Γ₂)
                         (subst Type (WcₙWc+ₙ≡ A Γ₁ Γ₂) (Wₙ A (Γ₁ ++++ Γ₂) p))))
                     (subst-Type-Π (++++-assoc Γ₁ Γ₂)))
           (trans
              (cong
               (λ p →
                  subst Type (Wₙ-exch≡ A Γ₁ B Γ₂)
                  (Wₙ (Wₙ A Γ₁ B) (Wc+ₙ A Γ₁ Γ₂) p))
               (subst-Type-Π (WcₙWc+ₙ≡ A Γ₁ Γ₂)))
              (trans (subst-Type-Π (Wₙ-exch≡ A Γ₁ B Γ₂))
           (cong₂-dep ‘Π’ refl refl)))))))
      where helper : ∀ T₁ → subst (λ z → Type ((Γ₀ ▻ A +++ Wcₙ (Γ₁ ▻++ B ++++ Wcₙ Γ₂)) ▻ z))
                       (Wₙ-exch A Γ₁ B Γ₂ T)
                       (subst (λ z → Type ((Γ₀ ▻ A +++ Wcₙ (Γ₁ ▻++ B ++++ Wcₙ Γ₂)) ▻ z))
                        refl
                        (subst Type (cong₂-dep _▻_ (Wₙ-exch≡ A Γ₁ B Γ₂) refl)
                         (Wₙ (Wₙ A Γ₁ B)
                          (Wc+ₙ A Γ₁ Γ₂ ▻++
                           subst Type (WcₙWc+ₙ≡ A Γ₁ Γ₂)
                           (Wₙ A (Γ₁ ++++ Γ₂) (subst Type (++++-assoc Γ₁ Γ₂) T)))
                          (subst Type (cong₂-dep _▻_ (WcₙWc+ₙ≡ A Γ₁ Γ₂) refl)
                           (Wₙ A ((Γ₁ ++++ Γ₂) ▻++ subst Type (++++-assoc Γ₁ Γ₂) T)
                            (subst Type (cong₂-dep _▻_ (++++-assoc Γ₁ Γ₂) refl) T₁))))))
                       ≡
                       subst Type (Wₙ-exch≡ A Γ₁ B (Γ₂ ▻++ T))
                       (Wₙ (Wₙ A Γ₁ B) (Wc+ₙ A Γ₁ (Γ₂ ▻++ T))
                        (subst Type (WcₙWc+ₙ≡ A Γ₁ (Γ₂ ▻++ T))
                         (Wₙ A (Γ₁ ++++ Γ₂ ▻++ T)
                          (subst Type (++++-assoc Γ₁ (Γ₂ ▻++ T)) T₁))))
            helper U = {!!}
            helper (‘Π’ T₂ T₃) = {!!}
 {-

           (sym (trans (sym (Wₙ-exch A Γ₁ B (Γ₂ ▻++ T) T₁)) {!!}))))
         {!!}))
-}
 {-         (trans (subst-Type-Π (Wₙ-exch≡ A Γ₁ B Γ₂ (‘Π’ T T₁)))
                          (sym (trans (cong (λ p → Wₙ A (Γ₁ ▻++ B ++++ Wcₙ Γ₂) p)
                                         (subst-Type-Π (++++-assoc (Γ₁ ▻++ B) (Wcₙ Γ₂))))
                                      (trans {!(cong₂-dep ‘Π’ (trans (Wₙ-exch {Γ₀ A Γ₁ B Γ₂ T}) {!!}) {!!})!} {!!})))))-}

  data Var : ∀ Γ → Type Γ → Set where
    vz : ∀ {Γ T}             → Var (Γ ▻ T) (Wₙ {Γ} T ε++ T)
    vs : ∀ {Γ T A} → Var Γ T → Var (Γ ▻ A) (Wₙ {Γ} A ε++ T)

  data Term : ∀ Γ → Type Γ → Set where
    ‘λ’ : ∀ {Γ A B} → Term (Γ ▻ A) B → Term Γ (‘Π’ A B)
    varₙ : ∀ {Γ A} → Var Γ A → Term Γ A
{-
  Wc* : ∀ {Γ Δ} → Γ ++ → (Γ +++ Δ) ++
  Wc* {Γ} {Δ} ε++ = ε++
  Wc* {Γ} {Δ} (Δ' ▻++ T) = Wc* {Γ} {Δ} Δ' ▻++ {!Wₙ* {Γ} {Δ} {Δ'} T!}
-}
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
          helper {Γ} {Δ} {Δ' = ε++} {Γ''} {A''} {Δ''} H = {!!}
          helper {Δ' = Δ''' ▻++ x} H₁ = {!!}-}





{-
data Con : Set
data _++ : Con → Set

data Ty (Γ : Con) : Set
data Var : ∀ Γ → Ty Γ → Set
data Tm (Γ : Con) : Ty Γ → Set
-}
-}

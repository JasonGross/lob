{-# OPTIONS --without-K #-}
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.Product
  using (_×_; Σ) renaming (_,_ to _,,_)
open import Data.Unit
open import Data.Maybe
open import Data.Empty
open import Relation.Nullary
open import Level

infixl 4 _,_
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

Wₙ : ∀ {Γ} (Δ : Γ ++) (A : Ty Γ) → Ty (++ Δ) → Ty (++ A cw Δ)

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

data Ty (Γ : Con) where
  U : Ty Γ
  ‘Π’ : ∀ A → Ty (Γ , A) → Ty Γ

data Var where
  vz : ∀ {Γ A}             → Var (Γ , A) (Wₙ (ε Γ) A A)
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ , B) (Wₙ (ε Γ) B A)

data Tm (Γ : Con) where
  ‘λ’ : ∀ {A B} → Tm (Γ , A) B → Tm Γ (‘Π’ A B)
  var : ∀ {A} → Var Γ A → Tm Γ A

subst-Var-Con : ∀ {Γ A Γ' A'} → _≡_ {lzero} {Con} (Γ , A) (Γ' , A') → Var Γ A → Var Γ' A'
subst-Var-Con refl v = v

mutual
  Var-code-helper : ∀ {Γ A Γ' A'} (B : Ty Γ) (B' : Ty Γ') (v1 : Var Γ A) (v2 : Var Γ' A')→ _≡_ {lzero} {Con} (Γ , A) (Γ' , A') → Set
  Var-code-helper B₁ B'' v3 v4 refl = B₁ ≡ B''

  Var-code : ∀ {Γ T Γ' T'} → Var Γ T → Var Γ' T' → Set
  Var-code {Γ , A} {._} {Γ' , A'} {._} vz vz = _≡_ {lzero} {Con} (Γ , A) (Γ' , A')
  Var-code vz _ = ⊥
  Var-code (vs {Γ} {A} {B} v1) (vs {Γ'} {A'} {B'} v2) = Σ (Var-code v1 v2) (λ c → Var-code-helper B B' v1 v2 (Var-decodeT {v₁ = v1} {v2} c))
  Var-code (vs v1) _ = ⊥

  Var-encode : ∀ {Γ T} {v₁ v₂ : Var Γ T} → v₁ ≡ v₂ → Var-code v₁ v₂
  Var-encode {v₁ = vz} refl = refl
  Var-encode {v₁ = vs v₁} refl = Var-encode {v₁ = v₁} refl ,, subst (λ p → Var-code-helper _ _ v₁ v₁ p) (Var-decodeTencode v₁) refl

  Var-decodeT-helper : ∀ {Γ A Γ' A'} B B' {v₁ : Var Γ A} {v₂ : Var Γ' A'} → (p : _≡_ {lzero} {Con} (Γ , A) (Γ' , A')) → (q : Var-code-helper B B' v₁ v₂ p) → _≡_ {lzero} {Con} (Γ , B , Wₙ (ε Γ) B A) (Γ' , B' , Wₙ (ε Γ') B' A')
  Var-decodeT-helper B₁ .B₁ refl refl = refl

  subst-Var-Con-vs : ∀ {Γ A Γ' A'} (B : Ty Γ) (B' : Ty Γ')
    → (v : Var Γ A) (v2 : Var Γ' A')
    → (p : _≡_ {lzero} {Con} (Γ , A) (Γ' , A'))
    → (q : Var-code-helper B B' v v2 p)
    → subst-Var-Con (Var-decodeT-helper B B' p q) (vs {Γ} {A} {B} v)
      ≡ vs {Γ'} {A'} {B'} (subst-Var-Con p v)
  subst-Var-Con-vs B .B v v2 refl refl = refl


  Var-decodeT : ∀ {Γ T Γ' T'} {v₁ : Var Γ T} {v₂ : Var Γ' T'} → Var-code v₁ v₂ → _≡_ {lzero} {Con} (Γ , T) (Γ' , T')
  Var-decodeT {v₁ = vz} {vz} refl = refl
  Var-decodeT {v₁ = vz} {vs v₂} ()
  Var-decodeT {v₁ = vs v₁} {vz} ()
  Var-decodeT {v₁ = vs {Γ} {A} {B} v₁} {vs {Γ'} {A'} {B'} v₂} (p ,, q) = Var-decodeT-helper B B' {v₁ = v₁} {v₂} (Var-decodeT {v₁ = v₁} {v₂} p) q

  Var-decodeTencode : ∀ {Γ T} (v₁ : Var Γ T) → refl ≡ Var-decodeT (Var-encode {v₁ = v₁} refl)
  Var-decodeTencode vz = refl
  Var-decodeTencode (vs {Γ} {A} {B} v) = helper (Var-decodeT {Γ} {A} {Γ} {A} {v} (Var-encode {Γ} {A} {v} refl)) (Var-decodeTencode {Γ} {A} v)
    where
      helper : ∀ (p : (Γ , A) ≡ (Γ , A)) (q : refl ≡ p) → refl ≡ Var-decodeT-helper B B p (subst (Var-code-helper B B v v) q refl)
      helper .refl refl = refl

  Var-decode : ∀ {Γ T Γ' T'} {v₁ : Var Γ T} {v₂ : Var Γ' T'} → (c : Var-code v₁ v₂) → _≡_ {lzero} {Var Γ' T'} (subst-Var-Con (Var-decodeT c) v₁) v₂
  Var-decode {v₁ = vz} {vz} refl = refl
  Var-decode {v₁ = vz} {vs v₂} ()
  Var-decode {v₁ = vs v₁} {vz} ()
  Var-decode {v₁ = vs {Γ} {A} {B} v₁} {vs {Γ'} {A'} {B'} v₂} (c₁ ,, c₂) = trans (subst-Var-Con-vs B B' v₁ v₂ (Var-decodeT c₁) c₂) helper
    where helper : vs {Γ'} {A'} {B'} (subst-Var-Con (Var-decodeT c₁) v₁) ≡ vs v₂
          helper = cong vs (Var-decode {Γ} {A} {Γ'} {A'} {v₁ = v₁} {v₂} c₁)



Wₙ Δ A U = U
Wₙ Δ A (‘Π’ ty ty') = ‘Π’ (Wₙ Δ A ty) (Wₙ (Δ , ty) A ty')

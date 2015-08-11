{-# OPTIONS --without-K #-}
open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.Nat
  using (ℕ; zero; suc) renaming (_⊔_ to _⊔ℕ_)
open import Data.Product
  using (_×_; Σ) renaming (_,_ to _,,_)
open import Data.Unit
open import Data.Maybe
open import Data.Empty
open import Relation.Nullary
open import Level

subst₂-dep : {a b p : Level} {A : Set a} {B : A → Set b} (P : (x : A) → B x → Set p)
  {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂} →
  (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
subst₂-dep P {x₁ = x₁} refl = subst (P x₁)

cong₂-dep : {a b p : Level} {A : Set a} {B : A → Set b} {R : Set p} (P : (x : A) → B x → R)
  {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂} →
  (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂ → P x₁ y₁ ≡ P x₂ y₂
cong₂-dep P {x₁ = x₁} refl = cong (P x₁)

{-# NON_TERMINATING #-}
undefined : ∀ {A : Set} → A
undefined = undefined

infixl 4 _,_
infix 5 _++
infix 5 ++_
infixl 10 _cw_

data Con : Set
data _++ : Con → Set

data Ty (Γ : Con) : (ℓ : ℕ) → Set
data Var : ∀ {ℓ} Γ → Ty Γ ℓ → Set
data Tm {ℓ : ℕ} (Γ : Con) : Ty Γ ℓ → Set

SemiDec = Maybe

SemiDecidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set (ℓ ⊔ (b ⊔ a))
SemiDecidable {A = A} {B = B} _~_ = ∀ (x : A) (y : B) → SemiDec (x ~ y)

postulate
  _≟c_ : SemiDecidable {A = Con} _≡_
  _≟t_ : ∀ {ℓ Γ T} → SemiDecidable {A = Tm {ℓ} Γ T} _≡_
  _≟T_ : ∀ {ℓ Γ} → SemiDecidable {A = Ty Γ ℓ} _≡_
  _≟v_ : ∀ {ℓ Γ T} → SemiDecidable {A = Var {ℓ} Γ T} _≡_

_▻'_ : ∀ {ℓ} Γ → Ty Γ ℓ → Con
ε' : ∀ Γ → Γ ++

++_ : ∀ {Γ} → Γ ++ → Con
_cw_ : ∀ {ℓ Γ} (A : Ty _ ℓ) → Γ ++ → (Γ ▻' A) ++

_▻_ : ∀ {ℓ Γ} (Δ : Γ ++) → Ty (++ Δ) ℓ → Γ ++

Wₙ : ∀ {ℓ ℓ′ Γ} (Δ : Γ ++) (A : Ty Γ ℓ) → Ty (++ Δ) ℓ′ → Ty (++ A cw Δ) ℓ′
wₙ : ∀ {ℓ ℓ′ Γ} (Δ : Γ ++) (B : Ty Γ ℓ) {A : Ty _ ℓ′} → Tm (++ Δ) A → Tm (++ B cw Δ) (Wₙ Δ B A)
vₙ : ∀ {ℓ ℓ′ Γ} (Δ : Γ ++) (B : Ty Γ ℓ) {A : Ty _ ℓ′} → Var (++ Δ) A → Var (++ (B cw Δ)) (Wₙ Δ B A)

data Con where
  ∅ : Con
  _,_ : ∀ {ℓ} Γ → Ty Γ ℓ → Con

_▻'_ = _,_

data _++ where
  ε : ∀ Γ → Γ ++
  _,_ : ∀ {ℓ Γ} (Δ : Γ ++) → Ty (++ Δ) ℓ → Γ ++

_▻_ = _,_
ε' = ε

++ ε Γ = Γ
++ (Δ , x) = ++ Δ , x

A cw ε Γ = ε (Γ , A)
A cw (Δ , x) = A cw Δ , Wₙ Δ A x

data Ty (Γ : Con) where
  U : ∀ ℓ → Ty Γ (Data.Nat.suc ℓ)
  El : ∀ {ℓ} → Tm Γ (U ℓ) → Ty Γ ℓ -- this constructor causes problems for termination of weakening
  ‘Π’ : ∀ {a b} (A : Ty Γ a) → Ty (Γ , A) b → Ty Γ (a ⊔ℕ b)
--  ‘Σ’ : ∀ A → Ty (Γ , A) → Ty Γ

data Var where
  vz : ∀ {ℓ Γ} {A : Ty _ ℓ}                          → Var (Γ , A) (Wₙ (ε Γ) A A)
  vs : ∀ {ℓ ℓ′ Γ} {A : Ty _ ℓ} {B : Ty _ ℓ′} → Var Γ A → Var (Γ , B) (Wₙ (ε Γ) B A)
  v⊥ : ∀ {ℓ Γ} {A : Ty _ ℓ}                          → Var Γ A

data Tm {ℓ : ℕ} (Γ : Con) where
  var : ∀ {A} → Var Γ A → Tm Γ A

lift-≟ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′}
  → (f : A → B)
  → {x x' : A}
  → SemiDec (x ≡ x')
  → SemiDec (f x ≡ f x')
lift-≟ f (just refl) = just refl
lift-≟ f nothing = nothing

subst-SemiDec : ∀ {ℓ ℓ′} {A : Set ℓ} (P : A → Set ℓ′)
  → {x y : A}
  → (x' : P x) (y' : P y)
  → SemiDec (x ≡ y)
  → Set ℓ′
subst-SemiDec P x' y' (just refl) = SemiDec (x' ≡ y')
subst-SemiDec P x' y' nothing = Lift ⊤

make-subst-SemiDec : ∀ {ℓ ℓ′} {A : Set ℓ} (P : A → Set ℓ′)
  → (∀ {x} → SemiDecidable {A = P x} _≡_)
  → {x y : A}
  → (x' : P x) (y' : P y)
  → (p : SemiDec (x ≡ y))
  → subst-SemiDec P x' y' p
make-subst-SemiDec P _≟_ _ _ (just refl) = _ ≟ _
make-subst-SemiDec P _≟_ _ _ nothing = lift tt

lift₂-≟ : ∀ {ℓ ℓ′ ℓ′′} {A : Set ℓ′} {B : A → Set ℓ′′} {R : Set ℓ}
  → (f : (x : A) → B x → R)
  → {x x' : A}
  → {y : B x} {y' : B x'}
  → (p : SemiDec (x ≡ x'))
  → (subst-SemiDec B y y' p)
  → SemiDec (f x y ≡ f x' y')
lift₂-≟ f (just refl) (just refl) = just refl
lift₂-≟ f (just refl) nothing = nothing
lift₂-≟ f nothing p₁ = nothing

{-∅ ≟c ∅ = just refl
∅ ≟c _ = nothing
(x , x₁) ≟c (y , x₂) = lift₂-≟ _,_ (_ ≟c _) (make-subst-SemiDec (λ Γ → Ty Γ _) _≟T_ x₁ x₂ (_ ≟c _))
(x , x₁) ≟c _ = nothing

U ≟T U = just refl
U ≟T _ = nothing
‘Π’ x x₁ ≟T ‘Π’ y y₁ with x ≟T y
‘Π’ x x₂ ≟T ‘Π’ .x y₁ | just refl with x₂ ≟T y₁
‘Π’ x x₂ ≟T ‘Π’ .x .x₂ | just refl | just refl = just refl
‘Π’ x x₂ ≟T ‘Π’ .x y₁ | just refl | nothing = nothing
‘Π’ x x₁ ≟T ‘Π’ y y₁ | nothing = nothing
‘Π’ x x₁ ≟T _ = nothing
El x ≟T El y with x ≟t y
El x ≟T El .x | just refl = just refl
El x ≟T El y | nothing = nothing
El x ≟T _ = nothing

-- ‘λ’ x ≟t ‘λ’ y = lift-≟ ‘λ’ (_ ≟t _)
-- ‘λ’ x ≟t _ = nothing
var x ≟t var x₁ = lift-≟ var {!_ ≟v _!}
-- var x ≟t _ = nothing

subst-Ty-U : ∀ {A B} (p : A ≡ B) → subst Ty p U ≡ U
subst-Ty-U refl = refl

{-module encode-decode
  {ℓ ℓ′ : Level}
  (A : Set ℓ)
  (code : A → A → Set ℓ′)
  (encode' : ∀ x → code x x)
  (decode' : ∀ x y (c : code x y) → x ≡ y)
  (code-contr : ∀ x y (c : code x y) → subst (code x) (decode' _ _ c) (encode' x) ≡ c)
  where

  encode : ∀ {x y} → x ≡ y → code x y
  encode {x} p = subst (code x) p (encode' x)

  decode : ∀ {x y} → code x y → x ≡ y
  decode {x} {y} c = trans (decode' _ _ c) (sym (decode' _ _ (encode refl)))

  private
    endecode' : ∀ {x y} (p : x ≡ y) → subst (code x) (trans p (sym refl)) (encode' x) ≡ subst (code x) p (encode' x)
    endecode' refl = {!!}

  endecode : ∀ {x y} (c : code x y) → encode (decode c) ≡ c
  endecode {x} {y} c = trans {!endecode' !} (code-contr x y c)


  private
    deencode' : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) → trans p (sym p) ≡ refl
    deencode' refl = refl

  deencode : ∀ {x y} (p : x ≡ y) → decode (encode p) ≡ p
  deencode {x} refl = deencode' (decode' _ _ (encode' x))

  lift-allpaths : (∀ x (c1 c2 : code x x) → c1 ≡ c2) → ∀ {x y : A} (p q : x ≡ y) → p ≡ q
  lift-allpaths allpaths p refl = trans (trans (sym (deencode p)) (cong decode (allpaths _ (encode p) (encode refl)))) (deencode refl)-}

{-module encode-decode-het
  {ℓ ℓ′ ℓ′′ : Level}
  {A : Set ℓ}
  (B : A → Set ℓ′)
  (code : {a a' : A} → B a → B a' → Set ℓ′′)
  (encode' : ∀ {a} x → code {a} {a} x x)
  (decodeT' : ∀ {a a'} x y (c : code {a} {a'} x y) → a ≡ a')
  (decode' : (f : ∀ a a' x y → code {a} {a'} x y → a ≡ a')
    → (∀ a x y c → refl ≡ f a a x y c)
    → ∀ {a a'} x y (c : code {a} {a'} x y) → subst B (f a a' x y c) x ≡ y)
  (code-contr : ∀ {a} (x y : B a) (p : x ≡ y) (c : code x y) → subst (code x) p (encode' x) ≡ c)
  where

  encodeT : ∀ {a-}

Con-code : Con → Con → Set
Con-code ∅ ∅ = ⊤
Con-code ∅ _ = ⊥
Con-code (Γ , A) (Γ' , A') = Σ (Γ ≡ Γ') (λ p → subst Ty p A ≡ A')
Con-code (Γ , A) _ = ⊥

Con-encode : ∀ {Γ Γ'} → Γ ≡ Γ' → Con-code Γ Γ'
Con-encode {∅} {∅} p = tt
Con-encode {∅} {Γ' , x} ()
Con-encode {Γ , x} {∅} ()
Con-encode {Γ , x} {._ , ._} refl = refl ,, refl

Con-decode' : ∀ {Γ Γ'} → Con-code Γ Γ' → Γ ≡ Γ'
Con-decode' {∅} {∅} p = refl
Con-decode' {∅} {Γ' , x} ()
Con-decode' {Γ , x} {∅} ()
Con-decode' {Γ , x} {Γ' , x₁} (p ,, q) = cong₂-dep _,_ p q

Con-decode : ∀ {Γ Γ'} → Con-code Γ Γ' → Γ ≡ Γ'
Con-decode {Γ} {Γ'} c = trans (Con-decode' c) (sym (Con-decode' (Con-encode {Γ'} {Γ'} refl)))

trans-pp⁻¹ : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → trans p (sym p) ≡ refl
trans-pp⁻¹ refl = refl

Con-deencode : ∀ {Γ Γ'} (p : Γ ≡ Γ') → Con-decode {Γ} {Γ'} (Con-encode p) ≡ p
Con-deencode {Γ} refl = trans-pp⁻¹ (Con-decode' (Con-encode {Γ} refl))

Con-endecode : ∀ {Γ Γ'} (c : Con-code Γ Γ') → Con-encode {Γ} {Γ'} (Con-decode c) ≡ c
Con-endecode {∅} {∅} c = refl
Con-endecode {∅} {Γ' , x} ()
Con-endecode {Γ , x} {∅} ()
Con-endecode {Γ , x} {.Γ , .x} (refl ,, refl) = refl

Con≡-proj₁ : ∀ {Γ A Γ' A'} → _≡_ {lzero} {Con} (Γ , A) (Γ' , A') → Γ ≡ Γ'
Con≡-proj₁ refl = refl

Ty-code : ∀ {Γ} → Ty Γ → Ty Γ → Set
Ty-code {Γ} U U = ⊤
Ty-code U _ = ⊥
Ty-code (‘Π’ A B) (‘Π’ A' B') = Σ (A ≡ A') (λ p → subst (λ X → Ty (_ , X)) p B ≡ B')
Ty-code (‘Π’ T T₁) _ = ⊥
Ty-code (El x) (El x₁) = x ≡ x₁
Ty-code (El x) _ = ⊥

Ty-encode : ∀ {Γ T T'} → T ≡ T' → Ty-code {Γ} T T'
Ty-encode {Γ} {T = U} {T' = U} p = tt
Ty-encode {Γ} {T = U} {T' = ‘Π’ _ _} ()
Ty-encode {T = ‘Π’ T T₁} refl = refl ,, refl
Ty-encode {T = U} {El x} ()
Ty-encode {T = El x} {U} ()
Ty-encode {T = El x} {El .x} refl = refl
Ty-encode {T = El x} {‘Π’ T' T''} ()

Ty-decode' : ∀ {Γ} {T : Ty Γ} {T' : Ty Γ} → Ty-code T T' → T ≡ T'
Ty-decode' {T = U} {U} p = refl
Ty-decode' {T = U} {‘Π’ T' T''} ()
Ty-decode' {T = ‘Π’ T T₁} {U} ()
Ty-decode' {T = ‘Π’ T T₁} {‘Π’ .T .T₁} (refl ,, refl) = refl
Ty-decode' {T = U} {El x} ()
Ty-decode' {T = El x} {U} ()
Ty-decode' {T = El x} {El .x} refl = refl
Ty-decode' {T = El x} {‘Π’ T' T''} ()
Ty-decode' {T = ‘Π’ T T₁} {El x} ()

Ty-decode : ∀ {Γ} {T : Ty Γ} {T' : Ty Γ} → Ty-code T T' → T ≡ T'
Ty-decode {Γ} {T} {T'} c = trans (Ty-decode' {Γ} {T} {T'} c) (sym (Ty-decode' {Γ} {T'} {T'} (Ty-encode {Γ} {T'} {T'} refl)))

Ty-deencode : ∀ {Γ} {T T' : Ty Γ} (p : T ≡ T') → Ty-decode {Γ} {T} {T'} (Ty-encode p) ≡ p
Ty-deencode {Γ} {T} refl = trans-pp⁻¹ (Ty-decode' (Ty-encode {Γ} {T} refl))

Ty-endecode : ∀ {Γ} {T T' : Ty Γ} (c : Ty-code T T') → Ty-encode {Γ} {T} {T'} (Ty-decode c) ≡ c
Ty-endecode {T = U} {U} c = refl
Ty-endecode {T = U} {‘Π’ T' T''} ()
Ty-endecode {T = U} {El _} ()
Ty-endecode {T = ‘Π’ T T₁} {U} ()
Ty-endecode {T = ‘Π’ T T₁} {El _} ()
Ty-endecode {T = ‘Π’ T T₁} {‘Π’ .T .T₁} (refl ,, refl) = refl
Ty-endecode {T = El _} {U} ()
Ty-endecode {T = El x} {El .x} refl = refl
Ty-endecode {T = El x} {‘Π’ T' T''} ()

Σ-decode : ∀ {a b} {A : Set a} {B : A → Set b} {x y : Σ A B}
  → Σ (Σ.proj₁ x ≡ Σ.proj₁ y) (λ p → subst B p (Σ.proj₂ x) ≡ Σ.proj₂ y)
  → x ≡ y
Σ-decode {x = _ ,, _} {._ ,, ._} (refl ,, refl) = refl

mutual
  Ty-set : ∀ {Γ} {T T' : Ty Γ} (p q : T ≡ T') → p ≡ q
  Ty-set {Γ} {T} {T'} p q = trans (trans (sym (Ty-deencode p)) (cong Ty-decode (Ty-code-set {Γ} {T} {T'} _ _))) (Ty-deencode q)

  Ty-code-set : ∀ {Γ} {T T' : Ty Γ} (p q : Ty-code T T') → p ≡ q
  Ty-code-set {T = U} {U} p q = refl
  Ty-code-set {T = U} {‘Π’ T' T''} () q
  Ty-code-set {T = U} {El _} () q
  Ty-code-set {T = ‘Π’ T T₁} {U} () q
  Ty-code-set {T = ‘Π’ T T₁} {El _} () q
  Ty-code-set {T = ‘Π’ T T₁} {‘Π’ T' T''} (p₁ ,, p₂) (q₁ ,, q₂) = Σ-decode (Ty-set p₁ q₁ ,, Ty-set _ q₂)
  Ty-code-set {T = El x} {U} () q
  Ty-code-set {T = El x} {El x₁} p q = {!!}
  Ty-code-set {T = El x} {‘Π’ T' T''} () q

mutual
  Con-set : ∀ {Γ Γ' : Con} (p q : Γ ≡ Γ') → p ≡ q
  Con-set {Γ} {Γ'} p q = trans (trans (sym (Con-deencode p)) (cong Con-decode (Con-code-set {Γ} {Γ'} _ _))) (Con-deencode q)

  Con-code-set : ∀ {Γ Γ' : Con} (p q : Con-code Γ Γ') → p ≡ q
  Con-code-set {∅} {∅} p q = refl
  Con-code-set {∅} {Γ' , x} () q
  Con-code-set {Γ , x} {∅} () q
  Con-code-set {Γ , x} {Γ' , x₁} (p₁ ,, p₂) (q₁ ,, q₂) = Σ-decode ((Con-set p₁ q₁) ,, Ty-set _ q₂)

{-
Ty-decodeT' {T = U} {U} p = Con-decode p
Ty-decodeT' {T = U} {‘Π’ T' T''} ()
Ty-decodeT' {T = ‘Π’ T T₁} {U} ()
Ty-decodeT' {Γ} {Γ'} {‘Π’ T T₁} {‘Π’ T' T''} p = Con≡-proj₁ (Ty-decodeT' {Γ , T} {Γ' , T'} {T₁} {T''} p)

Ty-decodeT : ∀ {Γ Γ'} {T : Ty Γ} {T' : Ty Γ'} → Ty-code T T' → Γ ≡ Γ'
Ty-decodeT {Γ} {Γ'} {T} {T'} c = trans (Ty-decodeT' {Γ} {Γ'} {T} {T'} c) (sym (Ty-decodeT' {Γ'} {Γ'} {T'} {T'} (Ty-encode {Γ'} {T'} {T'} refl)))

Ty-deencodeT : ∀ {Γ} {T T' : Ty Γ} (p : T ≡ T') → Ty-decodeT {Γ} {Γ} {T} {T'} (Ty-encode p) ≡ refl
Ty-deencodeT {Γ} {T} refl = trans-pp⁻¹ (Ty-decodeT' {Γ} {Γ} {T} {T} (Ty-encode {Γ} {T} {T} refl))
-}

{-
Ty-code : ∀ {Γ Γ'} → Ty Γ → Ty Γ' → Set
Ty-code {Γ} {Γ'} U U = Con-code Γ Γ'
Ty-code U _ = ⊥
Ty-code (‘Π’ T T₁) (‘Π’ T' T'') = Ty-code T₁ T''
Ty-code (‘Π’ T T₁) _ = ⊥

Ty-encode : ∀ {Γ T T'} → T ≡ T' → Ty-code {Γ} {Γ} T T'
Ty-encode {Γ} {T = U} refl = Con-encode {Γ} {Γ} refl
Ty-encode {T = ‘Π’ T T₁} refl = Ty-encode {_ , T} {T₁} {T₁} refl

Ty-decodeT' : ∀ {Γ Γ'} {T : Ty Γ} {T' : Ty Γ'} → Ty-code T T' → Γ ≡ Γ'
Ty-decodeT' {T = U} {U} p = Con-decode p
Ty-decodeT' {T = U} {‘Π’ T' T''} ()
Ty-decodeT' {T = ‘Π’ T T₁} {U} ()
Ty-decodeT' {Γ} {Γ'} {‘Π’ T T₁} {‘Π’ T' T''} p = Con≡-proj₁ (Ty-decodeT' {Γ , T} {Γ' , T'} {T₁} {T''} p)

Ty-decodeT : ∀ {Γ Γ'} {T : Ty Γ} {T' : Ty Γ'} → Ty-code T T' → Γ ≡ Γ'
Ty-decodeT {Γ} {Γ'} {T} {T'} c = trans (Ty-decodeT' {Γ} {Γ'} {T} {T'} c) (sym (Ty-decodeT' {Γ'} {Γ'} {T'} {T'} (Ty-encode {Γ'} {T'} {T'} refl)))

Ty-deencodeT : ∀ {Γ} {T T' : Ty Γ} (p : T ≡ T') → Ty-decodeT {Γ} {Γ} {T} {T'} (Ty-encode p) ≡ refl
Ty-deencodeT {Γ} {T} refl = trans-pp⁻¹ (Ty-decodeT' {Γ} {Γ} {T} {T} (Ty-encode {Γ} {T} {T} refl))

{-Ty-decode' : ∀ {Γ} {T : Ty Γ} {T' : Ty Γ'} → (c : Ty-code T T') → subst Ty (Ty-decodeT {Γ} {Γ'} {T} {T'} c) T ≡ T'
Ty-decode' {T = U} {U} p = {!!}
Ty-decode' {T = U} {‘Π’ T' T''} ()
Ty-decode' {T = ‘Π’ A B} {U} p = {!!}
Ty-decode' {T = ‘Π’ A B} {‘Π’ A' B'} p = {!!}-}
{-
Ty-decodeT : ∀ {Γ Γ'} {T : Ty Γ} {T' : Ty Γ'} → Ty-code T T' → Γ ≡ Γ'
Ty-decodeT {Γ} {Γ'} {T} {T'} c = trans (Ty-decodeT' {Γ} {Γ'} {T} {T'} c) (sym (Ty-decodeT' {Γ'} {Γ'} {T'} {T'} (Ty-encode {Γ'} {T'} {T'} refl)))

Ty-deencodeT : ∀ {Γ} {T T' : Ty Γ} (p : T ≡ T') → Ty-decodeT {Γ} {Γ} {T} {T'} (Ty-encode p) ≡ refl
Ty-deencodeT {Γ} {T} refl = trans-pp⁻¹ (Ty-decodeT' {Γ} {Γ} {T} {T} (Ty-encode {Γ} {T} {T} refl))
-}
-}
--mutual


{-
  subst-Ty-decodeT : ∀ {Γ Γ'} {A : Ty Γ} {B : Ty (Γ , A)} {A' : Ty Γ'} {B' : Ty (Γ' , A')} (p : Ty-code B B') → subst Ty (Ty-decodeT-helper {Γ} {A} {Γ'} {A'} {B} {B'} (Ty-decodeT {T = B} {T' = B'} p)) (‘Π’ A B) ≡ ‘Π’ A' B'
  subst-Ty-decodeT {Γ} {Γ'} {A} {B} {A'} {B'} p = helper {Γ} {Γ'} A B A' B' (Ty-decodeT {Γ , A} {Γ' , A'} {B} {B'} p) (Ty-decode' {Γ , A} {Γ' , A'} {B} {B'} p)
    where
      helper : ∀ {Γ} {Γ'} A B A' B' (p : _≡_ {lzero} {Con} (Γ , A) (Γ' , A')) (q : subst Ty p B ≡ B') → subst Ty (Ty-decodeT-helper {Γ} {A} {Γ'} {A'} {B} {B'} p) (‘Π’ A B) ≡ ‘Π’ A' B'
      helper A₁ B₁ .A₁ .B₁ refl refl = refl

  Ty-deencodeT : ∀ {Γ} {T T' : Ty Γ} (p : T ≡ T') → refl ≡ Ty-decodeT (Ty-encode p)
  Ty-deencodeT {T = U} refl = Con-deencode refl
  Ty-deencodeT {Γ} {T = ‘Π’ T T₁} refl = cong (λ p → Ty-decodeT-helper p) (Ty-deencodeT {Γ , T} {T₁} refl)

  Con-deencode : ∀ {Γ Γ' : Con} (p : Γ ≡ Γ') → p ≡ Con-decode (Con-encode p)
  Con-deencode {∅} refl = refl
  Con-deencode {Γ , x} refl = refl

  Ty-decode' : ∀ {Γ Γ'} {T : Ty Γ} {T' : Ty Γ'} → (p : Ty-code T T') → subst Ty (Ty-decodeT p) T ≡ T'
  Ty-decode' {Γ} {Γ'} {T = U} {U} p = subst-Ty-U {Γ} {Γ'} (Con-decode p)
  Ty-decode' {T = U} {‘Π’ T' T''} ()
  Ty-decode' {T = ‘Π’ T T₁} {U} ()
  Ty-decode' {Γ} {Γ'} {‘Π’ A B} {‘Π’ A' B'} p = subst-Ty-decodeT {Γ} {Γ'} {A} {B} {A'} {B'} p

  Ty-deencode : ∀ {Γ} {T T' : Ty Γ} (p : T ≡ T') → subst (λ q → subst Ty q T ≡ T') {refl} {_} (Ty-deencodeT p) p ≡ Ty-decode' (Ty-encode p)
  Ty-deencode {∅} {U} refl = refl
  Ty-deencode {Γ , x} {U} refl = refl
  Ty-deencode {Γ} {T = ‘Π’ T T₁} refl = {!trans ? helper!}
    where helper : subst (λ q → subst Ty q T₁ ≡ T₁) (Ty-deencodeT {Γ , T} {T₁} {T₁} refl) refl ≡
                     Ty-decode' {Γ , T} {Γ , T} {T₁} {T₁} (Ty-encode {Γ , T} {T₁} {T₁} refl)
          helper = Ty-deencode {Γ , T} {T₁} {T₁} refl


-}
subst-Var-Con : ∀ {Γ A Γ' A'} → _≡_ {lzero} {Con} (Γ , A) (Γ' , A') → Var Γ A → Var Γ' A'
subst-Var-Con refl v = v

mutual
  Var-code-helper : ∀ {Γ A Γ' A'} (B : Ty Γ) (B' : Ty Γ') (v1 : Var Γ A) (v2 : Var Γ' A')→ _≡_ {lzero} {Con} (Γ , A) (Γ' , A') → Set
  Var-code-helper B₁ B'' v3 v4 refl = B₁ ≡ B''

  Var-code : ∀ {Γ T Γ' T'} → Var Γ T → Var Γ' T' → Set
  Var-code (vz {Γ} {A}) (vz {Γ'} {A'}) = _≡_ {lzero} {Con} (Γ , A) (Γ' , A')
  Var-code vz _ = ⊥
  Var-code (vs {Γ} {A} {B} v1) (vs {Γ'} {A'} {B'} v2) = Σ (Var-code v1 v2) (λ c → Var-code-helper B B' v1 v2 (Var-decodeT {v₁ = v1} {v2} c))
  Var-code (vs v1) _ = ⊥
  Var-code (v⊥ {Γ} {A}) (v⊥ {Γ'} {A'}) = _≡_ {lzero} {Con} (Γ , A) (Γ' , A')
  Var-code v⊥ _ = ⊥

  Var-encode : ∀ {Γ T} {v₁ v₂ : Var Γ T} → v₁ ≡ v₂ → Var-code v₁ v₂
  Var-encode {v₁ = vz} refl = refl
  Var-encode {v₁ = vs v₁} refl = Var-encode {v₁ = v₁} refl ,, subst (λ p → Var-code-helper _ _ v₁ v₁ p) (Var-decodeTencode v₁) refl
  Var-encode {v₁ = v⊥ {Γ} {T}} refl = refl

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
  Var-decodeT {Γ , A} {v₁ = vz} {v⊥} ()
  Var-decodeT {v₁ = vs v₁} {vz} ()
  Var-decodeT {v₁ = vs v₁} {v⊥} ()
  Var-decodeT {v₁ = vs {Γ} {A} {B} v₁} {vs {Γ'} {A'} {B'} v₂} (p ,, q) = Var-decodeT-helper B B' {v₁ = v₁} {v₂} (Var-decodeT {v₁ = v₁} {v₂} p) q
  Var-decodeT {v₁ = v⊥ {Γ} {A}} {v⊥ {Γ'} {A'}} p = p
  Var-decodeT {v₁ = v⊥} {vz} ()
  Var-decodeT {v₁ = v⊥} {vs v₂} ()

  Var-decodeTencode : ∀ {Γ T} (v₁ : Var Γ T) → refl ≡ Var-decodeT (Var-encode {v₁ = v₁} refl)
  Var-decodeTencode vz = refl
  Var-decodeTencode (vs {Γ} {A} {B} v) = helper (Var-decodeT {Γ} {A} {Γ} {A} {v} (Var-encode {Γ} {A} {v} refl)) (Var-decodeTencode {Γ} {A} v)
    where
      helper : ∀ (p : (Γ , A) ≡ (Γ , A)) (q : refl ≡ p) → refl ≡ Var-decodeT-helper B B p (subst (Var-code-helper B B v v) q refl)
      helper .refl refl = refl
  Var-decodeTencode (v⊥ {Γ} {A}) = refl

  Var-decode : ∀ {Γ T Γ' T'} {v₁ : Var Γ T} {v₂ : Var Γ' T'} → (c : Var-code v₁ v₂) → _≡_ {lzero} {Var Γ' T'} (subst-Var-Con (Var-decodeT c) v₁) v₂
  Var-decode {v₁ = vz} {vz} refl = refl
  Var-decode {v₁ = vz} {vs v₂} ()
  Var-decode {v₁ = vz} {v⊥} ()
  Var-decode {v₁ = vs v₁} {vz} ()
  Var-decode {v₁ = vs v₁} {v⊥} ()
  Var-decode {v₁ = vs {Γ} {A} {B} v₁} {vs {Γ'} {A'} {B'} v₂} (c₁ ,, c₂) = trans (subst-Var-Con-vs B B' v₁ v₂ (Var-decodeT {Γ} {A} {Γ'} {A'} {v₁} c₁) c₂) helper
    where helper : vs {Γ'} {A'} {B'} (subst-Var-Con (Var-decodeT {Γ} {A} {Γ'} {A'} {v₁} c₁) v₁) ≡ vs v₂
          helper = cong vs (Var-decode {Γ} {A} {Γ'} {A'} {v₁ = v₁} {v₂} c₁)
  Var-decode {v₁ = v⊥} {v⊥} refl = refl
  Var-decode {v₁ = v⊥} {vz} ()
  Var-decode {v₁ = v⊥} {vs v₂} ()


mutual
  Var-code-helper-dec : ∀ {Γ A Γ' A'} (B : Ty Γ) (B' : Ty Γ') (v1 : Var Γ A) (v2 : Var Γ' A') (p : _≡_ {lzero} {Con} (Γ , A) (Γ' , A'))
    → SemiDec (Var-code-helper B B' v1 v2 p)
  Var-code-helper-dec B₁ B'' v3 v4 refl = _ ≟T _

  Var-code-dec : ∀ {Γ T Γ' T'} → (v1 : Var Γ T) → (v2 : Var Γ' T') → SemiDec (Var-code v1 v2)
  Var-code-dec vz vz = _ ≟c _
  Var-code-dec vz _ = nothing
  Var-code-dec (vs v1) (vs v2) with Var-code-dec v1 v2
  Var-code-dec (vs {Γ} {A} {B} v1) (vs {Γ'} {A'} {B'} v2) | just x with Var-code-helper-dec B B' v1 v2 (Var-decodeT {v₁ = v1} x)
  Var-code-dec (vs v1) (vs v2) | just x | just x₁ = just (x ,, x₁)
  Var-code-dec (vs v1) (vs v2) | just x | nothing = nothing
  Var-code-dec (vs v1) (vs v2) | nothing = nothing
  Var-code-dec (vs v1) _ = nothing
  Var-code-dec v⊥ v⊥ = _ ≟c _
  Var-code-dec v⊥ _ = nothing


v₁ ≟v v₂ with Var-code-dec v₁ v₂
_≟v_ {Γ} {T} v₁ v₂ | just x = just (trans (cong (λ p → subst-Var-Con p v₁) {refl} {Var-decodeT {v₁ = v₁} x} helper') helper)
  where helper : subst-Var-Con (Var-decodeT {v₁ = v₁} x) v₁ ≡ v₂
        helper = (Var-decode {v₁ = v₁} {v₂ = v₂} x)

        helper' : refl {lzero} {Con} ≡ Var-decodeT {Γ} {T} {Γ} {T} {v₁} x
        helper' = Con-set refl (Var-decodeT {v₁ = v₁} x)
v₁ ≟v v₂ | nothing = nothing
-}



-- Wₙ Δ A (El x) = El (wₙ Δ A x)
-- Wₙ Δ A (‘Π’ ty ty') = ‘Π’ (Wₙ Δ A ty) (Wₙ (Δ , ty) A ty')

-- wₙ Δ A (‘λ’ tm) = ‘λ’ (wₙ (Δ , _) A tm)
-- wₙ Δ A (var v) = var (vₙ Δ A v)

cast-Var : ∀ {ℓ Γ} {T T' : Ty Γ ℓ} → Var Γ T → Var Γ T'
cast-Var {Γ = Γ} {T} {T'} v with T ≟T T'
cast-Var v | just refl = v
cast-Var v | nothing = v⊥

vₙ (ε Γ) A v = vs v
vₙ (Δ , X) A vz = cast-Var vz -- ACK!
vₙ (Δ , X) A (vs {A = B} v) = cast-Var (vs (vₙ Δ A v))
vₙ (Δ , X) A v⊥ = v⊥

wₙU : ∀ {ℓ ℓ′ Γ} (Δ : Γ ++) (B : Ty Γ ℓ′) → Tm (++ Δ) (U ℓ) → Tm (++ B cw Δ) (U ℓ)

Wₙ Δ A (U ℓ) = (U ℓ)
-- Wₙ Δ A (El x) = El (wₙ Δ A x)
Wₙ Δ A (‘Π’ ty ty') = ‘Π’ (Wₙ Δ A ty) (Wₙ (Δ , ty) A ty')
Wₙ {ℓ} {ℓ′} {Γ} Δ A (El {.ℓ′} x) = El {!(wₙ {?} {?} {Γ} Δ A x)!}
--  where helper : {!Tm (++_ {Γ , A} (_cw_ {Γ} A Δ)) U!}
--        helper = wₙU {Γ} Δ A x
--  : ∀ {ℓ ℓ′ Γ} (Δ : Γ ++) (B : Ty Γ ℓ) {A : Ty _ ℓ′} → Tm (++ Δ) A → Tm (++ B cw Δ) (Wₙ Δ B A)

wₙU Δ B (var v) = var (vₙ Δ B v)

-- wₙ Δ A (‘λ’ tm) = ‘λ’ (wₙ (Δ , _) A tm)
wₙ Δ A (var v) = var (vₙ Δ A v)

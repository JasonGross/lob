{-# OPTIONS --without-K #-}

module common where
open import Agda.Primitive public
  using    (Level; _⊔_; lzero; lsuc; Setω)

infixr 1 _,_
infixr 1 _,≡_
infixr 1 _×≡_
infixl 1 _≡_
infixr 1 _~_
infixr 2 _∧_
infixr 2 _×_
infixr 3 _∷_

data bool : Set where
  true : bool
  false : bool

{-# BUILTIN BOOL  bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE  true  #-}

_∧_ : bool → bool → bool
true ∧ true = true
true ∧ false = false
false ∧ true = false
false ∧ false = false

_∨_ : bool → bool → bool
true ∨ true = true
true ∨ false = true
false ∨ true = true
false ∨ false = false

record Σ {ℓ ℓ′} (A : Set ℓ) (P : A → Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : P proj₁

_×_ : ∀ {ℓ ℓ′} (A : Set ℓ) (B : Set ℓ′) → Set (ℓ ⊔ ℓ′)
A × B = Σ A (λ _ → B)

record _↔_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor iff
  field
    fwdl : A → B
    bakl : B → A

_←■→_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → A ↔ B → B ↔ C → A ↔ C
f ←■→ g = iff (λ x → g .fwdl (f .fwdl x)) (λ x → f .bakl (g .bakl x))
  where open _↔_

id↔ : ∀ {a} {A : Set a} → A ↔ A
id↔ = iff (λ x → x) (λ x → x)

if_then_else_ : ∀ {ℓ} {A : Set ℓ} → (b : bool) → A → A → A
if true then t else f = t
if false then t else f = f

record Lifted {a b} (A : Set a) : Set (b ⊔ a) where
  constructor lift
  field lower : A

open Lifted using (lower) public

data Maybe {ℓ : Level} (A : Set ℓ) : Set ℓ where
  just    : (x : A) → Maybe A
  nothing : Maybe A

Maybe-elim : ∀ {ℓ ℓ′} {A : Set ℓ} (P : Maybe A → Set ℓ′)
  → ((x : A) → P (just x))
  → P nothing
  → (x : Maybe A)
  → P x
Maybe-elim P Pjust Pnothing (just x) = Pjust x
Maybe-elim P Pjust Pnothing nothing = Pnothing

option-map : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′}
  → (A → B)
  → Maybe A → Maybe B
option-map f (just x) = just (f x)
option-map f nothing = nothing


option-bind : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′}
  → Maybe A
  → (A → Maybe B)
  → Maybe B
option-bind (just x) f = option-map (λ x₁ → x₁) (f x)
option-bind nothing f = nothing

data ⊥ {ℓ : Level} : Set ℓ where

⊥-elim : {ℓ ℓ′ : Level} → ⊥ {ℓ} → {A : Set ℓ′} → A
⊥-elim ()

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ T = T → ⊥ {lzero}

record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt

infixr 1 _⊎_

data _⊎_ {a} {b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
x ≢ y = ¬ (x ≡ y)

dec-eq-on : ∀ {ℓ} {A : Set ℓ} → (x : A) → (y : A) → Set ℓ
dec-eq-on x y = (x ≡ y) ⊎ (x ≢ y)

dec-eq : ∀ {ℓ} → Set ℓ → Set ℓ
dec-eq A = (x : A) → (y : A) → dec-eq-on x y

UIP-on : ∀ {ℓ} → Set ℓ → Set ℓ
UIP-on A = ∀ {x y : A} → (p q : x ≡ y) → p ≡ q

K-on : ∀ {ℓ} → Set ℓ → Setω
K-on A = ∀ {x : A} {ℓ′} (P : x ≡ x → Set ℓ′) → P refl → ∀ {p} → P p

sym : ∀ {ℓ} {A : Set ℓ} → {x : A} → {y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

trans-syml : ∀ {ℓ} {A : Set ℓ} → {x y : A} (p : x ≡ y) → trans (sym p) p ≡ refl
trans-syml refl = refl

transport : ∀ {A : Set} {x : A} {y : A} → (P : A → Set) → x ≡ y → P x → P y
transport P refl v = v

transport2 : ∀ {A : Set} {B : A → Set} {x x' : A} {y : B x} {y' : B x'} → (P : (x : A) → B x → Set) → (p : x ≡ x') → transport B p y ≡ y' → P x y → P x' y'
transport2 P refl = transport (P _)

transport3 : ∀ {A : Set} {B : A → Set} {C : (x : A) → (y : B x) → Set} {x x' : A} {y : B x} {y' : B x'} {z : C x y} {z' : C x' y'} → (P : (x : A) → (y : B x) → C x y → Set) → (p : x ≡ x') → (q : transport B p y ≡ y') → transport2 C p q z ≡ z' → P x y z → P x' y' z'
transport3 P refl = transport2 (P _)

transport4 : ∀ {A : Set} {B : A → Set} {C : (x : A) → (y : B x) → Set} {D : (x : A) → (y : B x) → (z : C x y) → Set} {x x' : A} {y : B x} {y' : B x'} {z : C x y} {z' : C x' y'} {w : D x y z} {w' : D x' y' z'} → (P : (x : A) → (y : B x) → (z : C x y) → D x y z → Set) → (p : x ≡ x') → (q : transport B p y ≡ y') → (r : transport2 C p q z ≡ z') → transport3 D p q r w ≡ w' → P x y z w → P x' y' z' w'
transport4 P refl = transport3 (P _)

sub : ∀ {l} {A : Set l} {m} (B : A -> Set m) {a1 a2} -> a1 ≡ a2 -> B a1 -> B a2
sub B refl b = b

sub2 : ∀ {ℓ₁ ℓ₂} {A₁ : Set ℓ₁} {A₂ : Set ℓ₂} {m} (B : A₁ → A₂ -> Set m) {a1 a2} -> a1 ≡ a2 → ∀ {a1' a2'} → a1' ≡ a2' -> B a1 a1' -> B a2 a2'
sub2 B refl refl b = b

ap : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
ap f refl = refl

ap2 : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (f : A → B → C) {x y : A} (p : x ≡ y) {x' y' : B} (q : x' ≡ y') → f x x' ≡ f y y'
ap2 f refl refl = refl

apD : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂} (f : (a : A) → B a) {x y : A} (p : x ≡ y) → sub B p (f x) ≡ f y
apD f refl = refl

K-from-UIP : ∀ {ℓ} {A : Set ℓ} → UIP-on A → K-on A
K-from-UIP uip P h {p} = sub P (uip refl p) h

UIP-from-K : ∀ {ℓ} {A : Set ℓ} → K-on A → UIP-on A
UIP-from-K K refl p = K (λ{ p → refl ≡ p }) refl

_,≡_ : ∀ {ℓ ℓ′} {A : Set ℓ} {P : A → Set ℓ′} {x y : A} {p : P x} {q : P y}
  → (h : x ≡ y)
  → (sub P h p ≡ q)
  → (x , p) ≡ (y , q)
refl ,≡ refl = refl

_×≡_ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} {x y : A} {p q : B}
  → (x ≡ y)
  → (p ≡ q)
  → (x , p) ≡ (y , q)
refl ×≡ refl = refl

-- slightly nicer form
apD-proj₂ : ∀ {ℓ ℓ′} {A : Set ℓ} {P : A → Set ℓ′} {x y : Σ A P} → (p : x ≡ y) → sub P (ap Σ.proj₁ p) (Σ.proj₂ x) ≡ Σ.proj₂ y
apD-proj₂ refl = refl

ap-compose : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} (f : A → B) (g : B → C) {x y : A} (p : x ≡ y) → ap g (ap f p) ≡ ap (λ x → g (f x)) p
ap-compose f g refl = refl

ap-id : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → ap (λ x → x) p ≡ p
ap-id refl = refl

transparent-dec-eq : ∀ {ℓ} {A : Set ℓ} → dec-eq A → dec-eq A
transparent-dec-eq dec x y with (dec x x) | (dec x y)
... | inj₁ p | inj₁ q = inj₁ (trans (sym p) q)
... | inj₁ p | inj₂ q = inj₂ q
... | inj₂ p | inj₁ q = ⊥-elim (p refl)
... | inj₂ p | inj₂ q = inj₂ q

transparent-dec-eq-refl : ∀ {ℓ} {A : Set ℓ} (dec : dec-eq A) {x y} (p : x ≡ y) → transparent-dec-eq dec x y ≡ inj₁ p
transparent-dec-eq-refl dec {x = x} refl with (dec x x)
... | inj₁ p = ap inj₁ (trans-syml _)
... | inj₂ p = ⊥-elim (p refl)

UIP-from-dec : ∀ {ℓ} {A : Set ℓ} → dec-eq A → UIP-on A
UIP-from-dec dec p q with (trans (sym (transparent-dec-eq-refl dec p)) (transparent-dec-eq-refl dec q))
... | refl = refl

K-from-dec : ∀ {ℓ} {A : Set ℓ} → dec-eq A → K-on A
K-from-dec dec P h {p} with (UIP-from-dec dec p refl)
... | refl = h

transparent-UIP : ∀ {ℓ} {A : Set ℓ} → UIP-on A → UIP-on A
transparent-UIP uip x y = trans (sym (uip x x)) (uip x y)

transparent-UIP-refl : ∀ {ℓ} {A : Set ℓ} (uip : UIP-on A) {x y : A} {p q : x ≡ y} (r : p ≡ q) → transparent-UIP uip p q ≡ r
transparent-UIP-refl uip {x = x} refl = trans-syml (uip _ _)

bump-UIP : ∀ {ℓ} {A : Set ℓ} → UIP-on A → ∀ {x y : A} → UIP-on (x ≡ y)
bump-UIP uip p q = trans (sym (transparent-UIP-refl uip p)) (transparent-UIP-refl uip q)

eq-dec-from-endecode : ∀ {ℓ} {A : Set ℓ} {c}
  (code : A → A → Set c)
  (encode : ∀ x → code x x)
  (decode : ∀ {x y} → code x y → x ≡ y)
  (dec-code : ∀ {x y} → (code x y) ⊎ (¬ code x y))
  → dec-eq A
eq-dec-from-endecode {A = A} code encode decode dec-code x y with (dec-code {x} {y})
... | inj₁ c = inj₁ (decode c)
... | inj₂ n = inj₂ (λ{ refl → n (encode x) })

Σ-dec-eq : ∀ {ℓ ℓ′} {A : Set ℓ} {B : A → Set ℓ′} → dec-eq A → (∀ {a} → dec-eq (B a)) → dec-eq (Σ A B)
Σ-dec-eq {B = B} decA decB (a , b) (a' , b') with (decA a a')
... | inj₁ p with (decB (sub B p b) b')
...          | inj₁ q = inj₁ (p ,≡ q)
...          | inj₂ n = inj₂ λ{ refl → n (K-from-dec decA (λ{ p → sub B p b ≡ b }) refl) }
Σ-dec-eq _ _ _ _ | inj₂ n = inj₂ (λ{ refl → n refl })

×-dec-eq : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → dec-eq A → dec-eq B → dec-eq (A × B)
×-dec-eq decA decB = Σ-dec-eq decA decB

Maybe-code : {A : Set} → Maybe A → Maybe A → Set
Maybe-code (just x) (just x₁) = x ≡ x₁
Maybe-code (just x) nothing = ⊥
Maybe-code nothing (just x) = ⊥
Maybe-code nothing nothing = ⊤

Maybe-encode : ∀ {A} {x y : Maybe A} → x ≡ y → Maybe-code x y
Maybe-encode {A} {just x} refl = refl
Maybe-encode {A} {nothing} refl = tt

Maybe-decode : ∀ {A} {x y : Maybe A} → Maybe-code x y → x ≡ y
Maybe-decode {A} {just .x₁} {just x₁} refl = refl
Maybe-decode {A} {just x} {nothing} ()
Maybe-decode {A} {nothing} {just x} ()
Maybe-decode {A} {nothing} {nothing} tt = refl

Maybe-deencode : ∀ {A} {x y : Maybe A} {p : x ≡ y} → Maybe-decode (Maybe-encode p) ≡ p
Maybe-deencode {A} {just x} {.(just x)} {refl} = refl
Maybe-deencode {A} {nothing} {.nothing} {refl} = refl

Maybe-endecode : ∀ {A} {x y : Maybe A} (p : Maybe-code x y) → Maybe-encode {A} {x} {y} (Maybe-decode p) ≡ p
Maybe-endecode {A} {just .x'} {just x'} refl = refl
Maybe-endecode {A} {just x} {nothing} ()
Maybe-endecode {A} {nothing} {just x} ()
Maybe-endecode {A} {nothing} {nothing} tt = refl

bool-dec-eq : dec-eq bool
bool-dec-eq true true = inj₁ refl
bool-dec-eq true false = inj₂ (λ ())
bool-dec-eq false true = inj₂ (λ ())
bool-dec-eq false false = inj₁ refl

bool-UIP : UIP-on bool
bool-UIP = UIP-from-dec bool-dec-eq

bool-K : K-on bool
bool-K = K-from-dec bool-dec-eq

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

ℕ-dec-eq : dec-eq ℕ
ℕ-dec-eq zero zero = inj₁ refl
ℕ-dec-eq (suc x) (suc y) with (ℕ-dec-eq x y)
... | inj₁ p = inj₁ (ap suc p)
... | inj₂ n = inj₂ (λ{ refl → n refl })
ℕ-dec-eq zero (suc _) = inj₂ λ()
ℕ-dec-eq (suc _) zero = inj₂ λ()

ℕ-K : ∀ {ℓ} {n : ℕ} (P : n ≡ n → Set ℓ) → P refl → ∀ {p} → P p
ℕ-K P h = K-from-dec ℕ-dec-eq P h

ℕ2-K : ∀ {ℓ} {n m : ℕ} (P : n ≡ n → m ≡ m → Set ℓ) → P refl refl → ∀ {p q} → P p q
ℕ2-K P h = ℕ-K (P _) (ℕ-K (λ { p → P p refl }) h)

max : ℕ → ℕ → ℕ
max 0 y = y
max x@(suc _) 0 = x
max (suc x) (suc y) = suc (max x y)

infix  4 _==_ _<_ _<?_
infixl 6 _+_ _-_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

{-# BUILTIN NATPLUS _+_ #-}

_-_ : ℕ → ℕ → ℕ
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m

{-# BUILTIN NATMINUS _-_ #-}

_*_ : ℕ → ℕ → ℕ
zero  * m = zero
suc n * m = m + n * m

{-# BUILTIN NATTIMES _*_ #-}

_==_ : ℕ → ℕ → bool
zero  == zero  = true
suc n == suc m = n == m
_     == _     = false

{-# BUILTIN NATEQUALS _==_ #-}

_<?_ : ℕ → ℕ → bool
_     <? zero  = false
zero  <? suc _ = true
suc n <? suc m = n <? m

{-# BUILTIN NATLESS _<?_ #-}

record _<_ (n m : ℕ) : Set where
  constructor rigidify<
  field compute< : n <? m ≡ true

<-alleq : ∀ {n m} → {p q : n < m} → p ≡ q
<-alleq {n} {m} {rigidify< p} {rigidify< q} = ap rigidify< (bool-UIP p q)

<-UIP : ∀ {n m} → UIP-on (n < m)
<-UIP {n} {m} {rigidify< x} {_} refl q = trans {_} {_} {_} {ap rigidify< (ap _<_.compute< q)} (ap (ap rigidify<) (bump-UIP bool-UIP refl (ap (λ r → _<_.compute< r) q))) (trans (ap-compose _<_.compute< rigidify< q) (ap-id q))

<-K : ∀ {n m} → K-on (n < m)
<-K = K-from-UIP <-UIP

<?-trans : ∀ {n m o} → (n <? m) ≡ true → (m <? o) ≡ true → n <? o ≡ true
<?-trans {n} {zero} ()
<?-trans {n} {m} {zero} _ ()
<?-trans {zero} {suc m} {suc o} p q = refl
<?-trans {suc n} {suc m} {suc o} = <?-trans {n} {m} {o}

<-trans : ∀ {n m o} → (n < m) → (m < o) → (n < o)
<-trans {n} {m} {o} (rigidify< p) (rigidify< q) = rigidify< (<?-trans {n} {m} {o} p q)

infixr 2 _■<_
_■<_ = <-trans

_≤_ : ℕ → ℕ → Set
n ≤ m = n < suc m

_≤?_ : ℕ → ℕ → bool
n ≤? m = n <? suc m

<≤?-trans : ∀ {n m o} → (n <? m) ≡ true → (m ≤? o) ≡ true → n <? o ≡ true
<≤?-trans {n} {zero} ()
<≤?-trans {zero} {suc m} {suc o} p q = refl
<≤?-trans {suc n} {suc m} {suc o} = <≤?-trans {n} {m} {o}

<≤-trans : ∀ {n m o} → (n < m) → (m ≤ o) → (n < o)
<≤-trans {n} {m} {o} (rigidify< p) (rigidify< q) = rigidify< (<≤?-trans {n} {m} {o} p q)

infixr 2 _■<≤_
_■<≤_ = <≤-trans

≤<?-trans : ∀ {n m o} → (n ≤? m) ≡ true → (m <? o) ≡ true → n <? o ≡ true
≤<?-trans {n} {m} {zero} _ ()
≤<?-trans {zero} {_} {suc o} p q = refl
≤<?-trans {suc n} {suc m} {suc o} = ≤<?-trans {n} {m} {o}

≤<-trans : ∀ {n m o} → (n ≤ m) → (m < o) → (n < o)
≤<-trans {n} {m} {o} (rigidify< p) (rigidify< q) = rigidify< (≤<?-trans {n} {m} {o} p q)

infixr 2 _■≤<_
_■≤<_ = ≤<-trans

<?-suc : ∀ {a} → a <? suc a ≡ true
<?-suc {zero} = refl
<?-suc {suc a} = <?-suc {a}

<-suc : ∀ {a} → a < suc a
<-suc {a} = rigidify< (<?-suc {a})

<-suc→ : ∀ {a b} → a < b → suc a < suc b
<-suc→ {a} {b} (rigidify< p) = rigidify< p

<-suc← : ∀ {a b} → suc a < suc b → a < b
<-suc← {a} {b} (rigidify< p) = rigidify< p

<?-plus-L : ∀ {a b} → a <? suc (a + b) ≡ true
<?-plus-L {zero} = refl
<?-plus-L {suc a} = <?-plus-L {a}

<-plus-L : ∀ {a b} → a < suc (a + b)
<-plus-L {a} {b} = rigidify< (<?-plus-L {a} {b})

<?-plus-R : ∀ {a b} → b <? suc (a + b) ≡ true
<?-plus-R {zero} {b} = <?-suc {b}
<?-plus-R {suc a} {b} = <?-trans {b} {suc b} {suc (suc (a + b))} (<?-suc {b}) (<?-plus-R {a} {b})

<-plus-R : ∀ {a b} → b < suc (a + b)
<-plus-R {a} {b} = rigidify< (<?-plus-R {a} {b})

<?-plus : ∀ {a b c d} → a <? b ≡ true → c <? d ≡ true → (a + c <? b + d) ≡ true
<?-plus {_} {zero} ()
<?-plus {zero} {suc b} {c} {d} _ p = <?-trans {c} {d} {suc (b + d)} p (<?-plus-R {b} {d})
<?-plus {suc a} {suc b} {c} {d} = <?-plus {a} {b} {c} {d}

<-plus : ∀ {a b c d} → a < b → c < d → (a + c < b + d)
<-plus {a} {b} {c} {d} (rigidify< p) (rigidify< q) = rigidify< (<?-plus {a} {b} {c} {d} p q)

<?-max-spec : ∀ {a b c} → (a <? max b c) ≡ ((a <? b) ∨ (a <? c))
<?-max-spec {zero} {zero} {zero} = refl
<?-max-spec {zero} {zero} {suc c} = refl
<?-max-spec {zero} {suc b} {zero} = refl
<?-max-spec {zero} {suc b} {suc c} = refl
<?-max-spec {suc a} {zero} {zero} = refl
<?-max-spec {suc a} {zero} {suc c} with (a <? c)
... | true = refl
... | false = refl
<?-max-spec {suc a} {suc b} {zero} with (a <? b)
... | true = refl
... | false = refl
<?-max-spec {suc a} {suc b} {suc c} = <?-max-spec {a} {b} {c}

max-<?-spec : ∀ {a b c} → (max b c <? a) ≡ ((b <? a) ∧ (c <? a))
max-<?-spec {zero} {zero} {zero} = refl
max-<?-spec {zero} {zero} {suc c} = refl
max-<?-spec {zero} {suc b} {zero} = refl
max-<?-spec {zero} {suc b} {suc c} = refl
max-<?-spec {suc a} {zero} {zero} = refl
max-<?-spec {suc a} {zero} {suc c} with (c <? a)
... | true = refl
... | false = refl
max-<?-spec {suc a} {suc b} {zero} with (b <? a)
... | true = refl
... | false = refl
max-<?-spec {suc a} {suc b} {suc c} = max-<?-spec {a} {b} {c}

<?-max-spec-L : ∀ {a b c} → (a <? b) ≡ true → (a <? max b c) ≡ true
<?-max-spec-L {a} {b} {c} = helper (<?-max-spec {a} {b} {c})
  where
    helper : ∀ {x y z} → x ≡ (y ∨ z) → y ≡ true → x ≡ true
    helper {z = true} refl refl = refl
    helper {z = false} refl refl = refl

<-max-spec-L : ∀ {a b c} → (a < b) → (a < max b c)
<-max-spec-L {a} {b} {c} (rigidify< p) = rigidify< (<?-max-spec-L {a} {b} {c} p)

<?-max-spec-R : ∀ {a b c} → (a <? c) ≡ true → (a <? max b c) ≡ true
<?-max-spec-R {a} {b} {c} = helper (<?-max-spec {a} {b} {c})
  where
    helper : ∀ {x y z} → x ≡ (y ∨ z) -> z ≡ true → x ≡ true
    helper {y = true} refl refl = refl
    helper {y = false} refl refl = refl

<-max-spec-R : ∀ {a b c} → (a < c) → (a < max b c)
<-max-spec-R {a} {b} {c} (rigidify< p) = rigidify< (<?-max-spec-R {a} {b} {c} p)

<?-max-spec-inv : ∀ {a b c} → (a <? max b c) ≡ true → ((a <? b) ≡ true) ⊎ ((a <? c) ≡ true)
<?-max-spec-inv {a} {b} {c} = helper (<?-max-spec {a} {b} {c})
  where
    helper : ∀ {x} {y} {z} → x ≡ (y ∨ z) → x ≡ true → (y ≡ true) ⊎ (z ≡ true)
    helper {_} {true} {z} p q = inj₁ refl
    helper {_} {false} {true} p q = inj₂ refl
    helper {_} {false} {false} () refl

<-max-spec-inv : ∀ {a b c} → (a < max b c) → (a < b) ⊎ (a < c)
<-max-spec-inv {a} {b} {c} (rigidify< p) with (<?-max-spec-inv {a} {b} {c} p)
... | inj₁ q = inj₁ (rigidify< q)
... | inj₂ q = inj₂ (rigidify< q)

max-<?-spec-inv : ∀ {a b c} → (max b c <? a) ≡ true → ((b <? a) ≡ true) × ((c <? a) ≡ true)
max-<?-spec-inv {a} {b} {c} = helper (max-<?-spec {a} {b} {c})
  where
    helper : ∀ {x} {y} {z} → x ≡ (y ∧ z) → x ≡ true → (y ≡ true) × (z ≡ true)
    helper {_} {true} {true} p q = refl , refl
    helper {_} {true} {false} refl ()
    helper {_} {false} {true} refl ()
    helper {_} {false} {false} refl ()

max-<-spec-inv : ∀ {a b c} → (max b c < a) → (b < a) × (c < a)
max-<-spec-inv {a} {b} {c} (rigidify< p) with (max-<?-spec-inv {a} {b} {c} p)
... | (q , r) = (rigidify< q) , (rigidify< r)

max-<?-spec-build : ∀ {a b c} → ((b <? a) ≡ true) → ((c <? a) ≡ true) → (max b c <? a) ≡ true
max-<?-spec-build {a} {b} {c} = helper (max-<?-spec {a} {b} {c})
  where
    helper : ∀ {x} {y} {z} → x ≡ (y ∧ z) → (y ≡ true) → (z ≡ true) → x ≡ true
    helper refl refl refl = refl

max-<-spec-build : ∀ {a b c} → (b < a) → (c < a) → (max b c < a)
max-<-spec-build {a} {b} {c} (rigidify< p) (rigidify< q) = rigidify< (max-<?-spec-build {a} {b} {c} p q)

<?-max-spec-L-suc : ∀ {a b c} → (a <? suc b) ≡ true → (a <? suc (max b c)) ≡ true
<?-max-spec-L-suc {zero} {b} {c} _ = refl
<?-max-spec-L-suc {suc a} {b} {c} = <?-max-spec-L {a} {b} {c}

<-max-spec-L-suc : ∀ {a b c} → (a < suc b) → (a < suc (max b c))
<-max-spec-L-suc {a} {b} {c} (rigidify< p) = rigidify< (<?-max-spec-L-suc {a} {b} {c} p)

<?-max-spec-R-suc : ∀ {a b c} → (a <? suc c) ≡ true → (a <? suc (max b c)) ≡ true
<?-max-spec-R-suc {zero} {b} {c} _ = refl
<?-max-spec-R-suc {suc a} {b} {c} = <?-max-spec-R {a} {b} {c}

<-max-spec-R-suc : ∀ {a b c} → (a < suc c) → (a < suc (max b c))
<-max-spec-R-suc {a} {b} {c} (rigidify< p) = rigidify< (<?-max-spec-R-suc {a} {b} {c} p)

<?-max : ∀ {a b c d} → a <? b ≡ true → c <? d ≡ true → (max a c <? max b d) ≡ true
<?-max {_} {zero} ()
<?-max {_} {suc b} {_} {zero} _ ()
<?-max {zero} {suc b} {zero} {suc d} _ p = refl
<?-max {zero} {suc b} {suc c} {suc d} _ p = <?-max-spec-R {c} {b} {d} p
<?-max {suc a} {suc b} {zero} {suc d} p _ = <?-max-spec-L {a} {b} {d} p
<?-max {suc a} {suc b} {suc c} {suc d} = <?-max {a} {b} {c} {d}

<-max : ∀ {a b c d} → a < b → c < d → (max a c < max b d)
<-max {a} {b} {c} {d} (rigidify< p) (rigidify< q) = rigidify< (<?-max {a} {b} {c} {d} p q)

data List {ℓ} (A : Set ℓ) : Set ℓ where
  [] : List A
  _∷_ : A → List A → List A

record IsEquiv {ℓ} {A B : Set ℓ} (f : A → B) : Set ℓ where
  constructor is-eqv
  field
    inv : B → A
    isretr : ∀ b → f (inv b) ≡ b
    issect : ∀ a → inv (f a) ≡ a
    isadj : ∀ a → isretr (f a) ≡ ap f (issect a)

record _~_ {ℓ} (A B : Set ℓ) : Set ℓ where
  constructor eqv
  field
    fwd : A → B
    iseqv : IsEquiv fwd
  open IsEquiv iseqv renaming (inv to bak) public

refl~ : ∀ {ℓ} {A : Set ℓ} → A ~ A
refl~ = eqv (λ a → a) (is-eqv (λ a → a) (λ b → refl) (λ a → refl) (λ a → refl))

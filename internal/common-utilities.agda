module common-utilities where
open import common

lift-≟-1 : {A B : Set} → (f : A → B) → {x : A} → {y : A} → Maybe (x ≡ y) → Maybe (f x ≡ f y)
lift-≟-1 f (just refl) = just refl
lift-≟-1 f nothing = nothing

lift-≟-1-refl : ∀ {A B} f {x} p → p ≡ just refl → lift-≟-1 {A} {B} f {x} {x} p ≡ just refl
lift-≟-1-refl f ._ refl = refl

lift-≟-2-helper : ∀ {A : Set} {B : A → Set} {C} {f : (x : A) → B x → C} {x : A} {y y' : B x} → Maybe (y ≡ y') → Maybe (f x y ≡ f x y')
lift-≟-2-helper (just refl) = just refl
lift-≟-2-helper nothing = nothing

lift-≟-2 : ∀ {A} {B : A → Set} {C} → (f : (x : A) → B x → C) → {x x' : A} → {y : B x} → {y' : B x'} → Maybe (x ≡ x') → ((p : x ≡ x') → Maybe (transport B p y ≡ y')) → Maybe (f x y ≡ f x' y')
lift-≟-2 {A} {B} {C} f {x} {.x} {y} {y'} (just refl) p = lift-≟-2-helper {A} {B} {C} {f} {x} {y} {y'} (p refl)
lift-≟-2 f nothing _ = nothing

lift-≟-2-helper-refl : ∀ {A B C f x y p} → p ≡ just refl → lift-≟-2-helper {A} {B} {C} {f} {x} {y} {y} p ≡ just refl
lift-≟-2-helper-refl refl = refl

lift-≟-2-refl : ∀ {A B C} f {x} {y} p q → p ≡ just refl → q refl ≡ just refl → lift-≟-2 {A} {B} {C} f {x} {x} {y} {y} p q ≡ just refl
lift-≟-2-refl {A} {B} {C} f {x} {y} ._ q refl q' = lift-≟-2-helper-refl {A} {B} {C} {f} {x} {y} {q refl} q'

lift-≟-3-helper : ∀ {A : Set} {B : A → Set} {C D} → {f : (x : A) → (y : B x) → C x y → D} → {x : A} → {y y' : B x} → {z : C x y} → {z' : C x y'} → Maybe (y ≡ y') → ((q : y ≡ y') → Maybe (transport2 C refl q z ≡ z')) → Maybe (f x y z ≡ f x y' z')
lift-≟-3-helper {A} {B} {C} {D} {f} {x} {y} {.y} {z} {z'} (just refl) q = lift-≟-2-helper {B x} {C x} {D} {f x} {y} {z} {z'} (q refl)
lift-≟-3-helper nothing q = nothing

lift-≟-3 : ∀ {A B C D} → (f : (x : A) → (y : B x) → C x y → D) → {x x' : A} → {y : B x} → {y' : B x'} → {z : C x y} → {z' : C x' y'} → Maybe (x ≡ x') → ((p : x ≡ x') → Maybe (transport B p y ≡ y')) → ((p : x ≡ x') → (q : transport B p y ≡ y') → Maybe (transport2 C p q z ≡ z')) → Maybe (f x y z ≡ f x' y' z')
lift-≟-3 {A} {B} {C} {D} f {x} {.x} {y} {y'} {z} {z'} (just refl) q r = lift-≟-3-helper {A} {B} {C} {D} {f} {x} {y} {y'} {z} {z'} (q refl) (r refl)
lift-≟-3 f nothing q r = nothing

lift-≟-3-helper-refl : ∀ {A B C D f x y z p q} → p ≡ just refl → q refl ≡ just refl → lift-≟-3-helper {A} {B} {C} {D} {f} {x} {y} {y} {z} {z} p q ≡ just refl
lift-≟-3-helper-refl {A} {B} {C} {D} {f} {x} {y} {z} {._} {q} refl q' = lift-≟-2-helper-refl {B x} {C x} {D} {f x} {y} {z} {q refl} q'

lift-≟-3-refl : ∀ {A B C D} f {x y z} p q r → p ≡ just refl → q refl ≡ just refl → r refl refl ≡ just refl → lift-≟-3 {A} {B} {C} {D} f {x} {x} {y} {y} {z} {z} p q r ≡ just refl
lift-≟-3-refl {A} {B} {C} {D} f {x} {y} {z} ._ q r refl q' r' = lift-≟-3-helper-refl {A} {B} {C} {D} {f} {x} {y} {z} {q refl} {r refl} q' r'

lift-≟-4-helper : ∀ {A : Set} {B : A → Set} {C : (x : A) → B x → Set} {D : (x : A) → (y : B x) → C x y → Set} {E} → {f : (x : A) → (y : B x) → (z : C x y) → (w : D x y z) → E} → {x : A} → {y y' : B x} → {z : C x y} → {z' : C x y'} → {w : D x y z} → {w' : D x y' z'} → Maybe (y ≡ y') → ((q : y ≡ y') → Maybe (transport2 C refl q z ≡ z')) → ((q : y ≡ y') → (r : transport2 C refl q z ≡ z') → Maybe (transport3 D refl q r w ≡ w')) → Maybe (f x y z w ≡ f x y' z' w')
lift-≟-4-helper {A} {B} {C} {D} {E} {f} {x} {y} {.y} {z} {z'} {w} {w'} (just refl) q r = lift-≟-3-helper {B x} {C x} {D x} {E} {f x} {y} {z} {z'} {w} {w'}
                                                                                           (q refl) (r refl)
lift-≟-4-helper nothing q r = nothing

lift-≟-5-helper : ∀ {A : Set} {B : A → Set} {C : (x : A) → B x → Set} {D : (x : A) → (y : B x) → C x y → Set} {E F} → {f : (x : A) → (y : B x) → (z : C x y) → (w : D x y z) → (v : E x y z w) → F} → {x : A} → {y y' : B x} → {z : C x y} → {z' : C x y'} → {w : D x y z} → {w' : D x y' z'} → {v : E x y z w} → {v' : E x y' z' w'} → Maybe (y ≡ y') → ((q : y ≡ y') → Maybe (transport2 C refl q z ≡ z')) → ((q : y ≡ y') → (r : transport2 C refl q z ≡ z') → Maybe (transport3 D refl q r w ≡ w')) → ((q : y ≡ y') → (r : transport2 C refl q z ≡ z') → (s : transport3 D refl q r w ≡ w') → Maybe (transport4 E refl q r s v ≡ v')) → Maybe (f x y z w v ≡ f x y' z' w' v')
lift-≟-5-helper {A} {B} {C} {D} {E} {F} {f} {x} {y} {.y} {z} {z'} {w} {w'} {v} {v'} (just refl) q r s
  = lift-≟-4-helper {B x} {C x} {D x} {E x} {F} {f x} {y} {z} {z'} {w}
      {w'} {v} {v'} (q refl) (r refl) (s refl)
lift-≟-5-helper nothing q r s = nothing

lift-≟-5 : ∀ {A B C D E F} → (f : (x : A) → (y : B x) → (z : C x y) → (w : D x y z) → (v : E x y z w) → F) → {x x' : A} → {y : B x} → {y' : B x'} → {z : C x y} → {z' : C x' y'} → {w : D x y z} → {w' : D x' y' z'} → {v : E x y z w} → {v' : E x' y' z' w'} → Maybe (x ≡ x') → ((p : x ≡ x') → Maybe (transport B p y ≡ y')) → ((p : x ≡ x') → (q : transport B p y ≡ y') → Maybe (transport2 C p q z ≡ z')) → ((p : x ≡ x') → (q : transport B p y ≡ y') → (r : transport2 C p q z ≡ z') → Maybe (transport3 D p q r w ≡ w')) → ((p : x ≡ x') → (q : transport B p y ≡ y') → (r : transport2 C p q z ≡ z') → (s : transport3 D p q r w ≡ w') → Maybe (transport4 E p q r s v ≡ v')) → Maybe (f x y z w v ≡ f x' y' z' w' v')
lift-≟-5 {A} {B} {C} {D} {E} {F} f {x} {.x} {y} {y'} {z} {z'} {w} {w'} {v} {v'} (just refl) q r s t = lift-≟-5-helper {A} {B} {C} {D} {E} {F} {f} {x} {y} {y'} {z} {z'} {w} {w'} {v} {v'} (q refl) (r refl) (s refl) (t refl)
lift-≟-5 f nothing q r s t = nothing

lift-≟-4-helper-refl : ∀ {A B C D E f x y z w p q r} → p ≡ just refl → q refl ≡ just refl → r refl refl ≡ just refl → lift-≟-4-helper {A} {B} {C} {D} {E} {f} {x} {y} {y} {z} {z} {w} {w} p q r ≡ just refl
lift-≟-4-helper-refl {A} {B} {C} {D} {E} {f} {x} {y} {z} {w} {._} {q} {r} refl q' r' = lift-≟-3-helper-refl {B x} {C x} {D x} {E} {f x} {y} {z} {w}
                                                                                         {q refl} {r refl} q' r'

lift-≟-5-helper-refl : ∀ {A B C D E F f x y z w v p q r s} → p ≡ just refl → q refl ≡ just refl → r refl refl ≡ just refl → s refl refl refl ≡ just refl → lift-≟-5-helper {A} {B} {C} {D} {E} {F} {f} {x} {y} {y} {z} {z} {w} {w} {v} {v} p q r s ≡ just refl
lift-≟-5-helper-refl {A} {B} {C} {D} {E} {F} {f} {x} {y} {z} {w} {v} {._} {q} {r} {s} refl q' r' s'
  = lift-≟-4-helper-refl {B x} {C x} {D x} {E x} {F} {f x} {y} {z} {w}
      {v} {q refl} {r refl} {s refl} q' r' s'

lift-≟-5-refl : ∀ {A B C D E F} f {x y z w v} p q r s t → p ≡ just refl → q refl ≡ just refl → r refl refl ≡ just refl → s refl refl refl ≡ just refl → t refl refl refl refl ≡ just refl → lift-≟-5 {A} {B} {C} {D} {E} {F} f {x} {x} {y} {y} {z} {z} {w} {w} {v} {v} p q r s t ≡ just refl
lift-≟-5-refl {A} {B} {C} {D} {E} {F} f {x} {y} {z} {w} {v} ._ q r s t refl q' r' s' t' = lift-≟-5-helper-refl {A} {B} {C} {D} {E} {F} {f} {x} {y} {z} {w} {v} {q refl} {r refl} {s refl} {t refl} q' r' s' t'

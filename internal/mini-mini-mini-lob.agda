{-# OPTIONS --without-K #-}
infixr 1 _‘→’_

mutual
  data Type : Set where
    _‘→’_ : Type → Type → Type
    ‘□’ : Type → Type

  data □ : Type → Set where
    Lӧb : ∀ {X} → □ (‘□’ X ‘→’ X) → □ X

mutual
  ⌞_⌟ : Type → Set
  ⌞ A ‘→’ B ⌟ = ⌞ A ⌟ → ⌞ B ⌟
  ⌞ ‘□’ T ⌟   = □ T

  ⌞_⌟t : ∀ {T : Type} → □ T → ⌞ T ⌟
  ⌞ (Lӧb □‘X’→X) ⌟t = ⌞ □‘X’→X ⌟t (Lӧb □‘X’→X)

lӧb : ∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = ⌞ Lӧb f ⌟t

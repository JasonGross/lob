{-# OPTIONS --without-K #-}
infixr 1 _‘→’_

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

mutual
  data Type : Set where
    _‘→’_ : Type → Type → Type
    ‘□’ : Type → Type
    ‘⊤’ : Type
    ‘⊥’ : Type

  data □ : Type → Set where
    Lӧb : ∀ {X} → □ (‘□’ X ‘→’ X) → □ X
    ‘tt’ : □ ‘⊤’

mutual
  ⌞_⌟ : Type → Set
  ⌞ A ‘→’ B ⌟ = ⌞ A ⌟ → ⌞ B ⌟
  ⌞ ‘□’ T ⌟   = □ T
  ⌞ ‘⊤’ ⌟     = ⊤
  ⌞ ‘⊥’ ⌟     = ⊥

  ⌞_⌟t : ∀ {T : Type} → □ T → ⌞ T ⌟
  ⌞ (Lӧb □‘X’→X) ⌟t = ⌞ □‘X’→X ⌟t (Lӧb □‘X’→X)
  ⌞ ‘tt’ ⌟t = tt

¬_ : Set → Set
¬ T = T → ⊥

‘¬’_ : Type → Type
‘¬’ T = T ‘→’ ‘⊥’

lӧb : ∀ {‘X’} → □ (‘□’ ‘X’ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = ⌞ Lӧb f ⌟t

incompleteness : ¬ □ (‘¬’ (‘□’ ‘⊥’))
incompleteness = lӧb

soundness : ¬ □ ‘⊥’
soundness x = ⌞ x ⌟t

non-emptyness : □ ‘⊤’
non-emptyness = ‘tt’

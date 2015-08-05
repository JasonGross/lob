{-# OPTIONS --without-K #-}
module well-typed-syntax-context-helpers where
open import common
open import well-typed-syntax
open import well-typed-syntax-helpers

□_ : Typ ε → Set
□_ T = Term {Γ = ε} T

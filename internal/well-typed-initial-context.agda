{-# OPTIONS --without-K #-}
module well-typed-initial-context where
open import well-typed-syntax
open import well-typed-syntax-helpers
import well-typed-initial-context-internal
import well-typed-syntax-interpreter-full
import well-typed-syntax-interpreter

abstract
  ε : Context
  ε = well-typed-initial-context-internal.ε

  transfer-Typ : Typ ε → Typ well-typed-initial-context-internal.ε
  transfer-Typ x = x

  transfer-Term : {T : Typ ε} → Term T → Term (transfer-Typ T)
  transfer-Term x = x

  transfer-Typ▻ : ∀ {A} → Typ (ε ▻ A) → Typ (well-typed-initial-context-internal.ε ▻ transfer-Typ A)
  transfer-Typ▻ x = x

  transfer-Term▻ : ∀ {A} → {T : Typ (ε ▻ A)} → Term T → Term (transfer-Typ▻ T)
  transfer-Term▻ x = x

  un▻-Typε▻⇓ : ∀ {A} {T : Typ ε} {x} → well-typed-syntax-interpreter-full.Typε▻⇓ (transfer-Typ▻ (W {ε} {A} T)) x → well-typed-syntax-interpreter-full.Typε⇓ (transfer-Typ T)
  un▻-Typε▻⇓ t = t

  ‘Context’ : Typ ε
  ‘Context’ = well-typed-initial-context-internal.‘Context’

  ‘Typ’ : Typ (ε ▻ ‘Context’)
  ‘Typ’ = well-typed-initial-context-internal.‘Typ’

  ‘Term’ : Typ (ε ▻ ‘Context’ ▻ ‘Typ’)
  ‘Term’ = well-typed-initial-context-internal.‘Term’

  ‘ε₀’ : Term ‘Context’
  ‘ε₀’ = well-typed-initial-context-internal.‘ε₀’

  ‘_▻_’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→'’ W ‘Context’)
  ‘_▻_’ = well-typed-initial-context-internal.‘_▻_’

  ‘‘Σ'’’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→’ W1 (W1 ‘Typ’) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’) ‘→'’ W ‘Typ’)
  ‘‘Σ'’’ = well-typed-initial-context-internal.‘‘Σ'’’

  ‘_‘’_’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→’ W1 (W1 ‘Typ’) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’) ‘→'’ ‘Term’ ‘→'’ W ‘Typ’)
  ‘_‘’_’ = well-typed-initial-context-internal.‘_‘’_’

  ‘_‘→’_’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→’ W1 (W1 ‘Typ’) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’) ‘→'’ W ‘Typ’)
  ‘_‘→’_’ = well-typed-initial-context-internal.‘_‘→’_’

  ‘W’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→’ W ‘Typ’ ‘→'’ W1 (W1 ‘Typ’) ‘’ un‘λ'∙’ (un‘λ∙’ ‘_▻_’))
  ‘W’ = well-typed-initial-context-internal.‘W’

  ‘context-pick-if'’ : Term (‘Context’ ‘→’ ‘Typ’ ‘→'’ W ‘Context’ ‘→’ W1 ‘Typ’ ‘→'’ W ‘Typ’)
  ‘context-pick-if'’ = well-typed-initial-context-internal.‘context-pick-if’

Typε⇓ : Typ ε → Set well-typed-syntax-interpreter.max-level
Typε⇓ T = well-typed-syntax-interpreter-full.Typε⇓ (transfer-Typ T)

Termε⇓ : {T : Typ ε} → Term T → Typε⇓ T
Termε⇓ t = well-typed-syntax-interpreter-full.Termε⇓ (transfer-Term t)

Typε▻⇓ : ∀ {A} → Typ (ε ▻ A) → Typε⇓ A → Set well-typed-syntax-interpreter.max-level
Typε▻⇓ T = well-typed-syntax-interpreter-full.Typε▻⇓ (transfer-Typ▻ T)

Termε▻⇓ : ∀ {A} → {T : Typ (ε ▻ A)} → Term T → (x : Typε⇓ A) → Typε▻⇓ T x
Termε▻⇓ t = well-typed-syntax-interpreter-full.Termε▻⇓ (transfer-Term▻ t)

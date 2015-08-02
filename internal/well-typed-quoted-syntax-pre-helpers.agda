{-# OPTIONS --without-K #-}
module well-typed-quoted-syntax-pre-helpers where
open import common
open import well-typed-syntax
open import well-typed-initial-context
open import well-typed-syntax-helpers
open import well-typed-syntax-context-helpers
open import well-typed-quoted-syntax-defs public

Wquote-distr-qcontext-extend : ∀ {Γ T T'}
  → Term {ε ▻ T'} (W (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝c))
  → Term {ε ▻ T'} (W (‘Typ’ ‘’ (⌜ Γ ⌝c ‘▻’ ⌜ T ⌝T)))
Wquote-distr-qcontext-extend = distrP⌜▻⌝ (λ Γ▻T → Term (W (‘Typ’ ‘’ Γ▻T)))

Wquote-undistr-qcontext-extend : ∀ {Γ T T'}
  → Term {ε ▻ T'} (W (‘Typ’ ‘’ (⌜ Γ ⌝c ‘▻’ ⌜ T ⌝T)))
  → Term {ε ▻ T'} (W (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝c))
Wquote-undistr-qcontext-extend {Γ} {T} {T'} t = distrP⌜▻⌝ (λ Γ▻T → Term (W (‘Typ’ ‘’ Γ▻T)) → Term {ε ▻ T'} (W (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝c))) (λ x → x) t

⌜W‘▻’⌝ = Wquote-distr-qcontext-extend
⌜W‘◅’⌝ = Wquote-undistr-qcontext-extend

quote-distr-qcontext-extend : ∀ {Γ T}
      → □ (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝c)
      → □ (‘Typ’ ‘’ (⌜ Γ ⌝c ‘▻’ ⌜ T ⌝T))
quote-distr-qcontext-extend x = SW (Wquote-distr-qcontext-extend (w x) ‘t’ ‘ε’)

quote-undistr-qcontext-extend : ∀ {Γ T}
      → □ (‘Typ’ ‘’ (⌜ Γ ⌝c ‘▻’ ⌜ T ⌝T))
      → □ (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝c)
quote-undistr-qcontext-extend x = SW (Wquote-undistr-qcontext-extend (w x) ‘t’ ‘ε’)

⌜‘▻’⌝ = quote-distr-qcontext-extend
⌜‘◅’⌝ = quote-undistr-qcontext-extend

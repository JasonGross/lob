{-# OPTIONS --without-K #-}
module lawvere-contextual-compressed-from-query
  {o a} {p {-r-} r₂}
  (𝒞 : Set o)
  (_[>]_ : 𝒞 → 𝒞 → Set a)
  (ι : ∀ {a} → a [>] a)
  (_⨾_ : ∀ {a b c} → a [>] b → b [>] c → a [>] c)
  (_×_ : 𝒞 → 𝒞 → 𝒞)
  (dup : ∀ {a} → (a [>] (a × a)))
  (_××_ : ∀ {a b c d} → (a [>] b) → (c [>] d) → ((a × c) [>] (b × d)))
  (𝟙 : 𝒞)
--  (□ : 𝒞 → 𝒞)
  (X : 𝒞)
  (S : 𝒞) -- S := Δ (Σ (□S) R → X)
  (P : (𝟙 [>] X) → Set p)
  (ΣP : 𝒞) -- Σ (□ X) P
  (f : ΣP [>] X)
--  (R : (𝟙 [>] S) → Set r)
  (ΣR : 𝒞) -- Σ (□ S) R
  (R₂ : (𝟙 [>] ΣR) → Set r₂)
  (ΣR₂ : 𝒞) -- Σ (□ ΣR) R₂
  (××ΣR₂P-but-this-needs-a-better-name : (l : ΣR [>] X) → (r : ∀ i → R₂ i → P (i ⨾ l)) → ΣR₂ [>] ΣP)
  (quot : ΣR [>] ΣR₂)
  (ϕ : (ΣR × ΣR₂) [>] ΣP) -- □ (S × □ S) [>] □ X
  (ϕ⁻¹ : (ΣR₂ [>] ΣP) → (𝟙 [>] ΣR))
  (f : ΣP [>] X)
  where

-- Σ_{m : a [>] X} (if a ≅ 𝟙 then P₁ m elif a ≅ S then P₂ m elif a ≅ R then P₃ m else ⊤)

query : ∀ {a} → a [>] ΣR → a [>] ΣR → a [>] ΣP
query f g = (dup ⨾ (f ×× (g ⨾ quot))) ⨾ ϕ


import lawvere-query 𝒞 _[>]_ _⨾_ ι (_[>] X) _⨾_ 𝟙 ΣP ΣR {!!} {!!} query f as lawvere-query -- QT QS {!□-map-T!} {!□-map-ψ!} query f as lawvere-query
{-
k : ΣR [>] X
k = ((dup ⨾ (id ×× quot)) ⨾ ϕ) ⨾ f

module _ (s₁ : ∀ (i : 𝟙 [>] ΣR) → R₂ i → P (i ⨾ k)) where
  pt : ΣR₂ [>] ΣP -- this needs a better name too
  pt = ××ΣR₂P-but-this-needs-a-better-name k s₁

  lawvere : 𝟙 [>] X
  lawvere = ϕ⁻¹ pt ⨾ k
-}

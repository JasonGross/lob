{-# OPTIONS --without-K #-}
module mini-lob-dependent where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixl 3 _‘’₁_
infixl 3 _‘’₂_
infixl 3 _‘’₃_
infixl 3 _‘’w_
infixl 3 _‘’w₁_
infixl 3 _‘’t₂_
infixl 3 _‘’t₃_
infixr 1 _‘→’_
infixl 3 _‘’ₐ_
infixr 1 _‘~’_

{-
(A : TypTerm), (v : ValTerm A) ⊢ H ty -- when we type the hole, we only get to know that there's some ValTerm in the context, but not anything about its structure
(A : TypTerm), (v : ValTerm A), H ⊢ T ty -- we build the type using the value of the hole
(A : TypTerm), (v : ValTerm A), 'h' : ValTerm H, ValTerm (A ~ "T[A, v, h]") ⊢ h : H -- when filling the hole, we get access to the fixpoint equation
(A : TypTerm), (v : ValTerm A), 'h' : ValTerm H, (e : ValTerm (A ~ "T[A, v, h]")), ValTerm ('h' = quote h[A, v, 'h', e]) ⊢ f : T[A, v, h[A, v, 'h', e]]
───────────────────────
⊢ Δ_T ty
⊢ löb f : Δ_T
⊢ iso : Δ_T ~ T['Δ_T', 'löb f', 'h[Δ_T, löb f, "h", iso]', 'iso', 'refl']
-}

mutual
  data Context : Set where
    ε : Context
    _▻_ : (Γ : Context) → Type Γ → Context

  data Type : Context → Set where
    _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
    _‘’₁_ : ∀ {Γ A B} → Type (Γ ▻ A ▻ B) → (a : Term A) → Type (Γ ▻ (B ‘’ a))
    _‘’₂_ : ∀ {Γ A B C} → Type (Γ ▻ A ▻ B ▻ C) → (a : Term A) → Type (Γ ▻ (B ‘’ a) ▻ (C ‘’₁ a))
    _‘’₃_ : ∀ {Γ A B C D} → Type (Γ ▻ A ▻ B ▻ C ▻ D) → (a : Term A) → Type (Γ ▻ (B ‘’ a) ▻ (C ‘’₁ a) ▻ (D ‘’₂ a))
    ‘Type’ : ∀ {Γ} → Type Γ
    ‘Term’ : ∀ {Γ} → Type (Γ ▻ ‘Type’)
    _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
    ‘⊤’ : ∀ {Γ} → Type Γ
    ‘⊥’ : ∀ {Γ} → Type Γ
    _‘~’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
    _‘≡’_ : ∀ {Γ A} → Term {Γ} A → Term {Γ} A → Type Γ
    wk₀ : ∀ {Γ A} → Type Γ → Type (Γ ▻ A)
    wk‘Term’_⌜‘var₁’⌝⌜‘var₀’⌝ₜ : Type (ε ▻ ‘Type’ ▻ ‘Term’) → Type (ε ▻ ‘Type’ ▻ ‘Term’)
    wk‘Term’‘var₂’‘~’wk_‘’₂⌜var₂⌝‘’₁⌜var₁⌝‘’var₀ : ∀ {H} → Type (ε ▻ ‘Type’ ▻ ‘Term’ ▻ H)
      → Type (ε ▻ ‘Type’ ▻ ‘Term’ ▻ wk‘Term’ H ⌜‘var₁’⌝⌜‘var₀’⌝ₜ)
    wk‘Term’‘var₁’‘≡’wk_‘’t₃⌜var₃⌝‘’t₂⌜var₂⌝‘’w₁⌜var₁⌝‘’w⌜var₀⌝
      : ∀ {H T}
          (h : Term {ε ▻ ‘Type’ ▻ ‘Term’ ▻ (wk‘Term’ H ⌜‘var₁’⌝⌜‘var₀’⌝ₜ) ▻ (wk‘Term’‘var₂’‘~’wk T ‘’₂⌜var₂⌝‘’₁⌜var₁⌝‘’var₀)} (wk₀ (wk₀ H)))
        → Type (ε ▻ ‘Type’ ▻ ‘Term’ ▻ (wk‘Term’ H ⌜‘var₁’⌝⌜‘var₀’⌝ₜ) ▻ (wk‘Term’‘var₂’‘~’wk T ‘’₂⌜var₂⌝‘’₁⌜var₁⌝‘’var₀))
    wk_‘’₂var₄‘’₁var₃‘’₀_‘’₃var₄‘’₂var₃‘’₁var₂‘’₀var₁
      : ∀ {H} T
          (h : Term {ε ▻ ‘Type’ ▻ ‘Term’ ▻ (wk‘Term’ H ⌜‘var₁’⌝⌜‘var₀’⌝ₜ) ▻ (wk‘Term’‘var₂’‘~’wk T ‘’₂⌜var₂⌝‘’₁⌜var₁⌝‘’var₀)} (wk₀ (wk₀ H)))
        → Type (ε ▻ ‘Type’ ▻ ‘Term’ ▻ (wk‘Term’ H ⌜‘var₁’⌝⌜‘var₀’⌝ₜ) ▻ (wk‘Term’‘var₂’‘~’wk T ‘’₂⌜var₂⌝‘’₁⌜var₁⌝‘’var₀) ▻ wk‘Term’‘var₁’‘≡’wk h ‘’t₃⌜var₃⌝‘’t₂⌜var₂⌝‘’w₁⌜var₁⌝‘’w⌜var₀⌝)
{-(A : TypTerm), (v : ValTerm A) ⊢ H ty -- when we type the hole, we only get to know that there's some ValTerm in the context, but not anything about its structure
(A : TypTerm), (v : ValTerm A), H ⊢ T ty -- we build the type using the value of the hole
(A : TypTerm), (v : ValTerm A), 'h' : ValTerm H, ValTerm (A ~ "T[A, v, h]") ⊢ h : H -- when filling the hole, we get access to the fixpoint equation
(A : TypTerm), (v : ValTerm A), 'h' : ValTerm H, (e : ValTerm (A ~ "T[A, v, h]")), ValTerm ('h' = quote h[A, v, 'h', e]) ⊢ f : T[A, v, h[A, v, 'h', e]]-}
    ‘Δ’ : ∀ (H : Type (ε ▻ ‘Type’ ▻ ‘Term’)) (T : Type (ε ▻ ‘Type’ ▻ ‘Term’ ▻ H))
            (h : Term {ε ▻ ‘Type’ ▻ ‘Term’ ▻ (wk‘Term’ H ⌜‘var₁’⌝⌜‘var₀’⌝ₜ) ▻ (wk‘Term’‘var₂’‘~’wk T ‘’₂⌜var₂⌝‘’₁⌜var₁⌝‘’var₀)} (wk₀ (wk₀ H)))
          → Term {ε ▻ ‘Type’ ▻ ‘Term’ ▻ (wk‘Term’ H ⌜‘var₁’⌝⌜‘var₀’⌝ₜ) ▻ (wk‘Term’‘var₂’‘~’wk T ‘’₂⌜var₂⌝‘’₁⌜var₁⌝‘’var₀) ▻ wk‘Term’‘var₁’‘≡’wk h ‘’t₃⌜var₃⌝‘’t₂⌜var₂⌝‘’w₁⌜var₁⌝‘’w⌜var₀⌝} (wk T ‘’₂var₄‘’₁var₃‘’₀ h ‘’₃var₄‘’₂var₃‘’₁var₂‘’₀var₁)
          → Type ε

  data Term : {Γ : Context} → Type Γ → Set where
    ⌜_⌝ : Type ε → Term {ε} ‘Type’
    ⌜_⌝ₜ : ∀ {T} → Term {ε} T → Term {ε} (‘Term’ ‘’ ⌜ T ⌝)
    ⌜_⌝ₜ₂ : ∀ {H A a} → Term {ε} (H ‘’₁ ⌜ A ⌝ ‘’ ⌜ a ⌝ₜ) → Term {ε} (wk‘Term’ H ⌜‘var₁’⌝⌜‘var₀’⌝ₜ ‘’₁ ⌜ A ⌝ ‘’ ⌜ a ⌝ₜ)
    ⌜_⌝ₜ₃ : ∀ {H A a T ‘h’}
      → Term {ε} (A ‘~’ T ‘’₂ ⌜ A ⌝ ‘’₁ ⌜ a ⌝ₜ ‘’ ‘h’)
      → Term {ε} (wk‘Term’‘var₂’‘~’wk T ‘’₂⌜var₂⌝‘’₁⌜var₁⌝‘’var₀ ‘’₂ ⌜ A ⌝ ‘’₁ ⌜ a ⌝ₜ ‘’ (⌜_⌝ₜ₂ {H} {A} {a} ‘h’))
    _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
    _‘’w_ : ∀ {Γ A B} → Term {Γ ▻ A} (wk₀ B) → Term A → Term B
    _‘’w₁_ : ∀ {Γ A B C} → Term {Γ ▻ A ▻ B} (wk₀ (wk₀ C)) → (a : Term A) → Term {Γ ▻ B ‘’ a} (wk₀ C)
    _‘’t₂_ : ∀ {Γ A B C D} → Term {Γ ▻ A ▻ B ▻ C} (wk₀ (wk₀ D)) → (a : Term A) → Term {Γ ▻ B ‘’ a ▻ C ‘’₁ a} (wk₀ (wk₀ (D ‘’ a)))
    _‘’t₃_ : ∀ {Γ A B C D E} → Term {Γ ▻ A ▻ B ▻ C ▻ D} (wk₀ (wk₀ E)) → (a : Term A) → Term {Γ ▻ B ‘’ a ▻ C ‘’₁ a ▻ D ‘’₂ a} (wk₀ (wk₀ (E ‘’₁ a)))
    ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’
    ‘refl~’ : ∀ {Γ T} → Term {Γ} (T ‘~’ T)
    ‘refl’ : ∀ {Γ T} {t : Term {Γ} T} → Term {Γ} (t ‘≡’ t)
    {-⊢ löb f : Δ_T
⊢ iso : Δ_T ~ T['Δ_T', 'löb f', 'h[Δ_T, löb f, "h", iso]', 'iso', 'refl']
-}
    löb : ∀ {H T h} f → Term (‘Δ’ H T h f)
    ‘löb-h’ : ∀ {H T h} f → Term (wk‘Term’ H ⌜‘var₁’⌝⌜‘var₀’⌝ₜ ‘’₁ ⌜ ‘Δ’ H T h f ⌝ ‘’ ⌜ löb f ⌝ₜ)
    ‘iso’ : ∀ {H T h f} → Term (wk‘Term’‘var₂’‘~’wk T ‘’₂⌜var₂⌝‘’₁⌜var₁⌝‘’var₀ ‘’₂ ⌜ ‘Δ’ H T h f ⌝ ‘’₁ ⌜ löb f ⌝ₜ ‘’ ‘löb-h’ f)
    iso : ∀ {H T h f} → Term (‘Δ’ H T h f ‘~’ (T ‘’₂ ⌜ ‘Δ’ H T h f ⌝ ‘’₁ ⌜ löb f ⌝ₜ ‘’ ((h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ) ‘’w₁ ‘löb-h’ f ‘’w ‘iso’)))
    ‘löb-h-refl’ : ∀ {H T h f}
      → Term {ε} ((h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’)
                 ‘≡’
                 (h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ⌜ h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’ ⌝ₜ₂ ‘’w ⌜ iso ⌝ₜ₃))

max-level : Level
max-level = lzero

Context⇓ : (Γ : Context) → Set max-level
Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level

Context⇓ ε = ⊤
Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓

Type⇓ (‘Type’ {Γ}) Γ⇓ = Lifted (Type Γ)
Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
Type⇓ (T ‘’₁ x) (Γ⇓ , A) = Type⇓ T ((Γ⇓ , Term⇓ x Γ⇓) , A)
Type⇓ (T ‘’₂ x) ((Γ⇓ , A) , B) = Type⇓ T (((Γ⇓ , Term⇓ x Γ⇓) , A) , B)
Type⇓ (T ‘’₃ x) (((Γ⇓ , A) , B) , C) = Type⇓ T ((((Γ⇓ , Term⇓ x Γ⇓) , A) , B) , C)
Type⇓ (‘Term’ {Γ}) (Γ⇓ , lift T) = Lifted (Term {Γ} T)
Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
Type⇓ ‘⊤’ Γ⇓ = ⊤
Type⇓ ‘⊥’ Γ⇓ = ⊥
Type⇓ (A ‘~’ B) Γ⇓ = Type⇓ A Γ⇓ ~ Type⇓ B Γ⇓
Type⇓ (x ‘≡’ y) Γ⇓ = Term⇓ x Γ⇓ ≡ Term⇓ y Γ⇓
Type⇓ (wk₀ T) (Γ⇓ , _) = Type⇓ T Γ⇓
Type⇓ wk‘Term’ T ⌜‘var₁’⌝⌜‘var₀’⌝ₜ ((Γ⇓ , lift A) , lift a ) = Term (T ‘’₁ ⌜ A ⌝ ‘’ ⌜ a ⌝ₜ)
Type⇓ wk‘Term’‘var₂’‘~’wk T ‘’₂⌜var₂⌝‘’₁⌜var₁⌝‘’var₀ (((Γ⇓ , lift A) , lift a) , h)
  = Term (A ‘~’ T ‘’₂ ⌜ A ⌝ ‘’₁ ⌜ a ⌝ₜ ‘’ h)
Type⇓ wk‘Term’‘var₁’‘≡’wk h ‘’t₃⌜var₃⌝‘’t₂⌜var₂⌝‘’w₁⌜var₁⌝‘’w⌜var₀⌝ ((((Γ⇓ , lift A) , lift a) , ‘h’) , ‘e’)
  = Term (‘h’ ‘≡’ (h ‘’t₃ ⌜ A ⌝ ‘’t₂ ⌜ a ⌝ₜ ‘’w₁ ⌜ ‘h’ ⌝ₜ₂ ‘’w ⌜ ‘e’ ⌝ₜ₃))
Type⇓ wk T ‘’₂var₄‘’₁var₃‘’₀ h ‘’₃var₄‘’₂var₃‘’₁var₂‘’₀var₁ (((((Γ⇓ , A) , a) , ‘h’) , ‘e’) , p)
  = Type⇓ T (((Γ⇓ , A) , a) , Term⇓ h ((((Γ⇓ , A) , a) , ‘h’) , ‘e’))
Type⇓ (‘Δ’ H T h f) Γ⇓ = Type⇓ T (((
  Γ⇓
  , lift (‘Δ’ H T h f))
  , lift (löb f))
  , Term⇓ h ((((Γ⇓
            , lift (‘Δ’ H T h f))
            , lift (löb f))
            , h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’)
            , iso))


-- Work around AGDABUG(https://github.com/agda/agda/issues/6181)
Term⇓-helper1-cast
  : ∀ {H T h f} Γ⇓
      → Term⇓ h ((((Γ⇓ , lift (‘Δ’ H T h f)) , lift (löb f)) , h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’) , iso)
        ≡
        Term⇓ h ((((Γ⇓ , lift (‘Δ’ H T h f)) , lift (löb f)) , h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’) , iso)
      → Type⇓ ((h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’)
              ‘≡’
              (h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ⌜ h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’ ⌝ₜ₂ ‘’w ⌜ iso ⌝ₜ₃)) Γ⇓

Term⇓-helper2-cast
  : ∀ {H T h f} Γ⇓
      → Type⇓ T (((Γ⇓ , lift (‘Δ’ H T h f)) , lift (löb f)) , Term⇓ h ((((Γ⇓ , lift (‘Δ’ H T h f)) , lift (löb f)) , h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’) , iso))
        ~
        Type⇓ T (((Γ⇓ , lift (‘Δ’ H T h f)) , lift (löb f)) , Term⇓ h ((((Γ⇓ , lift (‘Δ’ H T h f)) , lift (löb f)) , h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’) , iso))
      → Type⇓ (‘Δ’ H T h f ‘~’ (T ‘’₂ ⌜ ‘Δ’ H T h f ⌝ ‘’₁ ⌜ löb f ⌝ₜ ‘’ ((h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ) ‘’w₁ ‘löb-h’ f ‘’w ‘iso’))) Γ⇓

Term⇓ ⌜ x ⌝ Γ⇓ = lift x
Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
Term⇓ ‘tt’ Γ⇓ = tt
Term⇓ ⌜ t ⌝ₜ Γ⇓ = lift t
Term⇓ ⌜ t ⌝ₜ₂ Γ⇓ = t
Term⇓ ⌜ t ⌝ₜ₃ Γ⇓ = t
Term⇓ (f ‘’w a) Γ⇓ = Term⇓ f (Γ⇓ , Term⇓ a Γ⇓)
Term⇓ (f ‘’w₁ a) (Γ⇓ , b) = Term⇓ f ((Γ⇓ , Term⇓ a Γ⇓) , b)
Term⇓ (f ‘’t₂ a) ((Γ⇓ , b) , c) = Term⇓ f (((Γ⇓ , Term⇓ a Γ⇓) , b) , c)
Term⇓ (f ‘’t₃ a) (((Γ⇓ , b) , c) , d) = Term⇓ f ((((Γ⇓ , Term⇓ a Γ⇓) , b) , c) , d)
Term⇓ ‘refl~’ Γ⇓ = refl~
Term⇓ ‘refl’ Γ⇓ = refl
Term⇓ (löb {H} {T} {h} f) Γ⇓
  = Term⇓ f (((((Γ⇓ , lift (‘Δ’ H T h f)) , lift (löb f)) , h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’) , iso) , ‘löb-h-refl’)
Term⇓ (‘löb-h’ {H} {T} {h} f) Γ⇓ = h ‘’t₃ ⌜ ‘Δ’ H T h f ⌝ ‘’t₂ ⌜ löb f ⌝ₜ ‘’w₁ ‘löb-h’ f ‘’w ‘iso’
Term⇓ ‘iso’ Γ⇓ = iso
Term⇓ (iso {H} {T} {h} {f}) Γ⇓ = Term⇓-helper2-cast {H} {T} {h} {f} Γ⇓ refl~
Term⇓ (‘löb-h-refl’ {H} {T} {h} {f}) Γ⇓ = Term⇓-helper1-cast {H} {T} {h} {f} Γ⇓ refl

Term⇓-helper1-cast _ x = x
Term⇓-helper2-cast _ x = x

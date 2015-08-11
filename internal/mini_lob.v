Require Import Coq.Strings.String.
Require Template.Ast.
Require Import Lob.Notations.
Require Import Lob.TermOperations.
Set Implicit Arguments.
Set Universe Polymorphism.

Local Open Scope list_scope.

Inductive Precontext : Set := empty_context | context_extend (c : Precontext) (T : Ast.term).
Bind Scope context_scope with Precontext.
Delimit Scope context_scope with ctx.
Notation ε := empty_context.
Notation "Γ ▻ T" := (context_extend Γ T) : context_scope.

(*
Require Import Template.Template.
Inductive has_type : Precontext -> Ast.term -> Ast.term -> Set := .
Quote Definition qSete := { x : Ast.term & { s : _ & has_type ε x (Ast.tSort s) } }.
Print qSete.
 *)
Notation qSete
  := (Ast.tApp (Ast.tInd (Ast.mkInd "Coq.Init.Specif.sigT" 0))
               (Ast.tInd (Ast.mkInd "Template.Ast.term" 0)
                         :: Ast.tLambda (Ast.nNamed "x"%string)
                         (Ast.tInd (Ast.mkInd "Template.Ast.term" 0))
                         (Ast.tApp (Ast.tInd (Ast.mkInd "Coq.Init.Specif.sigT" 0))
                                   (Ast.tInd (Ast.mkInd "Template.Ast.sort" 0)
                                             :: Ast.tLambda (Ast.nNamed "s"%string)
                                             (Ast.tInd (Ast.mkInd "Template.Ast.sort" 0))
                                             (Ast.tApp (Ast.tInd (Ast.mkInd "Top.has_type" 0))
                                                       (Ast.tConstruct (Ast.mkInd "Top.Precontext" 0) 0
                                                                       :: Ast.tRel 1
                                                                       :: Ast.tApp
                                                                       (Ast.tConstruct
                                                                          (Ast.mkInd "Template.Ast.term" 0) 4)
                                                                       (Ast.tRel 0 :: nil) :: nil)) :: nil)) :: nil))
       (only parsing).

Inductive has_type : Precontext -> Ast.term -> Ast.term -> Set := .

Notation Typ Γ := { T : _ & { s : _ & has_type Γ T (Ast.tSort s) } }.
Notation "‘Typε’" := { qt : Ast.term & has_type ε qt qSete }.


Axiom cheat' : forall {T}, T.
Notation quoteT := ( -> { qT : _ & has_type ε qT qSete }).
Definition quote : { T : _ & { s : _ & has_type ε T (Ast.tSort s) } } -> { qT : _ & has_type ε qT qSete }
  := cheat'.


Goal True.
  quote_term (forall X (t : Ast.term) (

    Lӧb : ∀ {X} → Term {ε} (‘□’ ‘’ ⌜ X ⌝ ‘→’ X) -> Term {ε} X




| htLob : forall ctx, has_type ctx (Ast.tConst "Lob.mini_lob.Lӧb") (Ast.tProd Ast.nAnon.

Delimit Scope typ_scope with typ.
Delimit Scope term_scope with term.
Bind Scope term_scope with Ast.term.

Notation "x ‘’ y" := (subst_n_name x%typ y%term (Some 0%nat) Ast.nAnon) : typ_scope.

Fixpoint htSubst ctx A s x y {struct x}
: has_type (ctx ▻ A) x (Ast.tSort s)
  -> has_type ctx y A
  -> has_type ctx (x ‘’ y)%typ (Ast.tSort s).
Proof.
  intros H H'; revert H.
  destruct x; simpl.
  { destruct n; simpl.
  unfold subst_n_name.

{-# OPTIONS --without-K #-}
module mini-lob where
open import common

infixl 2 _▻_
infixl 3 _‘’_
infixr 1 _‘→’_
infixl 3 _‘’ₐ_

mutual
  data Context : Set where
    ε : Context
    _▻_ : (Γ : Context) → Type Γ → Context

  data Type : Context → Set where
    _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
    ‘Typeε’ : Type ε
    ‘□’ : Type (ε ▻ ‘Typeε’)
    _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
    ‘⊤’ : ∀ {Γ} → Type Γ
    ‘⊥’ : ∀ {Γ} → Type Γ

  data Term : {Γ : Context} → Type Γ → Set where
    ⌜_⌝ : Type ε → Term {ε} ‘Typeε’
    _‘’ₐ_ : ∀ {Γ A B} → Term {Γ} (A ‘→’ B) → Term {Γ} A → Term {Γ} B
    Lӧb : ∀ {X} → Term {ε} (‘□’ ‘’ ⌜ X ⌝ ‘→’ X) -> Term {ε} X
    ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’

□ : Type ε → Set _
□ = Term {ε}

max-level : Level
max-level = lzero

mutual
  Context⇓ : (Γ : Context) → Set (lsuc max-level)
  Context⇓ ε = ⊤
  Context⇓ (Γ ▻ T) = Σ (Type⇓ {Γ} T)

  Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set max-level
  Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
  Type⇓ ‘Typeε’ Γ⇓ = Lifted (Type ε)
  Type⇓ ‘□’ Γ⇓ = Lifted (Term {ε} (lower (Σ.proj₂ Γ⇓)))
  Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
  Type⇓ ‘⊤’ Γ⇓ = ⊤
  Type⇓ ‘⊥’ Γ⇓ = ⊥

  Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓
  Term⇓ ⌜ x ⌝ Γ⇓ = lift x
  Term⇓ (f ‘’ₐ x) Γ⇓ = Term⇓ f Γ⇓ (Term⇓ x Γ⇓)
  Term⇓ (Lӧb □‘X’→X) Γ⇓ = Term⇓ □‘X’→X Γ⇓ (lift (Lӧb □‘X’→X))
  Term⇓ ‘tt’ Γ⇓ = tt

⌞_⌟ : Type ε → Set _
⌞ T ⌟ = Type⇓ T tt

‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
‘¬’ T = T ‘→’ ‘⊥’

lӧb : ∀ {‘X’} → □ (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = Term⇓ (Lӧb f) tt

incompleteness : ¬ □ (‘¬’ (‘□’ ‘’ ⌜ ‘⊥’ ⌝))
incompleteness = lӧb

soundness : ¬ □ ‘⊥’
soundness x = Term⇓ x tt

non-emptyness : Σ (λ T → □ T)
non-emptyness = ‘⊤’ , ‘tt’

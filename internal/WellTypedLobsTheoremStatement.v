(** The statement of the theorem *)
Require Export Lob.Notations.

Module Type LobContext.
  Axiom Context : Type.

  Delimit Scope context_scope with ctx.
  Bind Scope context_scope with Context.

  Axiom Typ : Context -> Type.

  Delimit Scope typ_scope with typ.
  Bind Scope typ_scope with Typ.

  Axiom Term : forall {Γ}, Typ Γ -> Type.

  Delimit Scope term_scope with term.
  Bind Scope term_scope with Term.

  Axiom empty_context : Context.
  Notation ε := empty_context.

  Axiom context_extend : forall Γ, Typ Γ -> Context.
  Notation "Γ ▻ x" := (@context_extend Γ x).

  Notation "□ T" := (@Term ε T) (at level 0).

  Axiom substTyp : forall {Γ A}, Typ (Γ ▻ A) -> Term A -> Typ Γ.
  Notation "f ‘’ x" := (@substTyp _ _ f x) : typ_scope.
  Axiom weakenTyp : forall {Γ A}, Typ Γ -> Typ (Γ ▻ A).
  Axiom substTerm : forall {Γ A} {B : Typ (Γ ▻ A)}
                           (b : Term B)
                           (a : Term A),
                      Term (substTyp B a).
  Notation "f ‘’ x" := (@substTerm _ _ _ f x) : term_scope.
  Axiom substTyp1 : forall {Γ A B}
                           (C : Typ (Γ ▻ A ▻ B))
                           (a : Term A),
                      Typ (Γ ▻ substTyp B a).
  Notation "f ‘’₁ x" := (@substTyp1 _ _ _ f x) : typ_scope.


  Local Open Scope typ_scope.

  Axiom qContext : Typ ε.
  Notation "‘Context’" := qContext : typ_scope.

  Axiom qTyp : Typ (ε ▻ ‘Context’).
  Notation "‘Typ’" := qTyp : typ_scope.

  Axiom VAR0 : forall {Γ T}, @Term (Γ ▻ T) (weakenTyp T).
  Notation "‘VAR₀’" := VAR0 : term_scope.

  Axiom quote_context : Context -> Term ‘Context’.
  Definition qempty_context := quote_context ε.
  Notation "‘ε’" := qempty_context : term_scope.
  Notation "⌜ x ⌝" := (quote_context x) : context_scope.

  Axiom qTerm : Typ (ε ▻ ‘Context’ ▻ ‘Typ’).
  Notation "‘Term’" := qTerm : typ_scope.

  Definition qbox := (substTyp1 ‘Term’ ‘ε’).
  Notation "‘□’" := qbox : typ_scope.

  Axiom quote_typ : forall {Γ}, Typ Γ -> □ (‘Typ’ ‘’ ⌜ Γ ⌝%ctx).
  Notation "⌜ x ⌝" := (quote_typ x%typ) : typ_scope.
  Axiom quote_term : forall {Γ} {A : Typ Γ}, Term A -> □ (‘Term’ ‘’₁ ⌜ Γ ⌝%ctx ‘’ ⌜ A ⌝%typ).
  Notation "⌜ x ⌝" := (quote_term x%term) : term_scope.
End LobContext.

Module Type LobHypotheses (Export LC : LobContext).
  Axiom X : Type.
  Axiom qX : Typ ε.
  Notation "‘X’" := qX : typ_scope.

  Axiom f : □ ‘X’ -> X.
  Axiom qf : @Term (ε ▻ (‘□’ ‘’ ⌜ ‘X’ ⌝%typ)) (weakenTyp ‘X’).
  Notation "‘f’" := qf : term_scope.
End LobHypotheses.

Module Type LobsTheorem (LC : LobContext) (Export LH : LobHypotheses LC).
  Axiom lob : X.
End LobsTheorem.

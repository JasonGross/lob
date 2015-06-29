(** The statement of the theorem *)
Require Export Lob.Notations.

Module Type LobContext.
  Axiom Preterm : Type.

  Delimit Scope preterm_scope with preterm.
  Bind Scope preterm_scope with Preterm.

  Axiom box : Preterm -> Type.

  Delimit Scope well_typed_term_scope with wtt.
  Bind Scope well_typed_term_scope with box.

  Notation "□ T" := (box T) (at level 0).



  Axiom qbox : Preterm.
  Notation "‘□’" := qbox.

  Axiom tProd : Preterm -> Preterm -> Preterm.
  Notation "x ‘→’ y" := (tProd x y) : preterm_scope.

  Axiom tApp : Preterm -> Preterm -> Preterm.
  Notation "x ‘’ y" := (tApp x y) : preterm_scope.

  Axiom quote : Preterm -> Preterm.
  Notation "⌜ x ⌝" := (quote x).
End LobContext.

Module Type LobHypotheses (Export LC : LobContext).
  Axiom X : Type.
  Axiom qX : Preterm.
  Notation "‘X’" := qX : preterm_scope.

  Axiom f : □ ‘X’ -> X.
  Axiom wtt_qf : □ ((‘□’ ‘’ ⌜ ‘X’ ⌝) ‘→’ ‘X’).
End LobHypotheses.

Module Type LobsTheorem (LC : LobContext) (Export LH : LobHypotheses LC).
  Axiom lob : X.
End LobsTheorem.

Require Import Coq.Setoids.Setoid Coq.Classes.CMorphisms.
Require Export Lob.Notations Lob.LobsTheoremStatement Lob.LobsTheoremPreProof.

Require Import Template.Template.

Require Import Coq.Strings.String.
Require Import Coq.Program.Program.
Require Import Coq.PArith.BinPos.
Local Open Scope string_scope.
Local Open Scope positive_scope.

Require Export Lob.quote_term.
(*Require Export Lob.quote_has_type.*)
Require Export Lob.conversion.

Axiom proof_admitted : False.
Ltac admit' := case proof_admitted.

Notation "( x ; y )" := (existT _ x y).
Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Notation "x .2" := (projT2 x) (at level 3, format "x '.2'").

Module LC <: LobExtendedContext.
  Definition Preterm := Ast.term.
  Definition Context : Type := Context.

  Delimit Scope context_scope with ctx.
  Bind Scope context_scope with Context.

  Definition empty_context : Context := ε.
  Notation ε := empty_context.
  Definition context_extend : Context -> Preterm -> Context
    := fun Γ T => context_extend Γ (Ast.nAnon, T).
  Notation "Γ ▻ x" := (context_extend Γ x).

  Delimit Scope preterm_scope with preterm.
  Bind Scope preterm_scope with Preterm.

  Global Open Scope preterm_scope.

  Definition box' (Γ : Context) (T : Preterm) : Type
  := { t : Preterm & has_type Γ t T }.

  Definition box : Preterm -> Type
    := box' ε.

  Delimit Scope well_typed_term_scope with wtt.
  Bind Scope well_typed_term_scope with box'.
  Bind Scope well_typed_term_scope with box.

  Notation "□ T" := (box T).


  Definition qbox : Preterm.
  Proof.
    let term := (eval cbv delta in box) in
    quote_term term (fun x => exact x).
  Defined.
  Notation "‘□’" := qbox.

  Definition tProd : Preterm -> Preterm -> Preterm
    := Ast.tProd Ast.nAnon.
  Notation "x ‘→’ y" := (tProd x y) : preterm_scope.

  Definition tApp : Preterm -> Preterm -> Preterm
    := fun f x => Ast.tApp f [x].
  Notation "x ‘’ y" := (tApp x y) : preterm_scope.

  Definition quote : Preterm -> Preterm
    := quote.
  Notation "⌜ x ⌝" := (quote x).


  Delimit Scope well_typed_term_scope with wtt.
  Bind Scope well_typed_term_scope with box'.
End LC.

Module PRP <: PretermReflectionPrimitives LC.
  Definition qPreterm := term'.
  Notation "‘Preterm’" := qPreterm : preterm_scope.

  Definition qquote : LC.Preterm.
  Proof.
    let t := (eval cbv beta delta [qO qS qEmptyString qString qnAnon qAscii qnil qcons qmkdef qtInd qtFix qtCase qtUnknown qtRel qtConstruct qtEvar qtMeta qtVar qtApp qtConst qtSort qtCast qtProd inductive_quotable quote_ascii bool_quotable quote_bool (*quote_string quote_positive quote_nat*) ident_quotable quote_ident quote_name nat_quotable name_quotable quote quote_term sort_quotable cast_kind_quotable quote_sort qsSet qsProp qsType universe_quotable quote_inductive qmkInd] in quote_term) in
    quote_term t (fun x => exact x).
  Defined.
  Notation "‘quote’" := qquote : preterm_scope.
End PRP.

Module PP <: PretermPrimitives LC.
  Export LC PRP.
  Definition tLambda : Preterm -> Preterm -> Preterm
    := Ast.tLambda Ast.nAnon.
  Definition qtApp : Preterm
    := tLambda ‘Preterm’ (tLambda ‘Preterm’ (Ast.tApp qtApp [Ast.tRel 1; (Ast.tApp qcons [‘Preterm’; Ast.tRel 0; Ast.tApp qnil [‘Preterm’]])])).

  Notation "‘App’" := qtApp : preterm_scope.

  Definition qtProd : Preterm -> Preterm -> Preterm
    := fun A B => (qtProd ‘’ qnAnon ‘’ A ‘’ B)%preterm.
  Notation "x ‘‘→’’ y" := (qtProd x y) : preterm_scope.

  Definition tVar0 : Preterm
    := Ast.tRel 0.
  Notation "‘VAR₀’" := tVar0.

  Definition ttVar0 {Γ T} : box' (Γ ▻ T) T.
  Proof.
    refine (tVar0; _).
    apply has_type_tRel_0.
  Defined.
  Notation "‘‘VAR₀’’" := ttVar0 : well_typed_term_scope.
End PP.

Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
    | [ H : T |- _ ] => fail 1
    | _ => pose proof defn
  end.

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail 0 tac "succeeds"; [](* test for [t] solved all goals *)).

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").


Module TR <: TypingRules LC PP.
  Export LC PP.
  Definition capture_avoiding_subst_0 : forall (in_term : Preterm)
                                               (new_value : Preterm),
                                          Preterm
    := fun in_term new_value
       => subst_n_name in_term new_value (Some 0%nat) Ast.nAnon.
  Notation "x [ 0 ↦ y ]" := (capture_avoiding_subst_0 x y).
  Definition convertible : Context -> Preterm -> Preterm -> Type
    := convertible.
  Definition box'_respectful : forall {Γ A B},
                                 convertible Γ A B
                                 -> box' Γ A
                                 -> box' Γ B.
  Proof.
    intros Γ A B H [a Ha].
    exists a.
    eapply has_type_conv_subst; try eassumption.
  Defined.

  Global Instance convertible_refl : forall {Γ}, Reflexive (convertible Γ) := conv_refl.
  Global Instance convertible_sym : forall {Γ}, Symmetric (convertible Γ) := conv_sym.
  Global Instance convertible_trans : forall {Γ}, Transitive (convertible Γ) := conv_trans.
  Definition convertible_beta_app_lambda
  : forall Γ A f a,
      convertible Γ (tApp (tLambda A f) a) (capture_avoiding_subst_0 f a).
  Proof.
    intros; eapply conv_beta.
  Defined.
  Definition convertible__capture_avoiding_subst_0__tApp
  : forall Γ A B x,
      convertible Γ ((A ‘’ B) [ 0 ↦ x ]) ((A [ 0 ↦ x ]) ‘’ (B [ 0 ↦ x ])).
  Proof.
    reflexivity.
  Defined.
  Definition convertible__capture_avoiding_subst_0__qtProd
  : forall Γ A B x,
      convertible Γ ((A ‘‘→’’ B) [ 0 ↦ x ]) ((A [ 0 ↦ x ]) ‘‘→’’ (B [ 0 ↦ x ])).
  Proof.
    reflexivity.
  Defined.
  Definition convertible__capture_avoiding_subst_0__tVar0
  : forall Γ x,
      convertible Γ (‘VAR₀’ [ 0 ↦ x ]) x.
  Proof.
    reflexivity.
  Defined.

  Global Instance tApp_Proper_convertible
  : forall Γ,
      Proper (convertible Γ ==> convertible Γ ==> convertible Γ) tApp.
  Proof.
    repeat intro; apply conv_tApp_respectful; assumption.
  Defined.
  Global Instance qtProd_Proper_convertible
  : forall Γ,
      Proper (convertible Γ ==> convertible Γ ==> convertible Γ) qtProd.
  Proof.
    repeat intro.
    unfold qtProd.
    apply tApp_Proper_convertible; [ | assumption ].
    apply tApp_Proper_convertible; [ reflexivity | assumption ].
  Defined.
  Definition convertible__quote__qtProd
  : forall Γ A B,
      convertible Γ (⌜ A ‘→’ B ⌝) (⌜ A ⌝ ‘‘→’’ ⌜ B ⌝).
  Proof.
    repeat intro.
    simpl.
    unfold qtProd, tApp; simpl.
    symmetry.
    apply conv_tApp_cons2.
    apply conv_tApp_cons2.
    reflexivity.
  Defined.

  Definition convertible__qtApp__closed
  : forall Γ x,
      convertible Γ (‘App’ [ 0 ↦ x ]) (‘App’).
  Proof.
    reflexivity.
  Defined.

  Create HintDb t_quote_db discriminated.

  Local Ltac t_quote0 tac :=
    repeat match goal with
             | _ => progress simpl
             | _ => progress intros
             | _ => reflexivity
             | _ => apply tApp_Proper_convertible; [ solve [ tac ] | ]
             | _ => apply tApp_Proper_convertible; [ | solve [ tac ] ]
             | [ |- convertible _ (Ast.tApp _ (_::_::_)%list) _ ] => apply conv_tApp_cons1
             | [ |- convertible _ _ (Ast.tApp _ (_::_::_)%list) ] => symmetry; apply conv_tApp_cons1; symmetry
             | _ => progress change conversion.convertible with convertible
           end.
  Local Ltac t_quote :=
    repeat match goal with
             | _ => progress t_quote0 t_quote
             | _ => solve [ eauto with nocore t_quote_db ]
           end.

  Definition convertible__quote_nat__closed_helper {Γ A x}
  : forall n n', convertible Γ (subst_n_name (quote_nat A) x n n') (quote_nat A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve convertible__quote_nat__closed_helper : t_quote_db.

  Definition convertible__quote_bool__closed_helper {Γ A x}
  : forall n n', convertible Γ (subst_n_name (quote_bool A) x n n') (quote_bool A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve convertible__quote_bool__closed_helper : t_quote_db.

  Definition convertible__quote_ascii__closed_helper {Γ A x}
  : forall n n', convertible Γ (subst_n_name (quote_ascii A) x n n') (quote_ascii A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve convertible__quote_ascii__closed_helper : t_quote_db.

  Definition convertible__quote_ident__closed_helper {Γ A x}
  : forall n n', convertible Γ (subst_n_name (quote_ident A) x n n') (quote_ident A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve convertible__quote_ident__closed_helper : t_quote_db.

  Definition convertible__quote_positive__closed_helper {Γ A x}
  : forall n n', convertible Γ (subst_n_name (quote_positive A) x n n') (quote_positive A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve convertible__quote_positive__closed_helper : t_quote_db.

  Definition convertible__quote_sort__closed_helper {Γ A x}
  : forall n n', convertible Γ (subst_n_name (quote_sort A) x n n') (quote_sort A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve convertible__quote_sort__closed_helper : t_quote_db.

  Definition convertible__quote_cast_kind__closed_helper {Γ A x}
  : forall n n', convertible Γ (subst_n_name (quote_cast_kind A) x n n') (quote_cast_kind A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve convertible__quote_cast_kind__closed_helper : t_quote_db.

  Definition convertible__quote_name__closed_helper {Γ A x}
  : forall n n', convertible Γ (subst_n_name (quote_name A) x n n') (quote_name A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve convertible__quote_name__closed_helper : t_quote_db.

  Definition convertible__quote_inductive__closed_helper {Γ A x}
  : forall n n', convertible Γ (subst_n_name (quote_inductive A) x n n') (quote_inductive A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve convertible__quote_inductive__closed_helper : t_quote_db.

  Section sub_helpers.
    Context (convertible__quote_term__closed_helper : forall (Γ : Context)
                                                             (A x : Ast.term)
                                                             (n : option nat)
                                                             (n' : Ast.name),
                                                        convertible Γ
                                                                    (subst_n_name
                                                                       (quote_term A) x n n')
                                                                    (quote_term A)).

    Fixpoint convertible__quote_term_helper__closed_helper Γ ls x
    : forall n n', convertible Γ (subst_n_name (quote_term_helper quote_term ls) x n n') (quote_term_helper quote_term ls).
    Proof.
      destruct ls as [|y ys]; simpl; try reflexivity; [].
      intros n n'.
      t_quote.
    Defined.

    Fixpoint convertible__quote_term_helper_def__closed_helper Γ ls x
    : forall n n', convertible Γ (subst_n_name (quote_term_helper_def quote_term ls) x n n') (quote_term_helper_def quote_term ls).
    Proof.
      destruct ls as [|[] ys]; simpl; try reflexivity; [].
      intros n n'.
      t_quote.
    Defined.
  End sub_helpers.

  Fixpoint convertible__quote_term__closed_helper Γ A x {struct A}
  : forall n n', convertible Γ (subst_n_name (quote_term A) x n n') (quote_term A).
  Proof.
    intros n n'; destruct A; simpl;
    repeat match goal with
             | [ Γ : Context, ls : list Ast.term |- _ ]
               => unique pose proof (convertible__quote_term_helper__closed_helper convertible__quote_term__closed_helper Γ ls x n n')
             | [ Γ : Context, ls : Ast.mfixpoint Ast.term |- _ ]
               => unique pose proof (convertible__quote_term_helper_def__closed_helper convertible__quote_term__closed_helper Γ ls x n n')
             | [ Γ : Context, A : Ast.term |- _ ]
               => not constr_eq A x; unique pose proof (convertible__quote_term__closed_helper Γ A x n n')
           end;
    try solve [ t_quote ].
  Defined.

  Definition convertible__quote__closed
  : forall Γ A x,
      convertible Γ ((quote A) [ 0 ↦ x ]) (quote A).
  Proof.
    intros; apply convertible__quote_term__closed_helper.
  Defined.

  Hint Resolve convertible__quote__closed : t_quote_db.

  Definition convertible__quote__app
  : forall Γ A B,
      convertible Γ (⌜ A ‘’ B ⌝) ((‘App’ ‘’ ⌜ A ⌝) ‘’ ⌜ B ⌝).
  Proof.
    intros; simpl.
    unfold tApp, qtApp, tLambda.
    symmetry.
    etransitivity.
    { apply conv_tApp_respectful; [ | reflexivity ].
      apply conv_beta. }
    simpl.
    etransitivity; [ apply conv_beta | ].
    simpl.
    t_quote.
  Defined.

End TR.

Module PRTR <: PretermReflectionTypingRules LC PP PRP TR.
  Export LC PP PRP TR.
  Axiom convertible__qquote__closed
  : forall Γ x,
      convertible Γ (‘quote’ [ 0 ↦ x ]) (‘quote’).

  (*Axiom box_distr_qtProd_quote
  : forall Γ A B,
      convertible Γ (‘□’ ‘’ (A ‘‘→’’ ⌜ B ⌝)) ((‘□’ ‘’ A) ‘‘→’’ (‘□’ ‘’ ⌜ B ⌝)).*)

  Axiom box_qtProd_dom_precompose
  : forall {Γ} A B C,
      (box' Γ (‘□’ ‘’ B) -> box' Γ (‘□’ ‘’ A))
      -> box' Γ (‘□’ ‘’ (A ‘‘→’’ C))
      -> box' Γ (‘□’ ‘’ (B ‘‘→’’ C)).

  (** FIXME: This seems a bit fishy... *)
  Axiom box_quote_app_quote
  : forall Γ T,
      box' Γ (‘□’
               ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ (‘App’ ‘’ ‘quote’ ‘’ ⌜ T ⌝))))
      -> box' Γ (‘□’ ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ ⌜ ⌜ T ⌝ ⌝))).

  Axiom box_quote_app_quote_inv
  : forall Γ T,
      box' Γ (‘□’ ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ ⌜ ⌜ T ⌝ ⌝)))
      -> box' Γ (‘□’
                  ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ (‘App’ ‘’ ‘quote’ ‘’ ⌜ T ⌝)))).
End PRTR.


Module PreL' <: PreL LC PP.
  Export LC PP.

  Definition App {A' B' : Preterm}
  : □ (A' ‘→’ B') -> □ A' -> □ B'.
  Proof.
    intros box_A'_impl'_B' box_A'.
    refine (box_A'_impl'_B'.1 ‘’ box_A'.1; _).
    pose has_type_tApp.
    { exact (box_A'_impl'_B'.2). }
    { exact (box_A'.2). }
  Defined.

  Definition wttLambda_nd
             {Γ : Context} {B' : Preterm}
  : forall A' : Preterm, box' (Γ ▻ A') B' -> box' Γ (A' ‘→’ B').
  Proof.
    refine (fun A' body
            => (Ast.tLambda Ast.nAnon A' body.1;
                _)).
    apply has_type_tLambda.
    exact body.2.
  Defined.

  Definition wttApp_1_nd {Γ : Context} {A' B' : Preterm}
  : box' Γ (A' ‘→’ B') -> box' Γ A' -> box' Γ B'.
  Proof.
    refine (fun F x
            => (Ast.tApp F.1 [x.1];
                _)).
    eapply has_type_tApp.
    { exact F.2. }
    { exact x.2. }
  Defined.

  Notation "x ‘’ y" := (wttApp_1_nd x%wtt y%wtt) : well_typed_term_scope.

  Definition box'_weaken {Γ A} : box' ε A -> box' Γ A.
  Proof.
    refine (fun x => (x.1; _ x.2)).
    apply (has_type_weaken nil).
  Defined.
End PreL'.

Module LA <: PostL_Assumptions LC PP.
  Export TR LC PP PRP.
  Definition Quot : forall T, □ T -> □ (‘□’ ‘’ ⌜ T ⌝).
  Proof.
    intros T box_T'.
    admit'.
    (*eapply box'_respectful.
    { symmetry.
      etransitivity.
      { apply convertible_beta_app_lambda.
    apply
    refine (Ast.tApp ‘existT’ [‘Preterm’; _; quote box_T'.1; _]; _).
    unfold qbox.
    eapply has_type_existT.

    do 4 (apply has_type_beta_1_type with (f := fun x => x); simpl).
  eapply has_type_existT.
  { apply quote_term_has_type. }
  { do 1 (apply has_type_beta_1_type with (f := fun x => x); simpl).
    (** Need to somehow lift (quine?) typing derivation here *)
    exfalso; admit.
    Grab Existential Variables.
    admit. }

    let t := (eval cbv delta [Quot box box'] in @Quot) in
    quote_term t (fun x => exact x).*)
  Defined.


  Axiom qQuote
  : forall T,
      let A := (‘□’ ‘’ T)%preterm in
      □ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝))).

  Axiom qbApp
   : forall A' B',
       □ ((‘□’ ‘’ (A' ‘‘→’’ B')) ‘→’ (‘□’ ‘’ A') ‘→’ (‘□’ ‘’ B')).
End LA.

Declare Module LH : LobHypotheses LC.

Module Lob <: LobsTheorem LC LH.
  Module Lob' := LobOfPreLob LC LH PP PreL' PRP TR PRTR LA.
  Definition lob := Lob'.lob.
  Print Assumptions lob.
End Lob.

Print Assumptions Lob.lob.

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

Module PP <: PretermPrimitives LC.
  Export LC.
  Definition tLambda : Preterm -> Preterm -> Preterm
    := Ast.tLambda Ast.nAnon.
  Definition qtApp : Preterm
    := qtApp.

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

Module PRP <: PretermReflectionPrimitives LC.
  Quote Definition qPreterm := Ast.term.
  Notation "‘Preterm’" := qPreterm : preterm_scope.

  Definition qquote : LC.Preterm.
  Proof.
    let t := (eval cbv beta delta [qO qS qEmptyString qString qnAnon qAscii qnil qcons qmkdef qtInd qtFix qtCase qtUnknown qtRel qtConstruct qtEvar qtMeta qtVar qtApp qtConst qtSort qtCast qtProd inductive_quotable quote_ascii bool_quotable quote_bool (*quote_string quote_positive quote_nat*) ident_quotable quote_ident quote_name nat_quotable name_quotable quote quote_term sort_quotable cast_kind_quotable quote_sort qsSet qsProp qsType universe_quotable quote_inductive qmkInd] in quote_term) in
    quote_term t (fun x => exact x).
  Defined.
  Notation "‘quote’" := qquote : preterm_scope.
End PRP.

Module TR <: TypingRules LC PP.
  Export LC PP.
  Definition capture_avoiding_subst_0 : forall (in_term : Preterm)
                                               (new_value : Preterm),
                                          Preterm
    := fun in_term new_value
       => subst_n_name in_term new_value (Some 0%nat) Ast.nAnon.
  Notation "x [ 0 ↦ y ]" := (capture_avoiding_subst_0 x y).
  Definition convertible : Context -> Preterm -> Preterm -> Prop
    := convertible.
  Definition box'_respectful : forall {Γ A B},
                                 convertible Γ A B
                                 -> box' Γ A
                                 -> box' Γ B.
  Proof.
    intros Γ A B H [a Ha].
    exists a.
    eapply has_type_conv_subst; try eassumption.

  Axiom convertible_refl : forall {Γ}, Reflexive (convertible Γ).
  Axiom convertible_sym : forall {Γ}, Symmetric (convertible Γ).
  Axiom convertible_trans : forall {Γ}, Transitive (convertible Γ).
  Axiom convertible_tApp : forall {Γ A A' B B'},
                             convertible Γ A A'
                             -> convertible Γ B B'
                             -> convertible Γ (tApp A B) (tApp A' B').
  Axiom convertible_beta_app_lambda
  : forall Γ A f a,
      convertible Γ (tApp (tLambda A f) a) (capture_avoiding_subst_0 f a).
  Axiom convertible__capture_avoiding_subst_0__tApp
  : forall Γ A B x,
      convertible Γ ((A ‘’ B) [ 0 ↦ x ]) ((A [ 0 ↦ x ]) ‘’ (B [ 0 ↦ x ])).
  Axiom convertible__capture_avoiding_subst_0__qtProd
  : forall Γ A B x,
      convertible Γ ((A ‘‘→’’ B) [ 0 ↦ x ]) ((A [ 0 ↦ x ]) ‘‘→’’ (B [ 0 ↦ x ])).
  Axiom convertible__capture_avoiding_subst_0__tVar0
  : forall Γ x,
      convertible Γ (‘VAR₀’ [ 0 ↦ x ]) x.

  Axiom qtProd_Proper_convertible
  : forall Γ,
      Proper (convertible Γ ==> convertible Γ ==> convertible Γ) qtProd.
  Existing Instance qtProd_Proper_convertible.
  Axiom tApp_Proper_convertible
  : forall Γ,
      Proper (convertible Γ ==> convertible Γ ==> convertible Γ) tApp.
  Existing Instance tApp_Proper_convertible.
  Axiom convertible__quote__qtProd
  : forall Γ A B,
      convertible Γ (⌜ A ‘→’ B ⌝) (⌜ A ⌝ ‘‘→’’ ⌜ B ⌝).
  Axiom convertible__quote__closed
  : forall Γ A x,
      convertible Γ ((quote A) [ 0 ↦ x ]) (quote A).
  Axiom convertible__qtApp__closed
  : forall Γ x,
      convertible Γ (‘App’ [ 0 ↦ x ]) (‘App’).
  Axiom convertible__quote__app
  : forall Γ A B,
      convertible Γ (⌜ A ‘’ B ⌝) ((‘App’ ‘’ ⌜ A ⌝) ‘’ ⌜ B ⌝).
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

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
Require Export Lob.conversion_quote.

Axiom proof_admitted : False.
Ltac admit' := case proof_admitted.

Notation "( x ; y )" := (existT _ x y).
Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Notation "x .2" := (projT2 x) (at level 3, format "x '.2'").

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

Module Type Contexts.
  Axiom qbox : Ast.term.

  Definition is_closed (x : Ast.term) : Type
    := forall k n, subst_n_name x k n Ast.nAnon = x.

  Existing Class is_closed.

  Axiom box_is_closed : is_closed qbox.

  Axiom qquote : Ast.term.

  Axiom qquote_is_closed : is_closed qquote.

End Contexts.

Module WithContext (Ctx : Contexts).

  Module LC <: LobExtendedContext.
    Definition Preterm := Ast.term.
    Definition Context : Type := Context.

    Delimit Scope context_scope with ctx.
    Bind Scope context_scope with Context.

    Definition empty_context : Context := DefaultContext.
    Notation ε := empty_context.

    Definition context_extend : Context -> Preterm -> Context
      := fun Γ T => context_extend Γ (CBinder Ast.nAnon T).
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


    Definition qbox : Preterm := Ctx.qbox.
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

    Definition is_closed (x : Preterm) : Type
      := forall k n, subst_n_name x k n Ast.nAnon = x.

    Existing Class is_closed.

    Global Instance box_is_closed : is_closed ‘□’
      := Ctx.box_is_closed.

    Global Instance tApp_is_closed : forall A' B', is_closed A' -> is_closed B' -> is_closed (A' ‘’ B').
    Proof.
      intros A' B' H0 H1 k n.
      specialize (H0 k).
      specialize (H1 k).
      simpl; rewrite H0, H1; reflexivity.
    Qed.

    Global Instance tProd_is_closed : forall A' B', is_closed A' -> is_closed B' -> is_closed (A' ‘→’ B').
    Proof.
      intros A' B' H0 H1 k n.
      specialize (H0 k).
      specialize (H1 k).
      simpl.
      rewrite H0, H1; reflexivity.
    Qed.

    Global Instance quote_is_closed : forall A', is_closed (quote A').
    Proof.
      repeat intro; apply eq__quote_term__closed_helper.
    Qed.
  End LC.

  Module PRP <: PretermReflectionPrimitives LC.
    Definition qPreterm := term'.
    Notation "‘Preterm’" := qPreterm : preterm_scope.

    Global Instance has_type__quote {Γ A} : has_type _ (quote A) qPreterm
      := has_type__quote_term _ Γ.
    Definition wttquote {Γ} A : LC.box' _ _
      := (quote A; @has_type__quote Γ _).
    Notation "‘⌜ A ⌝’" := (wttquote A) : well_typed_term_scope.

    Definition qquote : LC.Preterm
      := Ctx.qquote.
    (*Proof.
      let t := (eval cbv beta delta [qO qS qEmptyString qString qnAnon qAscii qnil qcons qmkdef qtInd qtFix qtCase qtUnknown qtRel qtConstruct qtEvar qtMeta qtVar qtApp qtConst qtSort qtCast qtProd inductive_quotable quote_ascii bool_quotable quote_bool (*quote_string quote_positive quote_nat*) ident_quotable quote_ident quote_name nat_quotable name_quotable quote quote_term sort_quotable cast_kind_quotable quote_sort qsSet qsProp qsType universe_quotable quote_inductive qmkInd] in quote_term) in
      quote_term t (fun x => exact x).
    Defined.*)
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

  Module TR <: TypingRules LC PP.
    Export LC PP.
    Definition capture_avoiding_subst_0 : forall (in_term : Preterm)
                                                 (new_value : Preterm),
                                            Preterm
      := fun in_term new_value
         => subst_n_name in_term new_value (Some 0%nat) Ast.nAnon.
    Notation "x [ 0 ↦ y ]" := (capture_avoiding_subst_0 x y).
    Global Arguments capture_avoiding_subst_0 !_ / _.
    Definition convertible : Context -> Preterm -> Preterm -> Type
      := convertible.

    Definition eq__subst__quote
    : forall A x, capture_avoiding_subst_0 (quote A) x = quote A.
    Proof.
      intros; unfold quote, capture_avoiding_subst_0.
      rewrite eq__quote_term__closed_helper; reflexivity.
    Defined.

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
    Global Instance tProd_Proper_convertible
    : forall Γ,
        Proper (convertible Γ ==> eq ==> convertible Γ) tProd.
    Proof.
      repeat intro.
      apply conv_tProd_respectful; [ assumption | subst; reflexivity ].
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

    Definition convertible__quote__closed
    : forall Γ A x,
        convertible Γ ((quote A) [ 0 ↦ x ]) (quote A).
    Proof.
      intros; rewrite eq__subst__quote.
      reflexivity.
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
      unfold capture_avoiding_subst_0.
      rewrite eq__quote_term__closed_helper; reflexivity.
    Defined.

  End TR.

  Module PreL' <: PreL LC PP.
    Export LC PP.

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

    Definition wttApp_1 {Γ : Context} {A' B' : Preterm}
    : box' Γ (A' ‘→’ B')
      -> forall x : box' Γ A',
           box' Γ (subst_n_name B' x.1 (Some 0%nat) Ast.nAnon).
    Proof.
      refine (fun F x
              => (Ast.tApp F.1 [x.1];
                  _)).
      eapply has_type_tApp.
      { exact F.2. }
      { exact x.2. }
    Defined.

    Definition wttApp_1_nd {Γ : Context} {A' B' : Preterm} {H : is_closed B'}
    : box' Γ (A' ‘→’ B') -> box' Γ A' -> box' Γ B'.
    Proof.
      intros F x.
      pose proof (wttApp_1 F x) as H'.
      exists H'.1.
      destruct H' as [Fx H']; simpl.
      hnf in H.
      rewrite H in H'.
      apply H'.
    Defined.

    Notation "x ‘’ y" := (wttApp_1_nd x%wtt y%wtt) : well_typed_term_scope.
  End PreL'.

  Module Type DoublyQuotedThings.
    Export TR LC PP PRP.
    Axiom qbox_Ui : Ast.sort.
    Axiom has_type_qbox
    : has_type ε ‘□’ (term' ‘→’ Ast.tSort qbox_Ui).
    Global Existing Instance has_type_qbox.

    Axiom box_qtProd_dom_precompose
    : forall {Γ} A B C,
        (box' Γ (‘□’ ‘’ B) -> box' Γ (‘□’ ‘’ A))
        -> box' Γ (‘□’ ‘’ (A ‘‘→’’ C))
        -> box' Γ (‘□’ ‘’ (B ‘‘→’’ C)).

    (** FIXME: This seems a bit fishy... *)
    Axiom box_quote_app_quote
    : forall Γ T,
        box' Γ (‘□’
                 ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ⌜ T ⌝))))
        -> box' Γ (‘□’ ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ ⌜ ⌜ T ⌝ ⌝))).

    Axiom box_quote_app_quote_inv
    : forall Γ T,
        box' Γ (‘□’ ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ ⌜ ⌜ T ⌝ ⌝)))
        -> box' Γ (‘□’
                    ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ⌜ T ⌝)))).

    Axiom Quot : forall T, □ T -> □ (‘□’ ‘’ ⌜ T ⌝).

    Section context.
      Context (qX qL0 : Preterm).
      Let Γ := (ε ▻ (‘□’
                      ‘’ (tLambda ‘Preterm’
                                  (‘App’ ‘’ ⌜ ‘□’ ⌝
                                    ‘’ (‘App’ ‘’ ‘VAR₀’ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ‘VAR₀’))
                                    ‘‘→’’ ⌜ qX ⌝) ‘’ ⌜ qL0 ⌝))).

      Axiom qQuote
      : forall T,
          let A := (‘□’ ‘’ T)%preterm in
          box' Γ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝))).

      Axiom qbApp
      : forall A' B',
          box' Γ ((‘□’ ‘’ (A' ‘‘→’’ B')) ‘→’ (‘□’ ‘’ A') ‘→’ (‘□’ ‘’ B')).
    End context.
  End DoublyQuotedThings.

  Module PRTR (DQT : DoublyQuotedThings) <: PretermReflectionTypingRules LC PP PRP TR.
    Export LC PP PRP TR.
    Include DQT.
    Definition convertible__qquote__closed
    : forall Γ x,
        convertible Γ (‘quote’ [ 0 ↦ x ]) (‘quote’).
    Proof.
      unfold capture_avoiding_subst_0; intros.
      rewrite Ctx.qquote_is_closed; reflexivity.
    Defined.
  End PRTR.

  Local Ltac t_has_type' :=
    idtac;
    match goal with
      | _ => progress simpl in *
      | _ => exact _
      | [ |- has_type _ (Ast.tLambda (Ast.nNamed _) _ _) _ ]
        => apply has_type_tLambda_unname
      | [ |- has_type ?Γ (Ast.tApp ?f [?a]) ?B ]
        => refine (@has_type_tApp Γ f Ast.nAnon _ _ a _ _); shelve_unifiable
      | [ |- has_type ?Γ (Ast.tLambda ?x ?A ?b) ?B ]
        => refine (has_type_tLambda _ _ _ _ _ _); shelve_unifiable
      | [ |- has_type ?Γ (Ast.tProd ?x ?A ?B) ?T ]
        => refine (has_type_tProd _ _ _ _ _ _); shelve_unifiable
      | [ |- has_type _ (quote_term _) (subst_n_name ?e _ _ _) ]
        => unify e term'
      | [ |- has_type _ (Ast.tApp (Ast.tLambda _ _ _) [_]) _ ]
        => eapply has_type_conv_subst_term;
          [
          | symmetry; solve [ apply conv_beta ] ];
          simpl subst_n_name
      | _ => rewrite !eq__quote_term__closed_helper
      | [ |- has_type ?Γ (Ast.tApp ?f [?a]) ?B ]
        => let A := fresh in
           let B' := fresh in
           evar (A : Ast.term);
             evar (B' : Ast.term);
             let H := fresh in
             pose proof (@has_type_tApp Γ f Ast.nAnon A B' a) as H;
               subst A B';
               refine (_ (H _ _)); shelve_unifiable; clear H;
               [ | repeat t_has_type' | ]; shelve_unifiable;
               [ simpl; exact (fun x => x) | ]
      | _ => exact _
      | [ |- has_type ?Γ (Ast.tApp ?f [?a]) ?B ]
        => not is_evar B; eapply has_type_conv_subst; shelve_unifiable
      | [ |- has_type (_ ▻▻ _) _ _ ]
        => apply wkg_rel_free; [ intros ? [?|]; reflexivity | intros ? [?|]; reflexivity | ]
      | [ |- has_type _ _ _ ]
        => eapply has_type_conv_subst;
          [ eapply has_type_tConstruct1_Lookup;
            [ | | simpl; reflexivity ];
            hnf; simpl; reflexivity
          | ]
      | [ |- convertible ?Γ ?k _ ] => unfold k
      | [ |- convertible ?Γ (Ast.tConst ?n) _ ]
        => let H := fresh in
           pose proof (@conv_delta_Lookup Γ n) as H;
             unfold is_rel_free in H;
             simpl in H;
             apply (H (fun _ _ => eq_refl))
      | [ |- conversion.convertible _ (Ast.tProd _ _ _) (Ast.tProd _ _ _) ]
        => apply conv_tProd_respectful
      | _ => progress simpl
      | [ |- has_type _ (Ast.tApp _ (_::_::_)%list) _ ]
        => apply has_type_tApp_split
      | [ |- conversion.convertible _ (Ast.tProd _ _ _) (Ast.tProd _ _ _) ]
        => apply conv_tProd_respectful
      | [ |- conversion.convertible _ ?x (subst_n_name ?e _ _ _) ]
        => is_evar e; not has_evar x; unify x e; simpl; reflexivity
      | [ |- conversion.convertible _ (subst_n_name ?e _ _ _) ?x ]
        => is_evar e; not has_evar x; unify x e; simpl; reflexivity
      | [ |- conversion.convertible _ ?x ?y ]
        => not has_evar x; not has_evar y; reflexivity
      | [ |- conversion.convertible _ ?x ?y ]
        => not has_evar x; is_evar y; reflexivity
      | [ |- conversion.convertible _ ?x (subst_n_name ?e _ _ _) ]
        => is_evar e; unify x e; simpl; reflexivity
      | [ |- conversion.convertible _ (subst_n_name ?e _ _ _) ?x ]
        => is_evar e; unify x e; simpl; reflexivity
      | _ => progress unfold LC.tProd
      | [ |- conversion.convertible _ (Ast.tSort match ?e with _ => _ end) (Ast.tSort ?v) ]
        => is_evar e; unify e v; reflexivity
    end.



  Module LA (DQT : DoublyQuotedThings) <: PostL_Assumptions LC PP PRP TR.
    Export TR LC PP PRP.
    Include DQT.

    Section context.
      Context (qX qL0 : Preterm).
      Let Γ := (ε ▻ (‘□’
                      ‘’ (tLambda ‘Preterm’
                                  (‘App’ ‘’ ⌜ ‘□’ ⌝
                                    ‘’ (‘App’ ‘’ ‘VAR₀’ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ‘VAR₀’))
                                    ‘‘→’’ ⌜ qX ⌝) ‘’ ⌜ qL0 ⌝))).

      Definition box'_weaken
      : forall {A} {H : is_closed A}, box' ε A -> box' Γ A.
      Proof.
        simpl; intros A H bA.
        refine (bump_rel_from bA.1 (Some 0%nat) Ast.nAnon tt; _).
        apply is_rel_free_iff in H.
        hnf in H.
        rewrite <- (H (Some 0%nat)).
        subst Γ.
        eapply (wkg_1 (Δ := nil)); [ | exact bA.2 ].
        unfold qtProd, qtApp, tApp, tLambda.
        Time do 3 t_has_type'.
        { match goal with
      | [ |- has_type ?Γ (Ast.tApp ?f [?a]) ?B ]
        => let A := fresh in
           let B' := fresh in
           evar (A : Ast.term);
             evar (B' : Ast.term);
             let H := fresh in
             pose proof (@has_type_tApp Γ f Ast.nAnon A B' a) as H;
               subst A B';
               refine (_ (H _ _)); shelve_unifiable; clear H;
               [ |  | ]; shelve_unifiable;
               [ simpl | | ]
end.
Focus 2.
{
        { match goal with
      | [ |- has_type ?Γ (Ast.tApp ?f [?a]) ?B ]
        => let A := fresh in
           let B' := fresh in
           evar (A : Ast.term);
             evar (B' : Ast.term);
             let H := fresh in
             pose proof (@has_type_tApp Γ f Ast.nAnon A B' a) as H;
               subst A B';
               refine (_ (H _ _)); shelve_unifiable; clear H;
               [ |  | ]; shelve_unifiable;
               [ simpl | | ]
end.
Focus 2.
{ repeat t_has_type'. }
Unfocus.
{ Time do 5 t_has_type'. }
{ Time do 2 t_has_type'.
{ t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.
t_has_type'.

Existing Class eq.
Hint Extern 1 (Some (CType ?x _) = Some (CType ?x _)) => reflexivity : typeclass_instances.

eapply has_type_tConstruct1_Lookup; simpl.

3:exact _.
simpl.
all:simpl; try exact _.
all:simpl; try exact _.
(*t_has_type'.
t_has_type'.
Global Existing Instance has_type__quote_term_1
refine (@has_type__quote_term _ [(_, _)]%list).

rewrite eq__quote_term__closed_helper.

        {



          all:admit. }
        {

admit'.
        (* refine ((fun Ui H => @wkg_1_nil nil Ast.nAnon _ _ _ Ui H bA.2) _ _); shelve_unifiable.
        unfold qtProd, qtApp, tApp, tLambda.
        t_has_type.*)*)
      Admitted.
    End context.

    Definition App : forall {A' B'} {H : is_closed B'},
                       □ (A' ‘→’ B') -> □ A' -> □ B'.
    Proof.
      intros A' B' H AtoB A.
      refine (AtoB.1 ‘’ A.1;
              _ (has_type_tApp ε AtoB.1 Ast.nAnon A' B' A.1 AtoB.2 A.2)).
      clear -H; abstract (hnf in H; rewrite H; intro; assumption).
    Defined.
  End LA.

  Module Lob (LH : LobHypotheses LC) (DQT : DoublyQuotedThings) <: LobsTheorem LC LH.
    Module PRTR' := PRTR DQT.
    Module LA' := LA DQT.
    Module Lob' := LobOfPreLob LC LH PP PreL' PRP TR PRTR' LA'.
    Definition lob := Lob'.lob.
    Print Assumptions lob.
  End Lob.
End WithContext.
(*
  Module DQT <: DoublyQuotedThings.
    Export TR LC PP PRP PreL'.
    Definition qbox_Ui' : Ast.universe := 1.
    Definition qbox_Ui := Ast.sType qbox_Ui'.

    (*Global Instance has_type_qPreterm {Γ}
    : has_type Γ ‘Preterm’ (Ast.tSort (Ast.sType 1))
      := _.

    Definition wttPreterm {Γ} : box' Γ (Ast.tSort (Ast.sType 1))
      := (‘Preterm’; has_type_qPreterm).
    Notation "‘‘Preterm’’" := wttPreterm : well_typed_term_scope.*)

    Global Instance has_type_qbox
    : has_type ε ‘□’ (term' ‘→’ Ast.tSort qbox_Ui).
    Proof.
      unfold qbox, qbox_Ui.
      repeat t_has_type; shelve_unifiable.
      admit'.
    Qed.

    Axiom box_qtProd_dom_precompose
    : forall {Γ} A B C,
        (box' Γ (‘□’ ‘’ B) -> box' Γ (‘□’ ‘’ A))
        -> box' Γ (‘□’ ‘’ (A ‘‘→’’ C))
        -> box' Γ (‘□’ ‘’ (B ‘‘→’’ C)).

    (** FIXME: This seems a bit fishy... *)
    Axiom box_quote_app_quote
    : forall Γ T,
        box' Γ (‘□’
                 ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ⌜ T ⌝))))
        -> box' Γ (‘□’ ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ ⌜ ⌜ T ⌝ ⌝))).

    Axiom box_quote_app_quote_inv
    : forall Γ T,
        box' Γ (‘□’ ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ ⌜ ⌜ T ⌝ ⌝)))
        -> box' Γ (‘□’
                    ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ⌜ T ⌝)))).

    Quote Definition has_type' := has_type nil.
    Axiom has_type_has_type' : forall {Γ}, has_type Γ has_type' (‘Preterm’ ‘→’ ‘Preterm’ ‘→’ Ast.tSort (Ast.sType 3)).
    Existing Instance has_type_has_type'.
    Definition wtthas_type {Γ} : box' Γ _
      := (has_type'; has_type_has_type').
    Notation "‘‘has_type’’" := wtthas_type : well_typed_term_scope.

    (*Definition wttexistT {Γ U1 U2} : box' Γ _
      := (‘existT’; has_type_qexistT _ U1 U2).
    Notation "‘‘existT’’" := wttexistT : well_typed_term_scope.*)

    Local Ltac set_evars :=
      repeat match goal with
               | [ |- appcontext[?E] ] => is_evar E; let e := fresh in set (e := E)
             end.

    Local Ltac subst_body :=
      repeat match goal with
               | [ H := _ |- _ ] => subst H
             end.

    Local Ltac conv_rewrite
      := set_evars;
        repeat match goal with
                 | [ |- convertible _ ?x ?x ] => reflexivity
                 | [ |- convertible _ (?x ‘’ _) (?x ‘’ _) ]
                   => apply tApp_Proper_convertible; [ reflexivity | ]
                 | [ |- convertible _ (_ ‘‘→’’ _) (_ ‘‘→’’ _) ]
                   => apply qtProd_Proper_convertible
                 | [ |- convertible _ (_ ‘→’ ?x) _ ]
                   => apply tProd_Proper_convertible; [ | reflexivity ]
                 | _ => progress rewrite_strat repeat (topdown repeat (hints convdb))
               (*| _ => progress rewrite ?convertible__capture_avoiding_subst_0__tApp, ?convertible__qtApp__closed, ?convertible__quote__closed, ?convertible__quote__app, ?convertible__capture_avoiding_subst_0__tVar0, ?convertible__qquote__closed, ?convertible__capture_avoiding_subst_0__qtProd, ?convertible__quote__qtProd, ?convertible_beta_app_lambda*)
               end;
        subst_body.

    Local Notation "x ‘’ y" := (wttApp_1 x%wtt y%wtt) : well_typed_term_scope.

    Definition Quot : forall T, □ T -> □ (‘□’ ‘’ ⌜ T ⌝).
    Proof.
      intros T bT.
      unfold qbox.
      eapply box'_respectful; cycle 1.
      2:unfold tApp.
      2:let RHS := match goal with |- ?R ?x ?y => constr:y end in
        match RHS with
          | context G[Ast.tApp (Ast.tLambda ?x ?A ?b) [?a]]
            => let G' := context G[subst_n_name b a (Some 0%nat) x] in
               refine (@transitivity _ _ _ _ G' _ _ _); simpl
        end;
          repeat match goal with
                   | [ |- ?R (Ast.tApp _ _) (Ast.tApp _ _) ]
                     => apply tApp_Proper
                   | [ |- ?R _ (Ast.tApp (Ast.tLambda _ _ _) _) ]
                     => etransitivity; [ | symmetry; apply conv_beta ]
                   | [ |- ?R (Ast.tLambda ?n ?A _) (Ast.tLambda ?n ?A _) ]
                     => apply tLambda_Proper1
                   | [ |- ?R ?x ?x ] => reflexivity
                   | [ |- (_ * _)%type ] => split
                   | [ |- True ] => constructor
                   | _ => progress simpl
                 end.
      Timeout 5 refine (‘‘existT’’ ‘’ ‘‘Preterm’’ ‘’ (wttLambda_nd _ (‘‘has_type’’ ‘’ ‘‘VAR₀’’ ‘’ ‘⌜ T ⌝’)) ‘’ ‘⌜ bT.1 ⌝’ ‘’ (_ bT.2))%wtt; shelve_unifiable.
      2:repeat match goal with
                 | [ |- ?R (Ast.tApp _ [_]) (Ast.tApp _ [_]) ]
                   => apply tApp_Proper
                 | [ |- ?R (Ast.tApp _ nil) (Ast.tApp _ nil) ]
                   => apply tApp_Proper
                 | [ |- ?R (Ast.tApp _ [_;_]) (Ast.tApp _ [_;_]) ]
                   => apply tApp_Proper
                 | [ |- ?R (Ast.tApp _ [_;_;_]) (Ast.tApp _ [_;_;_]) ]
                   => apply tApp_Proper
                 | [ |- ?R _ (Ast.tApp (Ast.tLambda _ _ _) _) ]
                   => etransitivity; [ | symmetry; apply conv_beta ]
                 | [ |- ?R (Ast.tApp (Ast.tApp _ _) _) _ ]
                   => apply conv_tApp_cons2
                 | [ |- ?R _ (Ast.tApp (Ast.tApp _ _) _) ]
                   => symmetry; apply conv_tApp_cons2; symmetry
                 | [ |- ?R (Ast.tLambda ?n ?A _) (Ast.tLambda ?n ?A _) ]
                   => apply tLambda_Proper1
                 | [ |- ?R _ (Ast.tLambda (Ast.nNamed _) _ _) ]
                   => etransitivity; [ | symmetry; apply conv_tLambda_unname ]
                 | [ |- ?R ?x ?x ] => reflexivity
                 | [ |- (_ * _)%type ] => split
                 | [ |- True ] => constructor
                 | _ => progress simpl
                 | _ => progress unfold quote_term.quote, term_quotable
                 | _ => rewrite eq__quote_term__closed_helper
               end.
      { simpl.
        intro ht.
        eapply box'_respectful.
        { let RHS := match goal with |- ?R ?x ?y => constr:y end in
          match RHS with
            | context G[Ast.tApp (Ast.tLambda ?x ?A ?b) [?a]]
              => let G' := context G[subst_n_name b a (Some 0%nat) x] in
                 refine (@transitivity _ _ _ _ G' _ _ _); simpl
          end;
            repeat match goal with
                     | [ |- ?R _ (Ast.tApp (Ast.tLambda _ _ _) _) ]
                       => etransitivity; [ | symmetry; apply conv_beta ]
                     | [ |- ?R (Ast.tApp (Ast.tLambda _ _ _) _) _ ]
                       => etransitivity; [ apply conv_beta | ]
                     | [ |- ?R (Ast.tLambda ?n ?A _) (Ast.tLambda ?n ?A _) ]
                       => apply tLambda_Proper1
                     | [ |- ?R (Ast.tApp _ [_]) (Ast.tApp _ [_]) ]
                       => apply tApp_Proper
                     | [ |- ?R (Ast.tApp _ nil) (Ast.tApp _ nil) ]
                       => apply tApp_Proper
                     | [ |- ?R (Ast.tApp _ [_;_]) (Ast.tApp _ [_;_]) ]
                       => apply tApp_Proper
                     | [ |- ?R (Ast.tApp _ [_;_;_]) (Ast.tApp _ [_;_;_]) ]
                       => apply tApp_Proper
                     | [ |- ?R (Ast.tApp (Ast.tApp _ _) _) _ ]
                       => apply conv_tApp_cons2
                     | [ |- ?R _ (Ast.tApp (Ast.tApp _ _) _) ]
                       => symmetry; apply conv_tApp_cons2; symmetry
                     | [ |- ?R ?x ?x ] => reflexivity
                     | [ |- (_ * _)%type ] => split
                     | [ |- True ] => constructor
                     | _ => progress simpl
                     | _ => progress unfold quote_term.quote, term_quotable
                     | _ => rewrite eq__quote_term__closed_helper
                   end;
            reflexivity. }
        admit.
    Admitted.


    Section context.
      Context (qX qL0 : Preterm).
      Let Γ := (ε ▻ (‘□’
                      ‘’ (tLambda ‘Preterm’
                                  (‘App’ ‘’ ⌜ ‘□’ ⌝
                                    ‘’ (‘App’ ‘’ ‘VAR₀’ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ‘VAR₀’))
                                    ‘‘→’’ ⌜ qX ⌝) ‘’ ⌜ qL0 ⌝))).

      Axiom qQuote
      : forall T,
          let A := (‘□’ ‘’ T)%preterm in
          box' Γ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝))).

      Axiom qbApp
      : forall A' B',
          box' Γ ((‘□’ ‘’ (A' ‘‘→’’ B')) ‘→’ (‘□’ ‘’ A') ‘→’ (‘□’ ‘’ B')).
    End context.
  End DQT.

  Declare Module LH : LobHypotheses LC.

  Module Lob <: LobsTheorem LC LH.
    Module PRTR' := PRTR DQT.
    Module LA' := LA DQT.
    Module Lob' := LobOfPreLob LC LH PP PreL' PRP TR PRTR' LA'.
    Definition lob := Lob'.lob.
    Print Assumptions lob.
  End Lob.

  Print Assumptions Lob.lob.
*)

Require Import Coq.Setoids.Setoid Coq.Classes.CMorphisms.
Require Export Lob.Notations.

Require Import Template.Template.

Require Import Coq.Strings.String.
Require Import Coq.Program.Program.
Require Import Coq.PArith.BinPos.
Local Open Scope string_scope.
Local Open Scope positive_scope.

Require Export Lob.quote_term.
(*Require Export Lob.quote_has_type.*)
Require Export Lob.conversion.

Notation "( x ; y )" := (existT _ x y).
Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Notation "x .2" := (projT2 x) (at level 3, format "x '.2'").

Axiom proof_admitted : False.
Ltac admit' := case proof_admitted.

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


Section quote_subst_eq.
  Create HintDb t_quote_db discriminated.

  Local Ltac t_quote0 tac :=
    repeat match goal with
             | _ => progress simpl
             | _ => progress intros
             | _ => reflexivity
             | [ |- Ast.tApp _ _ = Ast.tApp _ _ ] => apply f_equal2; [ solve [ tac ] | ]
             | [ |- Ast.tApp _ _ = Ast.tApp _ _ ] => apply f_equal2; [ | solve [ tac ] ]
             | [ |- cons _ _ = cons _ _ ] => apply f_equal2
             (*| _ => apply tApp_Proper_convertible; [ solve [ tac ] | ]
             | _ => apply tApp_Proper_convertible; [ | solve [ tac ] ]
             | [ |- convertible _ (Ast.tApp _ (_::_::_)%list) _ ] => apply conv_tApp_cons1
             | [ |- convertible _ _ (Ast.tApp _ (_::_::_)%list) ] => symmetry; apply conv_tApp_cons1; symmetry*)
             | _ => progress change conversion.convertible with convertible
           end.
  Local Ltac t_quote :=
    repeat match goal with
             | _ => progress t_quote0 t_quote
             | _ => solve [ eauto with nocore t_quote_db ]
           end.

  Definition eq__quote_nat__closed_helper {A x}
  : forall n n', eq (subst_n_name (quote_nat A) x n n') (quote_nat A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve eq__quote_nat__closed_helper : t_quote_db.

  Definition eq__quote_bool__closed_helper {A x}
  : forall n n', eq (subst_n_name (quote_bool A) x n n') (quote_bool A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve eq__quote_bool__closed_helper : t_quote_db.

  Definition eq__quote_ascii__closed_helper {A x}
  : forall n n', eq (subst_n_name (quote_ascii A) x n n') (quote_ascii A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve eq__quote_ascii__closed_helper : t_quote_db.

  Definition eq__quote_ident__closed_helper {A x}
  : forall n n', eq (subst_n_name (quote_ident A) x n n') (quote_ident A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve eq__quote_ident__closed_helper : t_quote_db.

  Definition eq__quote_positive__closed_helper {A x}
  : forall n n', eq (subst_n_name (quote_positive A) x n n') (quote_positive A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve eq__quote_positive__closed_helper : t_quote_db.

  Definition eq__quote_sort__closed_helper {A x}
  : forall n n', eq (subst_n_name (quote_sort A) x n n') (quote_sort A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve eq__quote_sort__closed_helper : t_quote_db.

  Definition eq__quote_cast_kind__closed_helper {A x}
  : forall n n', eq (subst_n_name (quote_cast_kind A) x n n') (quote_cast_kind A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve eq__quote_cast_kind__closed_helper : t_quote_db.

  Definition eq__quote_name__closed_helper {A x}
  : forall n n', eq (subst_n_name (quote_name A) x n n') (quote_name A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve eq__quote_name__closed_helper : t_quote_db.

  Definition eq__quote_inductive__closed_helper {A x}
  : forall n n', eq (subst_n_name (quote_inductive A) x n n') (quote_inductive A).
  Proof. induction A; t_quote. Qed.

  Hint Resolve eq__quote_inductive__closed_helper : t_quote_db.

  Section sub_helpers.
    Context (eq__quote_term__closed_helper : forall (A x : Ast.term)
                                                    (n : option nat)
                                                    (n' : Ast.name),
                                               eq
                                                 (subst_n_name
                                                    (quote_term A) x n n')
                                                 (quote_term A)).

    Fixpoint eq__quote_term_helper__closed_helper ls x
    : forall n n', eq (subst_n_name (quote_term_helper quote_term ls) x n n') (quote_term_helper quote_term ls).
    Proof.
      destruct ls as [|y ys]; simpl; try reflexivity; [].
      intros n n'.
      t_quote.
    Defined.

    Fixpoint eq__quote_term_helper_def__closed_helper ls x
    : forall n n', eq (subst_n_name (quote_term_helper_def quote_term ls) x n n') (quote_term_helper_def quote_term ls).
    Proof.
      destruct ls as [|[] ys]; simpl; try reflexivity; [].
      intros n n'.
      t_quote.
    Defined.
  End sub_helpers.

  Fixpoint eq__quote_term__closed_helper A x {struct A}
  : forall n n', eq (subst_n_name (quote_term A) x n n') (quote_term A).
  Proof.
    intros n n'; destruct A; simpl;
    repeat match goal with
             | [ ls : list Ast.term |- _ ]
               => unique pose proof (eq__quote_term_helper__closed_helper eq__quote_term__closed_helper ls x n n')
             | [ ls : Ast.mfixpoint Ast.term |- _ ]
               => unique pose proof (eq__quote_term_helper_def__closed_helper eq__quote_term__closed_helper ls x n n')
             | [ A : Ast.term |- _ ]
               => not constr_eq A x; unique pose proof (eq__quote_term__closed_helper A x n n')
           end;
    try solve [ t_quote ].
  Defined.
End quote_subst_eq.

Section quote_has_type.
  Local Ltac t_quote0 tac :=
    repeat match goal with
             | _ => progress simpl
             | _ => progress intros
             | _ => reflexivity
             | [ |- has_type ?Γ (Ast.tApp ?f [?a]) ?B ]
               => eapply (fun A => @has_type_tApp Γ f Ast.nAnon A B a)
             | [ |- has_type ?Γ (Ast.tApp ?f [?a]) ?B ]
               => refine (@has_type_tApp Γ f Ast.nAnon _ _ a _ _); shelve_unifiable
             | [ |- has_type ?Γ (Ast.tApp _ (_::_::_)%list) _ ]
               => apply has_type_tApp_split
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
             | _ => exact _
           end.
  Local Ltac t_quote :=
    repeat match goal with
             | _ => progress t_quote0 t_quote
             | _ => solve [ eauto with nocore ]
           end.

  Global Instance has_type__quote__nil A T (H : forall Γ, has_type (DefaultContext ▻▻ Γ) A T)
  : has_type DefaultContext A T
    := H nil.

  Global Instance has_type__quote_nat A
  : forall Γ, has_type (DefaultContext ▻▻ Γ) (quote_nat A) nat'.
  Proof. induction A; t_quote. Qed.

  Global Instance has_type__quote_bool A
  : forall Γ, has_type (DefaultContext ▻▻ Γ) (quote_bool A) bool'.
  Proof. induction A; t_quote. Qed.

  Global Instance has_type__quote_ascii A
  : forall Γ, has_type (DefaultContext ▻▻ Γ) (quote_ascii A) ascii'.
  Proof. induction A; t_quote. Qed.

  Global Instance has_type__quote_ident A
  : forall Γ, has_type (DefaultContext ▻▻ Γ) (quote_ident A) ident'.
  Proof. induction A; t_quote. Qed.

  Global Instance has_type__quote_positive A
  : forall Γ, has_type (DefaultContext ▻▻ Γ) (quote_positive A) positive'.
  Proof. induction A; t_quote. Qed.

  Global Instance has_type__quote_sort A
  : forall Γ, has_type (DefaultContext ▻▻ Γ) (quote_sort A) sort'.
  Proof. induction A; t_quote. Qed.

  Global Instance has_type__quote_cast_kind A
  : forall Γ, has_type (DefaultContext ▻▻ Γ) (quote_cast_kind A) cast_kind'.
  Proof. induction A; t_quote. Qed.

  Global Instance has_type__quote_name A
  : forall Γ, has_type (DefaultContext ▻▻ Γ) (quote_name A) name'.
  Proof. induction A; t_quote. Qed.

  Global Instance has_type__quote_inductive A
  : forall Γ, has_type (DefaultContext ▻▻ Γ) (quote_inductive A) inductive'.
  Proof. induction A; t_quote. Qed.

  Local Ltac t_has_type' :=
    idtac;
    match goal with
      | [ |- has_type ?Γ (Ast.tApp ?f [?a]) ?B ]
        => refine (@has_type_tApp Γ f Ast.nAnon _ _ a _ _); shelve_unifiable
      | _ => progress simpl
      | _ => exact _
      | _ => apply has_type_tApp_split
      | [ |- has_type _ (quote_term _) (subst_n_name ?e _ _ _) ]
        => progress unify e term'
      | [ |- convertible ?Γ (Ast.tApp (Ast.tConst ?n) _) _ ]
        => let H := fresh in
           pose proof (@conv_delta_Lookup Γ n) as H;
             unfold is_rel_free in H;
             simpl in H;
             etransitivity; [ apply conv_tApp_respectful; [ apply H; intros ? [?|]; simpl; reflexivity | reflexivity ] | ];
             clear H
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
               [ simpl; solve [ exact (fun x => x)
                              | let H' := fresh in
                                intro H';
                                  eapply has_type_conv_subst; [ | solve [ apply conv_tProd_unname ] ];
                                  exact H' ]
               | .. ]
      | [ |- has_type (_ ▻▻ _) _ _ ]
        => apply wkg_rel_free; [ intros ? [?|]; reflexivity | intros ? [?|]; reflexivity | ]
      | [ |- has_type _ _ _ ]
        => eapply has_type_conv_subst;
          [ eapply has_type_tConstruct1_Lookup;
            [ | | simpl; reflexivity ];
            hnf; simpl;
            [ reflexivity | intros ? [?|]; simpl; reflexivity ]
          | ]
      | [ |- has_type _ _ _ ]
        => eapply has_type_conv_subst;
          [ eapply has_type_tInd1_Lookup;
            [ | | simpl; reflexivity ];
            hnf; simpl;
            [ reflexivity | intros ? [?|]; simpl; reflexivity ]
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
      | [ |- convertible _ (Ast.tProd (Ast.nNamed _) _ _) _ ]
        => etransitivity; [ solve [ apply conv_tProd_unname ] | ]
      | [ |- convertible _ _ ?e ]
        => is_evar e; reflexivity
      | [ |- convertible _ ?e ?e ]
        => reflexivity
      | [ |- context[Ast.tApp (Ast.tLambda _ _ _) [_]] ]
        => etransitivity; [ solve [ eapply conv_beta ] | ]; simpl
    end.
  Local Ltac t_has_type := repeat t_has_type'.

  Local Notation Γ := (List.map (fun nT => CBinder (fst nT) (snd nT))) (only parsing).
  Section sub_helpers.
    Context (has_type__quote_term : forall (A : Ast.term),
                                      forall nTs, has_type (DefaultContext ▻▻ Γ nTs) (quote_term A) term').

    Fixpoint has_type__quote_term_helper ls
    : forall nTs, has_type (DefaultContext ▻▻ Γ nTs) (quote_term_helper quote_term ls) (Ast.tApp list' [term']).
    Proof.
      destruct ls as [|y ys]; simpl.
      { intros; t_has_type. }
      { intros nTs.
        specialize (fun nTs => has_type__quote_term_helper ys nTs).
        specialize (fun nTs => has_type__quote_term y nTs).
        induction nTs.
        { specialize (has_type__quote_term_helper nil).
          specialize (has_type__quote_term nil).
          simpl in *.
          t_has_type. }
        { simpl.
          apply (@wkg_rel_free _ [_]%list);
            [ intros ? [?|]; simpl;
              rewrite ?eq__quote_term_helper__closed_helper, ?eq__quote_term__closed_helper by apply eq__quote_term__closed_helper;
              try reflexivity
            | intros ? [?|]; reflexivity | ].
          auto with nocore. } }
    Defined.

    Fixpoint has_type__quote_term_helper_def ls
    : forall nTs, has_type (DefaultContext ▻▻ Γ nTs) (quote_term_helper_def quote_term ls) (Ast.tApp list' [Ast.tApp def' [term']]).
    Proof.
      destruct ls as [|[dnam dtyp dbod] ys]; simpl.
      { intros; t_has_type. }
      { intros nTs.
        specialize (fun nTs => has_type__quote_term_helper_def ys nTs).
        pose proof (fun nTs => has_type__quote_term dtyp nTs) as has_type__quote_term__dtyp.
        pose proof (fun nTs => has_type__quote_term dbod nTs) as has_type__quote_term__dbod.
        clear has_type__quote_term.
        induction nTs.
        { specialize (has_type__quote_term_helper_def nil).
          specialize (has_type__quote_term__dtyp nil).
          specialize (has_type__quote_term__dbod nil).
          simpl in *.
          t_has_type;
          match goal with
            | [ |- convertible _ (Ast.tSort (Ast.sType 1)) (Ast.tSort Ast.sSet) ]
              => admit'
          end. }
        { simpl.
          apply (@wkg_rel_free _ [_]%list);
            [ intros ? [?|]; simpl;
              rewrite ?eq__quote_term_helper_def__closed_helper, ?eq__quote_term__closed_helper, ?eq__quote_nat__closed_helper, ?eq__quote_name__closed_helper by apply eq__quote_term__closed_helper;
              try reflexivity
            | intros ? [?|]; reflexivity | ].
          auto with nocore. } }
    Defined.
  End sub_helpers.

  Fixpoint has_type__quote_term A {struct A}
  : forall nTs, has_type (DefaultContext ▻▻ Γ nTs) (quote_term A) term'.
  Proof.
    destruct A; t_quote;
    try solve [ apply has_type__quote_term_helper; assumption
              | apply has_type__quote_term_helper_def; assumption ];
    t_quote.
    t_has_type.
    t_quote.
  Qed.
End quote_has_type.

Global Instance has_type__quote_term_1 A T
: has_type (DefaultContext ▻ CBinder Ast.nAnon T) (quote_term A) term'
  := @has_type__quote_term A [(Ast.nAnon, T)].

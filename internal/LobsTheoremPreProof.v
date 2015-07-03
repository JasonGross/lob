Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Export Lob.Notations Lob.LobsTheoremStatement.

(** The proof of the theorem *)

Ltac do_shelve tac := tac(*; [ shelve | | ]*).

Module Type LobExtendedContext <: LobContext.
  Axiom Preterm : Type.
  Axiom Context : Type.

  Delimit Scope context_scope with ctx.
  Bind Scope context_scope with Context.

  Axiom empty_context : Context.
  Notation ε := empty_context.
  Axiom context_extend : Context -> Preterm -> Context.
  Notation "Γ ▻ x" := (context_extend Γ x).

  Delimit Scope preterm_scope with preterm.
  Bind Scope preterm_scope with Preterm.

  Global Open Scope preterm_scope.

  Axiom box' : Context -> Preterm -> Type.

  Definition box : Preterm -> Type
    := box' ε.

  Delimit Scope well_typed_term_scope with wtt.
  Bind Scope well_typed_term_scope with box'.
  Bind Scope well_typed_term_scope with box.

  Notation "□ T" := (box T).


  Axiom qbox : Preterm.
  Notation "‘□’" := qbox.

  Axiom tProd : Preterm -> Preterm -> Preterm.
  Notation "x ‘→’ y" := (tProd x y) : preterm_scope.

  Axiom tApp : Preterm -> Preterm -> Preterm.
  Notation "x ‘’ y" := (tApp x y) : preterm_scope.

  Axiom quote : Preterm -> Preterm.
  Notation "⌜ x ⌝" := (quote x).


  Delimit Scope well_typed_term_scope with wtt.
  Bind Scope well_typed_term_scope with box'.
End LobExtendedContext.

Module Type PretermPrimitives (Export LC : LobExtendedContext).
  Axiom tLambda : Preterm -> Preterm -> Preterm.
  Axiom qtApp : Preterm.

  Notation "‘App’" := qtApp : preterm_scope.

  Axiom qtProd : Preterm -> Preterm -> Preterm.
  Notation "x ‘‘→’’ y" := (qtProd x y) : preterm_scope.

  Axiom ttVar0 : forall {Γ T}, box' (Γ ▻ T) T.
  Notation "‘‘VAR₀’’" := ttVar0 : well_typed_term_scope.

  Axiom tVar0 : Preterm.
  Notation "‘VAR₀’" := tVar0.

End PretermPrimitives.

Module Type PreL (LC : LobExtendedContext) (Export PP : PretermPrimitives LC).

  Axiom App : forall {A' B' : Preterm},
                □ (A' ‘→’ B') -> □ A' -> □ B'.

  Axiom wttLambda_nd : forall {Γ : Context} {B' : Preterm},
                       forall A' : Preterm, box' (Γ ▻ A') B' -> box' Γ (A' ‘→’ B').

  Axiom wttApp_1_nd : forall {Γ : Context} {A' B' : Preterm},
                        box' Γ (A' ‘→’ B') -> box' Γ A' -> box' Γ B'.

  Notation "x ‘’ y" := (wttApp_1_nd x%wtt y%wtt) : well_typed_term_scope.

  Axiom box'_weaken : forall {Γ A}, box' ε A -> box' Γ A.
End PreL.

Module Lob1 (LC : LobExtendedContext) (Import LH : LobHypotheses LC).

  Module Type PretermPrimitives' := PretermPrimitives LC.

  Module Type L (PP : PretermPrimitives') (Export PL : PreL LC PP).
    Axiom L : Preterm.
    Axiom qL : Preterm.
    Notation "‘L’" := qL.
  End L.

  Module Type PostL (PP : PretermPrimitives') (PL : PreL LC PP) (Export L' : L PP PL).
    Axiom Conv : □ (‘□’ ‘’ ⌜ L ⌝) -> □ (‘□’ ‘’ ‘L’).

    Axiom Conv2 : □ L -> □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’).
    Axiom Conv2_inv : □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’) -> □ L.
    Axiom qConv2 : forall {Γ},
                     box' Γ (‘□’ ‘’ ‘L’) -> box' Γ (‘□’ ‘’ (⌜ (‘□’ ‘’ ‘L’) ⌝ ‘‘→’’ ⌜ ‘X’ ⌝)).

    Axiom Quot : □ L -> □ (‘□’ ‘’ ⌜ L ⌝).

    Axiom qbApp
    : forall (A' := (⌜ ‘□’ ‘’ ‘L’ ⌝)%preterm)
             (B' := (⌜ ‘X’ ⌝)%preterm),
        □ ((‘□’ ‘’ (A' ‘‘→’’ B')) ‘→’ ‘□’ ‘’ A' ‘→’ ‘□’ ‘’ B').

    Notation "‘‘App’’" := (box'_weaken qbApp) : well_typed_term_scope.

    (*Axiom qConv
  : □ (‘□’ ‘’ ⌜‘□’ ‘’ ⌜L ⌝ ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘□’ ‘’ ‘L’ ⌝).

  Notation "‘‘Conv’’" := (box'_weaken qConv) : well_typed_term_scope.*)

    Axiom qQuote
    : let A := (‘□’ ‘’ ‘L’)%preterm in
      □ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝))).

    Notation "‘‘Quote’’" := (box'_weaken qQuote) : well_typed_term_scope.
  End PostL.
End Lob1.

Module Type Lob1H (Export LC : LobExtendedContext) (Export LH : LobHypotheses LC).
  Module Lob1' := Lob1 LC LH.
  Declare Module Export PP : PretermPrimitives LC.
  Declare Module Export PreL' : PreL LC PP.
  Declare Module Export L' : Lob1'.L PP PreL'.
  Declare Module Export PostL' : Lob1'.PostL PP PreL' L'.
End Lob1H.

Module Lob1' (LC : LobExtendedContext) (Import LH : LobHypotheses LC) (Import M : Lob1H LC LH)
<: LobsTheorem LC LH.
  Notation "‘‘f’’" := (box'_weaken wtt_qf) : well_typed_term_scope.

  Definition lob : X.
    refine ((fun (ℓ : □ L) => f (App (Conv2 ℓ) (Conv (Quot ℓ))))
              (Conv2_inv
                 (wttLambda_nd
                    (‘□’ ‘’ ‘L’)
                    (‘‘f’’ ‘’ ((‘‘App’’ ‘’ (qConv2 ‘‘VAR₀’’)) ‘’ ((*‘‘Conv’’ ‘’*) (‘‘Quote’’ ‘’ ‘‘VAR₀’’))))))).
  Defined.
End Lob1'.

Module Type PretermReflectionPrimitives (Export LC : LobExtendedContext).
  Axiom qPreterm : Preterm.
  Notation "‘Preterm’" := qPreterm : preterm_scope.

  Axiom qquote : Preterm.
  Notation "‘quote’" := qquote : preterm_scope.
End PretermReflectionPrimitives.

Definition crelation (A : Type) := A -> A -> Type.
Definition cflip {A B C : Type} (f : A -> B -> C) := fun x y => f y x.

Class CReflexive {A} (R : crelation A) := creflexivity : forall x : A, R x x.
Class CSymmetric {A} (R : crelation A) := csymmetry : forall x y : A, R x y -> R y x.
Class CTransitive {A} (R : crelation A) := ctransitivity : forall x y z : A, R x y -> R y z -> R x z.
Class CProper {A} (R : crelation A) (m : A) :=
  proper_prf : R m m.

Definition crespectful_hetero
           (A B : Type)
           (C : A -> Type) (D : B -> Type)
           (R : A -> B -> Type)
           (R' : forall (x : A) (y : B), C x -> D y -> Type) :
  (forall x : A, C x) -> (forall x : B, D x) -> Type :=
  fun f g => forall x y, R x y -> R' x y (f x) (g y).

(** The non-dependent version is an instance where we forget dependencies. *)

Definition crespectful {A B} (R : crelation A) (R' : crelation B) : crelation (A -> B) :=
  Eval compute in @crespectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').

Delimit Scope csignature_scope with csignature.

Module Import CProperNotations.

  Notation " R ++> R' " := (@crespectful _ _ (R%csignature) (R'%csignature))
    (right associativity, at level 55) : csignature_scope.

  Notation " R ==> R' " := (@crespectful _ _ (R%csignature) (R'%csignature))
    (right associativity, at level 55) : csignature_scope.

  Notation " R --> R' " := (@crespectful _ _ (cflip (R%csignature)) (R'%csignature))
    (right associativity, at level 55) : csignature_scope.

End CProperNotations.

Arguments CProper {A}%type R%csignature m.
Arguments crespectful {A B}%type (R R')%csignature _ _.


Module Type TypingRules (Export LC : LobExtendedContext) (Export PP : PretermPrimitives LC).
  Axiom capture_avoiding_subst_0 : forall (in_term : Preterm)
                                          (new_value : Preterm),
                                     Preterm.
  Notation "x [ 0 ↦ y ]" := (capture_avoiding_subst_0 x y).
  Axiom convertible : Context -> Preterm -> Preterm -> Type.
  Axiom box'_respectful : forall {Γ A B},
                            convertible Γ A B
                            -> box' Γ A
                            -> box' Γ B.
  Axiom convertible_refl : forall {Γ}, CReflexive (convertible Γ).
  Axiom convertible_sym : forall {Γ}, CSymmetric (convertible Γ).
  Axiom convertible_trans : forall {Γ}, CTransitive (convertible Γ).
  Global Existing Instance convertible_refl.
  Global Existing Instance convertible_sym.
  Global Existing Instance convertible_trans.
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
      CProper (convertible Γ ==> convertible Γ ==> convertible Γ) qtProd.
  Existing Instance qtProd_Proper_convertible.
  Axiom tApp_Proper_convertible
  : forall Γ,
      CProper (convertible Γ ==> convertible Γ ==> convertible Γ) tApp.
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
End TypingRules.

Module Type PretermReflectionTypingRules (Export LC : LobExtendedContext) (Export PP : PretermPrimitives LC) (Export PRP : PretermReflectionPrimitives LC) (Export TR : TypingRules LC PP).
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
End PretermReflectionTypingRules.

Module Type PostL_Assumptions (LC : LobExtendedContext) (Export PP : PretermPrimitives LC).
  Axiom Quot : forall T, □ T -> □ (‘□’ ‘’ ⌜ T ⌝).

  Axiom qQuote
  : forall T,
      let A := (‘□’ ‘’ T)%preterm in
      □ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝))).

  Axiom qbApp
   : forall A' B',
       □ ((‘□’ ‘’ (A' ‘‘→’’ B')) ‘→’ (‘□’ ‘’ A') ‘→’ (‘□’ ‘’ B')).
End PostL_Assumptions.

Module Lob2 (LC : LobExtendedContext) (Import LH : LobHypotheses LC).
  Module Lob1' := Lob1 LC LH.

  Module L (Export PP : PretermPrimitives LC) (Export PL : PreL LC PP) (Export PRP : PretermReflectionPrimitives LC) (Export TR : TypingRules LC PP) (Export PRTR : PretermReflectionTypingRules LC PP PRP TR)
  <: Lob1'.L PP PL.

    Definition L0 (h : Preterm) : Preterm
      := ((‘□’ ‘’ (h ‘’ (quote h))) ‘→’ ‘X’)%preterm.

    Definition qL0 : Preterm
      := tLambda
           ‘Preterm’
           (((‘App’ ‘’ ⌜ ‘□’ ⌝)
               ‘’ ((‘App’ ‘’ ‘VAR₀’ ‘’ (‘App’ ‘’ ‘quote’ ‘’ ‘VAR₀’))))
              ‘‘→’’
              ⌜ ‘X’ ⌝).

    Notation "‘L0’" := qL0.

    Definition L : Preterm
      := L0 ‘L0’.

    Definition qL : Preterm
      := ‘L0’ ‘’ ⌜ ‘L0’ ⌝.

    Notation "‘L’" := qL.
  End L.

  Module PostL (Export PP : PretermPrimitives LC) (Export PL : PreL LC PP) (Export PRP : PretermReflectionPrimitives LC) (Export TR : TypingRules LC PP) (Export PRTR : PretermReflectionTypingRules LC PP PRP TR) (LA : PostL_Assumptions LC PP).
    Module L' := L PP PL PRP TR PRTR.
    Include L'.

    Module M <: Lob1'.PostL PP PL L'.

      Local Ltac conv_rewrite
        := repeat match goal with
                    | [ |- convertible _ ?x ?x ] => reflexivity
                    | [ |- convertible _ (?x ‘’ _) (?x ‘’ _) ]
                      => apply tApp_Proper_convertible; [ reflexivity | ]
                    | [ |- convertible _ (_ ‘‘→’’ _) (_ ‘‘→’’ _) ]
                      => apply qtProd_Proper_convertible
                    | [ |- convertible ?Γ ?lhs ?rhs ]
                      => is_evar rhs;
                        match lhs with
                          | appcontext G[tLambda ?A ?f ‘’ ?a]
                            => let G' := context G[(f) [0 ↦ a]] in
                               eapply (@ctransitivity _ _ _ _ G' _); [ solve [ conv_rewrite ] | ]
                        end
                    | _ => progress rewrite ?convertible__capture_avoiding_subst_0__tApp, ?convertible__qtApp__closed, ?convertible__quote__closed, ?convertible__quote__app, ?convertible__capture_avoiding_subst_0__tVar0, ?convertible__qquote__closed, ?convertible__capture_avoiding_subst_0__qtProd, ?convertible__quote__qtProd, ?convertible_beta_app_lambda
                  end.

      Definition Conv : □ (‘□’ ‘’ ⌜ L ⌝) -> □ (‘□’ ‘’ ‘L’).
      Proof.
        unfold box, L, qL.
        do_shelve
          ltac:(refine (fun box_L => let box_L' := box'_respectful _ box_L in _ box_L')).
        { unfold L0, qL0; conv_rewrite.
          pose convertible__quote__app.
          match goal with
                    | [ |- convertible ?Γ ?lhs ?rhs ]
                      => is_evar rhs;
                        match lhs with
                          | appcontext G[tLambda ?A ?f ‘’ ?a]
                            => let G' := context G[(f) [0 ↦ a]] in
                               eapply (@ctransitivity _ _ _ _ G' _); [ solve [ conv_rewrite ] | ]
                        end
end.

  match goal with
        | [ |- convertible ?Γ ?lhs ?rhs ]
                      => is_evar rhs;
                        match lhs with
                          | appcontext G[tLambda ?A ?f ‘’ ?a]
                            => let G' := context G[(f) [0 ↦ a]] in
                               eapply (@ctransitivity _ _ _ _ G' _); [ | ]
                        end

end.
Focus 2.


          match goal with
            | [ |- convertible ?Γ ?lhs ?rhs ]
              => is_evar rhs;
                match lhs with
                  | appcontext G[tLambda ?A ?f ‘’ ?a]
                    => let G' := context G[(f) [0 ↦ a]] in
                       eapply (@ctransitivity _ _ _ _ G' _)
                end
          end.
exact _.
          pose convertible__capture_avoiding_subst_0__tApp.
          reflexivity. }
        { clear.
          unfold L0, qL0.
          intro box_L.
          eapply box'_respectful.
          { conv_rewrite.
            reflexivity. }
          { revert box_L.
            match goal with
              | [ |- context[quote (quote ?X)] ] => generalize X; intro T
            end.
            apply box_qtProd_dom_precompose.
            apply box_quote_app_quote. } }
      Defined.

      Definition Conv2 : □ L -> □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’)
        := fun x => x.
      Definition Conv2_inv : □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’) -> □ L
        := fun x => x.
      Definition qConv2 {Γ}
      : box' Γ (‘□’ ‘’ ‘L’) -> box' Γ (‘□’ ‘’ (⌜‘□’ ‘’ ‘L’ ⌝ ‘‘→’’ ⌜ ‘X’ ⌝)).
      Proof.
        unfold qL.
        do_shelve
          ltac:(refine (fun box_L => let box_L' := box'_respectful _ box_L in _ box_L')).
        { unfold L0, qL0; conv_rewrite.
          reflexivity. }
        { clear.
          unfold L0, qL0.
          intro box_L.
          eapply box'_respectful.
          { conv_rewrite.
            reflexivity. }
          { revert box_L.
            match goal with
              | [ |- context[quote (quote ?X)] ] => generalize X; intro T
            end.
            apply box_qtProd_dom_precompose.
            apply box_quote_app_quote_inv. } }
      Defined.

      (*Axiom qConv
  : □ (‘□’ ‘’ ⌜‘□’ ‘’ ⌜L ⌝ ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘□’ ‘’ ‘L’ ⌝).

  Notation "‘‘Conv’’" := (box'_weaken qConv) : well_typed_term_scope.*)

      Definition Quot : □ L -> □ (‘□’ ‘’ ⌜ L ⌝)
        := LA.Quot _.

      Definition qbApp
      : forall (A' := (⌜‘□’ ‘’ ‘L’ ⌝)%preterm)
               (B' := (⌜‘X’ ⌝)%preterm),
          □ ((‘□’ ‘’ (A' ‘‘→’’ B')) ‘→’ (‘□’ ‘’ A') ‘→’ (‘□’ ‘’ B'))
        := LA.qbApp _ _.

      Notation "‘‘App’’" := (box'_weaken qbApp) : well_typed_term_scope.

      Definition qQuote
      : let A := (‘□’ ‘’ ‘L’)%preterm in
        □ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝)))
        := LA.qQuote _.

      Notation "‘‘Quote’’" := (box'_weaken qQuote) : well_typed_term_scope.
    End M.
  End PostL.
End Lob2.

Module Type Lob2H (Export LC : LobExtendedContext) (Export LH : LobHypotheses LC).
  Module Lob2' := Lob2 LC LH.
  Declare Module Export PP : PretermPrimitives LC.
  Declare Module Export PreL' : PreL LC PP.
  Declare Module Export PRP : PretermReflectionPrimitives LC.
  Declare Module Export TR : TypingRules LC PP.
  Declare Module Export PRTR : PretermReflectionTypingRules LC PP PRP TR.
  Declare Module Export LA : PostL_Assumptions LC PP.
End Lob2H.

Module Lob2'0 (LC : LobExtendedContext) (LH : LobHypotheses LC) (M : Lob2H LC LH)
<: LobsTheorem LC LH.
  Module Lob1HV <: Lob1H LC LH.
    Include M.
    Include M.Lob2'.
    Module L' <: Lob1'.L PP PreL'
      := L PP PreL' PRP TR PRTR.
    Module PostL'' := M.Lob2'.PostL PP PreL' PRP TR PRTR LA.
    Module PostL' <: Lob1'.PostL PP PreL' L'
      := PostL''.M.
  End Lob1HV.
  Module M' := Lob1' LC LH Lob1HV.
  Definition lob := M'.lob.
End Lob2'0.

Module LobOfPreLob
       (Export LC : LobExtendedContext)
       (Export LH : LobHypotheses LC)
       (Export PP : PretermPrimitives LC)
       (Export PreL' : PreL LC PP)
       (Export PRP : PretermReflectionPrimitives LC)
       (Export TR : TypingRules LC PP)
       (Export PRTR : PretermReflectionTypingRules LC PP PRP TR)
       (Export LA : PostL_Assumptions LC PP)
<: LobsTheorem LC LH.
  Module M'0 <: Lob2H LC LH.
    Module Lob2' := Lob2 LC LH.
    Module PP := PP.
    Module PreL' := PreL'.
    Module PRP := PRP.
    Module TR := TR.
    Module PRTR := PRTR.
    Module LA := LA.
  End M'0.
  Include (Lob2'0 LC LH M'0).
End LobOfPreLob.

Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Export Lob.Notations Lob.LobsTheoremStatement.

(** The proof of the theorem *)

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

Module Lob1 (LC : LobExtendedContext) (Import LH : LobHypotheses LC).

  Module Type PretermPrimitives' := PretermPrimitives LC.

  Module Type PreL (Export PP : PretermPrimitives').

    Axiom App : forall {A' B' : Preterm},
                  □ (A' ‘→’ B') -> □ A' -> □ B'.

    Axiom wttLambda_nd : forall {Γ : Context} {B' : Preterm},
                         forall A' : Preterm, box' (Γ ▻ A') B' -> box' Γ (A' ‘→’ B').

    Axiom wttApp_1_nd : forall {Γ : Context} {A' B' : Preterm},
                          box' Γ (A' ‘→’ B') -> box' Γ A' -> box' Γ B'.

    Notation "x ‘’ y" := (wttApp_1_nd x%wtt y%wtt) : well_typed_term_scope.

    Axiom box'_weaken : forall {Γ A}, box' ε A -> box' Γ A.

    Notation "‘‘f’’" := (box'_weaken wtt_qf) : well_typed_term_scope.
  End PreL.

  Module Type L (PP : PretermPrimitives') (Export PL : PreL PP).
    Axiom L : Preterm.
    Axiom qL : Preterm.
    Notation "‘L’" := qL.
  End L.

  Module Type PostL (PP : PretermPrimitives') (PL : PreL PP) (Export L' : L PP PL).
    Axiom Conv : □ (‘□’ ‘’ ⌜ L ⌝) -> □ (‘□’ ‘’ ‘L’).

    Axiom Conv2 : □ L -> □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’).
    Axiom Conv2_inv : □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’) -> □ L.
    Axiom qConv2 : forall {Γ},
                     box' Γ (‘□’ ‘’ ‘L’) -> box' Γ (‘□’ ‘’ ⌜‘□’ ‘’ ‘L’ ⌝ ‘‘→’’ ‘□’ ‘’ ⌜‘X’ ⌝).

    Axiom Quot : □ L -> □ (‘□’ ‘’ ⌜ L ⌝).

    Axiom qbApp
    : forall (A' := (‘□’ ‘’ ⌜‘□’ ‘’ ‘L’ ⌝)%preterm)
             (B' := (‘□’ ‘’ ⌜‘X’ ⌝)%preterm),
        □ ((A' ‘‘→’’ B') ‘→’ A' ‘→’ B').

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
  Declare Module Export PreL' : Lob1'.PreL PP.
  Declare Module Export L' : Lob1'.L PP PreL'.
  Declare Module Export PostL' : Lob1'.PostL PP PreL' L'.
End Lob1H.

Module Lob1' (LC : LobExtendedContext) (Import LH : LobHypotheses LC) (Import M : Lob1H LC LH)
<: LobsTheorem LC LH.
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

Module Type TypingRules (Export LC : LobExtendedContext) (Export PP : PretermPrimitives LC).
  Axiom capture_avoiding_subst_0 : forall (in_term : Preterm)
                                          (new_value : Preterm),
                                     Preterm.
  Notation "x [ 0 ↦ y ]" := (capture_avoiding_subst_0 x y).
  Axiom convertible : Context -> Preterm -> Preterm -> Prop.
  Axiom box'_respectful : forall {Γ A B},
                            convertible Γ A B
                            -> box' Γ A
                            -> box' Γ B.
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
End TypingRules.

Module Type PretermReflectionTypingRules (Export LC : LobExtendedContext) (Export PP : PretermPrimitives LC) (Export PRP : PretermReflectionPrimitives LC) (Export TR : TypingRules LC PP).
  Axiom convertible__qquote__closed
  : forall Γ x,
      convertible Γ (‘quote’ [ 0 ↦ x ]) (‘quote’).
End PretermReflectionTypingRules.



Module Lob2 (LC : LobExtendedContext) (Import LH : LobHypotheses LC).
  Module Lob1' := Lob1 LC LH.

  Module L (Export PP : PretermPrimitives LC) (Export PL : Lob1'.PreL PP) (Export PRP : PretermReflectionPrimitives LC) (Export TR : TypingRules LC PP) (Export PRTR : PretermReflectionTypingRules LC PP PRP TR)
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

  Module PostL (Export PP : PretermPrimitives LC) (Export PL : Lob1'.PreL PP) (Export PRP : PretermReflectionPrimitives LC) (Export TR : TypingRules LC PP) (Export PRTR : PretermReflectionTypingRules LC PP PRP TR)
  <: Lob1'.PostL.
    Module L' := L PP PL PRP TR PRTR.
    Include L'.

    Definition Conv : □ (‘□’ ‘’ ⌜ L ⌝) -> □ (‘□’ ‘’ ‘L’).
    Proof.
      unfold box, L, qL.
      apply box'_respectful.
      apply convertible_tApp.
      { reflexivity. }
      { unfold L0, qL0.
        symmetry.
        etransitivity; [ solve [ apply convertible_beta_app_lambda ] | ].
        rewrite convertible__capture_avoiding_subst_0__qtProd.
        rewrite convertible__quote__qtProd.
        apply qtProd_Proper_convertible; [ | solve [ apply convertible__quote__closed ] ].
        repeat match goal with
                 | [ |- convertible _ ?x ?x ] => reflexivity
                 | [ |- convertible _ (?x ‘’ _) (?x ‘’ _) ]
                   => apply tApp_Proper_convertible; [ reflexivity | ]
                 | _ => progress rewrite ?convertible__capture_avoiding_subst_0__tApp, ?convertible__qtApp__closed, ?convertible__quote__closed, ?convertible__quote__app, ?convertible__capture_avoiding_subst_0__tVar0, ?convertible__qquote__closed
               end.

        apply tApp_Proper_convertible.
        rewrite convertible__capture_avoiding_subst_0__tApp.
        etransitivity; [ sov
Axiom convertible__quote__box_app
  : forall Γ x,
      convertible Γ (⌜ ‘□’ ‘’ x ⌝) ((‘App’ ‘’ ⌜ ‘□’ ⌝) ‘’ ⌜ x ⌝).
        admit. }
    Defined.

    Axiom Conv2 : □ L -> □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’).
    Axiom Conv2_inv : □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’) -> □ L.
    Axiom qConv2 : forall {Γ},
                     box' Γ (‘□’ ‘’ ‘L’) -> box' Γ (‘□’ ‘’ ⌜‘□’ ‘’ ‘L’ ⌝ ‘‘→’’ ‘□’ ‘’ ⌜‘X’ ⌝).

    Axiom Quot : □ L -> □ (‘□’ ‘’ ⌜ L ⌝).

    Axiom qtApp
    : forall (A' := (‘□’ ‘’ ⌜‘□’ ‘’ ‘L’ ⌝)%preterm)
             (B' := (‘□’ ‘’ ⌜‘X’ ⌝)%preterm),
        □ ((A' ‘‘→’’ B') ‘→’ A' ‘→’ B').

    Notation "‘‘App’’" := (box'_weaken qtApp) : well_typed_term_scope.

    (*Axiom qConv
  : □ (‘□’ ‘’ ⌜‘□’ ‘’ ⌜L ⌝ ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘□’ ‘’ ‘L’ ⌝).

  Notation "‘‘Conv’’" := (box'_weaken qConv) : well_typed_term_scope.*)

    Axiom qQuote
    : let A := (‘□’ ‘’ ‘L’)%preterm in
      □ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝))).

    Notation "‘‘Quote’’" := (box'_weaken qQuote) : well_typed_term_scope.

  End PostL.


Module Type Lob2 (LC : LobExtendedContext) (Import LH : LobHypotheses LC).
  Axiom App : forall {A' B' : Preterm},
                □ (A' ‘→’ B') -> □ A' -> □ B'.

  Axiom L : Preterm.
  Axiom qL : Preterm.
  Notation "‘L’" := qL.

  Axiom qtProd : Preterm -> Preterm -> Preterm.
  Notation "x ‘‘→’’ y" := (qtProd x y) : preterm_scope.

  Axiom Conv : □ (‘□’ ‘’ ⌜ L ⌝) -> □ (‘□’ ‘’ ‘L’).

  Axiom Conv2 : □ L -> □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’).
  Axiom Conv2_inv : □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’) -> □ L.
  Axiom qConv2 : forall {Γ},
                   box' Γ (‘□’ ‘’ ‘L’) -> box' Γ (‘□’ ‘’ ⌜‘□’ ‘’ ‘L’ ⌝ ‘‘→’’ ‘□’ ‘’ ⌜‘X’ ⌝).

  Axiom Quot : □ L -> □ (‘□’ ‘’ ⌜ L ⌝).

  Axiom wttLambda_nd : forall {Γ : Context} {B' : Preterm},
                       forall A' : Preterm, box' (Γ ▻ A') B' -> box' Γ (A' ‘→’ B').

  Axiom wttApp_1_nd : forall {Γ : Context} {A' B' : Preterm},
                        box' Γ (A' ‘→’ B') -> box' Γ A' -> box' Γ B'.

  Notation "x ‘’ y" := (wttApp_1_nd x%wtt y%wtt) : well_typed_term_scope.

  Axiom box'_weaken : forall {Γ A}, box' ε A -> box' Γ A.

  Notation "‘‘f’’" := (box'_weaken wtt_qf) : well_typed_term_scope.

  Axiom qtApp
  : forall (A' := (‘□’ ‘’ ⌜‘□’ ‘’ ‘L’ ⌝)%preterm)
           (B' := (‘□’ ‘’ ⌜‘X’ ⌝)%preterm),
      □ ((A' ‘‘→’’ B') ‘→’ A' ‘→’ B').

  Notation "‘‘App’’" := (box'_weaken qtApp) : well_typed_term_scope.

  Axiom ttVar0 : forall {Γ T}, box' (Γ ▻ T) T.

  Notation "‘‘VAR₀’’" := ttVar0.

  Axiom tVar0 : Preterm.
  Notation "‘VAR₀’" := tVar0.

  Axiom qQuote
  : let A := (‘□’ ‘’ ‘L’)%preterm in
    □ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝))).

  Notation "‘‘Quote’’" := (box'_weaken qQuote) : well_typed_term_scope.
End Lob1.

Module Lob1' (LC : LobExtendedContext) (Import LH : LobHypotheses LC) (Import M : Lob1 LC LH)
<: LobsTheorem LC LH.
  Definition lob : X.
    refine ((fun (ℓ : □ L) => f (App (Conv2 ℓ) (Conv (Quot ℓ))))
              (Conv2_inv
                 (wttLambda_nd
                    (‘□’ ‘’ ‘L’)
                    (‘‘f’’ ‘’ ((‘‘App’’ ‘’ (qConv2 ‘‘VAR₀’’)) ‘’ ((*‘‘Conv’’ ‘’*) (‘‘Quote’’ ‘’ ‘‘VAR₀’’))))))).
  Defined.
End Lob1'.
*)
End Lob2.

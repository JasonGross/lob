Require Import Coq.Setoids.Setoid.
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

Module Lob1 (LC : LobExtendedContext) (Import LH : LobHypotheses LC).

  Module Type PreL.
    Axiom App : forall {A' B' : Preterm},
                  □ (A' ‘→’ B') -> □ A' -> □ B'.

    Axiom qtProd : Preterm -> Preterm -> Preterm.
    Notation "x ‘‘→’’ y" := (qtProd x y) : preterm_scope.

    Axiom ttVar0 : forall {Γ T}, box' (Γ ▻ T) T.
    Notation "‘‘VAR₀’’" := ttVar0.

    Axiom wttLambda_nd : forall {Γ : Context} {B' : Preterm},
                         forall A' : Preterm, box' (Γ ▻ A') B' -> box' Γ (A' ‘→’ B').

    Axiom wttApp_1_nd : forall {Γ : Context} {A' B' : Preterm},
                          box' Γ (A' ‘→’ B') -> box' Γ A' -> box' Γ B'.

    Notation "x ‘’ y" := (wttApp_1_nd x%wtt y%wtt) : well_typed_term_scope.

    Axiom box'_weaken : forall {Γ A}, box' ε A -> box' Γ A.

    Notation "‘‘f’’" := (box'_weaken wtt_qf) : well_typed_term_scope.
  End PreL.

  Module Type L.
    Include PreL.
    Axiom L : Preterm.
    Axiom qL : Preterm.
    Notation "‘L’" := qL.
  End L.

  Module Type PostL.
    Include L.

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

Module Type Lob1H (LC : LobExtendedContext) (Import LH : LobHypotheses LC).
  Module Lob1' := Lob1 LC LH.
  Include Lob1'.PostL.
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

Module Type PretermPrimitives (Export LC : LobExtendedContext).
  Axiom tLambda : Preterm -> Preterm -> Preterm.
  Axiom qtApp : Preterm.

  Notation "‘App’" := qtApp : preterm_scope.
End PretermPrimitives.

Module Type PretermReflectionPrimitives (Export LC : LobExtendedContext).
  Axiom qPreterm : Preterm.
  Notation "‘Preterm’" := qPreterm : preterm_scope.
End PretermReflectionPrimitives.

Module Type TypingRules (Import LC : LobExtendedContext) (Import PP : PretermPrimitives LC).
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
End TypingRules.

Module Lob2 (LC : LobExtendedContext) (Import LH : LobHypotheses LC).
  Module Lob1' := Lob1 LC LH.
  Module Type PretermPrimitives' := PretermPrimitives LC.
  Module Type PretermReflectionPrimitives' := PretermReflectionPrimitives LC.
  Module Type PreL'.
    Include Lob1'.PreL.
    Include PretermPrimitives'.
    Include PretermReflectionPrimitives'.
  End PreL'.

  Module L (PL : PreL') <: Lob1'.L.
    Include PL.

    Definition L0 (h : Preterm) : Preterm
      := ((‘□’ ‘’ (h ‘’ (quote h))) ‘→’ ‘X’)%preterm.

    Definition qL0 : Preterm.
    Proof.
      refine (tLambda
                ‘Preterm’
                (‘App’
                  ‘’ _(*‘□’*)           (*( *)
             )).

      admit.
   (*:= (fun h : Preterm => (‘□’ ‘’ (h ‘’ (quote h))) ‘→’ ‘X’).*)
    Defined.

    Notation "‘L0’" := qL0.

    Definition L : Preterm
      := L0 ‘L0’.

    Definition qL : Preterm
      := ‘L0’ ‘’ ⌜ ‘L0’ ⌝.

    Notation "‘L’" := qL.
  End L.

(*  Module PostL (PL : PreL') (Import TR : TypingRules LC PL) <: Lob1'.PostL.
    Module L' := L PL.
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

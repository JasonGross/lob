Require Import Setoid.
Set Implicit Arguments.
Set Universe Polymorphism.

Let typeof {T : Type} (_ : T) := T.

Parameter IsProvable : Prop -> Prop.
(* If the result of substituting x for 'x' in x is provable in PA, then C *)

Axiom L : forall C : Prop, Prop.

Notation "[[ x ]]" := (IsProvable x) (at level 50).
Notation "◻ x" := (IsProvable x) (at level 50, no associativity).

Definition IsProvableIsProvable (X : Prop) := [[ X ]] -> [[ [[ X ]] ]].
Axiom A1 : forall X : Prop, IsProvableIsProvable X.
Definition A1IsProvable X := [[ IsProvableIsProvable X ]].
Axiom A2 : forall X : Prop, A1IsProvable X.
Definition ModusPonensT (X Y : Prop) : Prop :=
  [[ X -> Y ]] -> [[ X ]] -> [[ Y ]].
Definition MPIsProvable (X Y : Prop) := IsProvable (ModusPonensT X Y).
Axiom A3 : forall X Y : Prop, MPIsProvable X Y.

Axiom MP : forall X Y : Prop, ModusPonensT X Y.

Axiom B1 : forall A B C : Prop, [[ A -> B ]] -> [[ B -> C ]] -> [[ A -> C ]].

Axiom B2 : forall A B C : Prop, [[ A -> B ]] -> [[ A -> (B -> C) ]] -> [[ A -> C ]].

Axiom L_Construction_1 : forall C : Prop, [[ L C -> ([[ L C ]] -> C) ]].
Axiom L_Construction_2 : forall C : Prop, [[ ([[ L C ]] -> C) -> L C ]].

Axiom C1 : forall A : Prop, A -> [[ A ]].

Section lob.
  Variable C : Prop.

  Lemma Step1a : [[ [[ L C ]] -> [[ [[ L C ]] -> C ]] ]].
  Proof.
    apply C1.
    apply MP.
    apply (L_Construction_1 C).
  Qed.

  Lemma Step1b : [[ [[ [[ L C ]] -> C ]] -> [[ L C ]] ]].
  Proof.
    apply C1.
    apply MP.
    apply (L_Construction_2 C).
  Qed.

  Hypothesis LobsHypothesis : [[ [[ C ]] -> C ]].

  Lemma Step3 : [[ [[ [[ L C ]] -> C ]] -> ([[ [[ L C ]] ]] -> [[ C ]])]].
  Proof.
    apply A3.
  Qed.

  Lemma Step4 : [[ [[ L C ]] -> ( [[ [[ L C ]] ]] -> [[ C ]]) ]].
  Proof.
    exact (B1 Step1a Step3).
  Qed.

  Lemma Step5 : [[ [[ L C ]] -> [[ [[ L C ]] ]] ]].
  Proof.
    apply A2.
  Qed.

  Lemma Step6 : [[ [[ L C ]] -> [[ C ]] ]].
  Proof.
    apply (B2 Step5 Step4).
  Qed.

  Lemma Step7 : [[ [[ L C ]] -> C ]].
  Proof.
    apply (B1 Step6 LobsHypothesis).
  Qed.

  Lemma Step8 : [[ [[ [[ L C ]] -> C ]] ]].
  Proof.
    apply (A1 Step7).
  Qed.
  Lemma Step9 : [[ [[ L C ]] ]].
  Proof.
    apply (MP Step1b Step8).
  Qed.

  Lemma Step10 : [[ C ]].
  Proof.
    apply (MP Step7 Step9).
  Qed.
End lob.

Lemma MaterialImplication (X Y : Prop) : ((X -> Y) -> Y) -> (~X -> Y).
  exact (fun f nx => f (fun x => match nx x with end)).
Qed.

Axiom DeductionTheorem0 : forall A X : Prop, (A -> ◻ X) -> ◻(A -> X).
Axiom DeductionTheorem1 : forall A X : Prop, (◻ A -> ◻ X) -> ◻(A -> X).


Print Step10.
Check (fun C => DeductionTheorem1 (@Step10 C)).

Axiom MaterialImplicationProvable : forall X Y : Prop, ◻((X -> Y) -> Y) -> ◻(~X -> Y).

Check (fun C => MP (MaterialImplicationProvable (DeductionTheorem1 (@Step10 C)))).


Print Step10.

(*Axiom MaterialImplication*)

Print Assumptions Step10.

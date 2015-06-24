(* -*- coq-prog-args: ("-emacs" "-top" "lob") -*- *)
(* Runs on top of https://github.com/gmalecha/template-coq *)
Require Import Template.Template.

Require Import Coq.Strings.String.
Require Import Coq.Program.Program.
Require Import Coq.PArith.BinPos.
Local Open Scope string_scope.
Local Open Scope positive_scope.

Require Export quote_term.
Require Export quote_has_type.

Notation "( x ; y )" := (existT _ x y).
Notation "x .1" := (projT1 x) (at level 3, format "x '.1'").
Notation "x .2" := (projT2 x) (at level 3, format "x '.2'").

Delimit Scope preterm_scope with preterm.
Bind Scope preterm_scope with Ast.term.
Local Open Scope preterm_scope.

Notation "x ‘→’ y" := (Ast.tProd Ast.nAnon x%preterm y%preterm) (at level 99, right associativity, y at level 200) : preterm_scope.
Notation "x ‘’ y" := (Ast.tApp x%preterm (cons y%preterm nil)) (at level 15, left associativity) : preterm_scope.
Quote Definition arrow''0 := (Ast.tProd Ast.nAnon).
Definition arrow'' x y
  := Eval cbv beta iota delta [arrow''0 List.app] in
      match arrow''0 as a
            return match a with
                     | Ast.tApp _ _ => Ast.term
                     | _ => True
                   end
      with
        | Ast.tApp f ls => Ast.tApp f (ls ++ [x; y])
        | _ => I
      end.
Notation "x ‘‘→’’ y" := (arrow'' x y) (at level 99, right associativity, y at level 200) : preterm_scope.


Definition Preterm := Ast.term.
Quote Definition Preterm' := Ast.term.

Bind Scope preterm_scope with Preterm.

Notation "‘Preterm’" := Preterm'.

Axiom X : Type.
Quote Definition qX := X.
Check qX : Preterm.
Notation "‘X’" := qX.

Definition box (Γ : Context) (T : Preterm) : Type
  := { t : Preterm & has_type Γ t T }.

Notation "□" := (box nil).

Delimit Scope well_typed_term_scope with wtt.
Bind Scope well_typed_term_scope with box.

Axiom f : □ ‘X’ -> X.
Quote Definition qf := f.
Check qf : Preterm.
Notation "‘f’" := qf.

(*Quote Recursively Definition Γ :=
  (let dummy_sigma := sigT in
   let dummy_X := X in
   has_type : Preterm -> Preterm -> Type).*)

Definition box' : Preterm.
Proof.
  let term := (eval cbv delta in □) in
  quote_term term (fun x => exact x).
Defined.

Notation "‘□’" := box'.

Definition quot' : Preterm.
Proof.
  let t := (eval cbv beta delta [qO qS qEmptyString qString qnAnon qAscii qnil qcons qmkdef qtInd qtFix qtCase qtUnknown qtRel qtConstruct qtEvar qtMeta qtVar qtApp qtConst qtSort qtCast qtProd inductive_quotable quote_ascii bool_quotable quote_bool (*quote_string quote_positive quote_nat*) ident_quotable quote_ident quote_name nat_quotable name_quotable quote quote_term sort_quotable cast_kind_quotable quote_sort qsSet qsProp qsType universe_quotable quote_inductive qmkInd] in quote_term) in
  quote_term t (fun x => exact x).
Defined.

Notation "‘quote’" := quot'.

Notation "⌜ x ⌝" := (quote x).

Notation "‘λ’ ( x : T ) ‘⇒’ body"
  := (Ast.tLambda (Ast.nNamed x) T body) (at level 15).

Axiom has_type_f : has_type nil ‘f’ ((‘□’ ‘’ ⌜ ‘X’ ⌝) ‘→’ ‘X’).

Global Instance f_has_type {Γ} : has_type Γ ‘f’ ((‘□’ ‘’ ⌜ ‘X’ ⌝) ‘→’ ‘X’).
Proof.
  apply (has_type_weaken nil).
  apply has_type_f.
Defined.

Notation "‘‘f’’" := (‘f’; f_has_type).

Definition App {A' B' : Preterm}
: □ (A' ‘→’ B') -> □ A' -> □ B'.
Proof.
  intros box_A'_impl'_B' box_A'.
  refine (box_A'_impl'_B'.1 ‘’ box_A'.1; _).
  eapply has_type_tApp.
  { exact (box_A'_impl'_B'.2). }
  { exact (box_A'.2). }
Defined.

Definition App' : Preterm.
Proof.
  let t := (eval cbv delta [App] in @App) in
  quote_term t (fun x => exact x).
Defined.

Notation "‘App’" := App'.

Definition Quot0 {T' : Preterm}
: □ T' -> □ (‘□’ ‘’ ⌜ T' ⌝).
Proof.
  intros box_T'.
  refine (Ast.tApp ‘existT’ [‘Preterm’; _; quote box_T'.1; _]; _).
  do 4 (apply has_type_beta_1_type with (f := fun x => x); simpl).
  eapply has_type_existT.
  { apply quote_term_has_type. }
  { do 1 (apply has_type_beta_1_type with (f := fun x => x); simpl).
    (** Need to somehow lift (quine?) typing derivation here *)
    exfalso; admit.
    Grab Existential Variables.
    admit. }
Defined.

Definition L0 (h : Preterm) : Preterm
  := (‘□’ ‘’ (h ‘’ (quote h))) ‘→’ ‘X’.

Quote Definition L0' := (fun h : Preterm => (‘□’ ‘’ (h ‘’ (quote h))) ‘→’ ‘X’).

Notation "‘L0’" := L0'.

Definition L : Preterm
  := L0 ‘L0’.

Definition L' : Preterm
  := ‘L0’ ‘’ ⌜ ‘L0’ ⌝.

Notation "‘L’" := L'.

Definition Quot
: □ L -> □ (‘□’ ‘’ ⌜ L ⌝)
  := Eval cbv beta delta [Quot0] in @Quot0 L.

Definition Quot' : Preterm.
Proof.
  let t := (eval cbv delta [Quot box] in @Quot) in
  quote_term t (fun x => exact x).
Defined.

Notation "‘Quot’" := Quot'.

Definition Quot'_has_type {Γ : Context}
: has_type Γ ‘Quot’ ((‘□’ ‘’ ‘L’) ‘→’ (‘□’ ‘’ (⌜ (‘□’ ‘’ ⌜ L ⌝) ⌝))).
Proof.
  apply (has_type_weaken nil).
  Timeout 5 apply has_type_beta_1_term with (f := fun x => x).
  Timeout 5 apply has_type_beta_1_type with (f := fun x => x).
  admit.
Admitted.

Notation "‘‘Quot’’" := (Quot'; Quot'_has_type).

Definition Conv_has_type (box_box_L : □ (‘□’ ‘’ ⌜ L ⌝))
: has_type nil box_box_L.1 (‘□’ ‘’ ‘L’).
Proof.
  (*unfold box' in *.
  apply has_type_beta_1_type with (f := fun x => x); simpl.
  apply has_type_beta_1_type with (f := fun x => x); simpl.
  destruct box_box_L as [x h]; simpl.
  apply has_type_eta_1_type with (f := fun x => x) in h; simpl in h.
  apply has_type_eta_1_type with (f := fun x => x) in h; simpl in h.
  unfold quote, term_quotable in *.
  let T := match type of h with has_type _ _ ?T => constr:T end in
  let T' := (match eval pattern (quote_term L) in T with ?T' _ => constr:T' end) in
  let x := match type of h with has_type _ ?x ?T => constr:x end in
  revert h;
    set (T'' := T');
    change (has_type nil x (T'' (quote_term L)) -> has_type nil x (T'' ‘L’));
    clearbody T'';
    intro h.
  unfold L, L' in *.
  unfold quote, term_quotable in *.
  unfold L0 in *.
  unfold L0'.
  simpl in h.
  unfold quote_term_step in h.
  simpl in h.
  apply has_type_beta_1_type with (f := T''); simpl.*)
  admit.
Admitted.

Definition Conv (box_box_L : □ (‘□’ ‘’ ⌜ L ⌝))
: □ (‘□’ ‘’ ‘L’).
Proof.
  refine (box_box_L.1; _).
  apply Conv_has_type.
Defined.

Definition Conv' : Preterm.
Proof.
  let t := (eval cbv delta [Conv] in @Conv) in
  quote_term t (fun x => exact x).
Defined.

Notation "‘Conv’" := Conv'.

Definition Conv'_has_type {Γ : Context}
: has_type Γ ‘Conv’ (‘□’ ‘’ ⌜‘□’ ‘’ ⌜L ⌝ ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘□’ ‘’ ‘L’ ⌝).
Proof.
  apply (has_type_weaken nil).
  admit.
Defined.

Notation "‘‘Conv’’" := (‘Conv’; Conv'_has_type).

Definition Conv2 : □ L -> □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’)
  := fun x => x.

Definition Conv2' {Γ}
: box Γ (‘□’ ‘’ ‘L’) -> box Γ (‘□’ ‘’ ⌜‘□’ ‘’ ‘L’ ⌝ ‘‘→’’ ‘□’ ‘’ ⌜‘X’ ⌝).
Proof.
  intro box_box_L.
  refine (box_box_L.1; _).
  pose proof (box_box_L.2) as bbLT.
  admit.
Admitted.

Definition ttLambda_nd {Γ : Context} {B' : Preterm}
: Ast.name -> forall A' : Preterm, box (Γ ▻ A') B' -> box Γ (A' ‘→’ B').
Proof.
  refine (fun n A' body
          => (Ast.tLambda n A' body.1;
              _)).
  apply has_type_tLambda.
  exact body.2.
Defined.

Definition ttApp_1_nd {Γ : Context} {A' B' : Preterm}
: box Γ (A' ‘→’ B') -> box Γ A' -> box Γ B'.
Proof.
  refine (fun F x
          => (Ast.tApp F.1 [x.1];
              _)).
  eapply has_type_tApp.
  { exact F.2. }
  { exact x.2. }
Defined.

Notation "x ‘’ y" := (ttApp_1_nd x%wtt y%wtt) : well_typed_term_scope.

Definition lob : X.
Proof.
  refine ((fun (ℓ : □ L) => f (App ℓ (Conv (Quot ℓ))))
            (ttLambda_nd
               (Ast.nNamed "ℓ") (‘□’ ‘’ ‘L’)
               (‘‘f’’ ‘’ (((‘App’; _) ‘’ (Conv2' (Ast.tRel 0; _))) ‘’ (‘‘Conv’’ ‘’ (‘‘Quot’’ ‘’ (Ast.tRel 0; _)))))));
  match goal with
    | [ |- has_type _ (Ast.tRel _) _ ] => exact _
    | _ => idtac
  end.


  { apply (has_type_weaken nil). unfold L'.
    pose (cbv_beta_1 (cbv_beta_1 (‘L0’ ‘’ ⌜‘L0’ ⌝))).
    Timeout 5 simpl in t.
    Timeout 5 apply has_type_beta_1_type with (f := fun x => x).
    Timeout 5 apply has_type_beta_1_type with (f := fun x => x); simpl.
    Timeout 5 apply has_type_beta_1_type with (f := fun x => x); simpl.
    Timeout 5 apply has_type_beta_1_type with (f := fun x => x); simpl.
    apply
  { apply (has_type_weaken nil); exact _. }
  3:exact
  Focus 3.
  2:exact _.


  { repeat apply has_type_tApp_split.
    Timeout 5 eapply has_type_tApp.
  Focus 2.
  { eapply has_type_tApp.
    unfold Conv'.
    Timeout 5 apply has_type_tLambda.
    intro H'.
    exfalso; admit.
    admit. }
  Unfocus.
  exfalso; admit.
  Grab Existential Variables.
  admit.
Defined.

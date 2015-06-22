(* -*- coq-prog-args: ("-emacs" "-top" "quote_has_type") -*- *)
(* Runs on top of https://github.com/gmalecha/template-coq *)
Require Import Template.Template.


Require Import Coq.Strings.String.
Require Import Coq.Program.Program.
Require Import Coq.PArith.BinPos.
Local Open Scope string_scope.
Local Open Scope positive_scope.

Require Export quote_term.

Local Notation "x ‘→’ y" := (Ast.tProd Ast.nAnon x y) (at level 99, right associativity, y at level 200).

Fixpoint cbv_beta_1_helper (term : Ast.term) (orig_name : Ast.name) (orig_type : Ast.term) (idx : nat) (subst_in : Ast.term)
: Ast.term
  := let cbv_beta_1_helper_helper
         := (fix cbv_beta_1_helper_helper (xs : list Ast.term) : list Ast.term
             := match xs with
                  | nil => nil
                  | cons x' xs' => cons (cbv_beta_1_helper x' orig_name orig_type idx subst_in) (cbv_beta_1_helper_helper xs')
                end) in
     match term with
       | Ast.tRel idx'
         => if NPeano.Nat.eq_dec idx idx'
            then subst_in
            else term
       | Ast.tVar _ => term
       | Ast.tMeta _ => term
       | Ast.tEvar _ => term
       | Ast.tSort _ => term
       | Ast.tCast body cst typ
         => Ast.tCast (cbv_beta_1_helper body orig_name orig_type idx subst_in) cst (cbv_beta_1_helper typ orig_name orig_type idx subst_in)
       | Ast.tProd name typ body
         => Ast.tProd name (cbv_beta_1_helper typ orig_name orig_type idx subst_in) (cbv_beta_1_helper body orig_name orig_type (S idx) subst_in)
       | Ast.tLambda name typ body
         => Ast.tLambda name (cbv_beta_1_helper typ orig_name orig_type idx subst_in) (cbv_beta_1_helper body orig_name orig_type (S idx) subst_in)
       | Ast.tLetIn name typ bodyx body
         => Ast.tLetIn
              name
              (cbv_beta_1_helper typ orig_name orig_type idx subst_in)
              (cbv_beta_1_helper bodyx orig_name orig_type idx subst_in)
              (cbv_beta_1_helper body orig_name orig_type (S idx) subst_in)
       | Ast.tApp f' nil
         => cbv_beta_1_helper f' orig_name orig_type idx subst_in
       | Ast.tApp f' args
         => Ast.tApp (cbv_beta_1_helper f' orig_name orig_type idx subst_in)
                     (cbv_beta_1_helper_helper args)
       | Ast.tConst _ => term
       | Ast.tInd _ => term
       | Ast.tConstruct _ _ => term
       | Ast.tCase _ _ _ _
         => Ast.tApp (Ast.tLambda orig_name orig_type term) [subst_in]
       | Ast.tFix _ _
         => Ast.tApp (Ast.tLambda orig_name orig_type term) [subst_in]
       | Ast.tUnknown _ => term
     end.

Definition cbv_beta_1 (term : Ast.term) : Ast.term
  := match term with
       | Ast.tApp term' nil
         => term'
       | Ast.tApp (Ast.tLambda orig_name typ body) (subst_in::xs')
         => Ast.tApp (cbv_beta_1_helper body orig_name typ 0 subst_in) xs'
       | _ => term
     end.

Inductive has_type : Ast.term -> Ast.term -> Type :=
| has_type_tApp : forall A B f x,
                    has_type f (A ‘→’ B)
                    -> has_type x A
                    -> has_type (Ast.tApp f [x]) B
| has_type_tApp_nil : forall A x,
                        has_type x A
                        -> has_type (Ast.tApp x []) A
| has_type_tApp_split : forall T f x1 x2 xs,
                          has_type (Ast.tApp (Ast.tApp f [x1]) (cons x2 xs)) T
                          -> has_type (Ast.tApp f (cons x1 (cons x2 xs))) T
(* TODO?: Make sure that the beta-expanded term is well-typed? *)
| has_type_beta_1_type : forall t f T,
                           has_type t (f (cbv_beta_1 T))
                           -> has_type t (f T)
| has_type_eta_1_type : forall t f T,
                          has_type t (f T)
                          -> has_type t (f (cbv_beta_1 T))
(** TODO?: Make sure that the arguments to [sigT] are well-typed? *)
| has_type_existT
  : forall A P x y,
      (*let T := Ast.tApp ‘sigT’ [A; P] in
    has_type T (Ast.tSort U)
    -> has_type A (Ast.tSort U1
    -> has_type P (A ‘→’ Ast.tSort U2)*)
      has_type x A
      -> has_type y (Ast.tApp P [x])
      -> has_type (Ast.tApp ‘existT’ [A; P; x; y]) (Ast.tApp ‘sigT’ [A; P])
| has_type_qO : has_type qO nat'
| has_type_qS : has_type qS (nat' ‘→’ nat')
| has_type_qxI : has_type qxI (positive' ‘→’ positive')
| has_type_qxO : has_type qxO (positive' ‘→’ positive')
| has_type_qxH : has_type qxH positive'
| has_type_qtrue : has_type qtrue bool'
| has_type_qfalse : has_type qfalse bool'
| has_type_qAscii : has_type qAscii (bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ ascii')
| has_type_qEmptyString : has_type qEmptyString string'
| has_type_qString : has_type qString (ascii' ‘→’ string' ‘→’ string')
| has_type_qnil : forall T U, has_type T (Ast.tSort U)
                              -> has_type (Ast.tApp qnil [T]) (Ast.tApp list' [T])
| has_type_qcons : forall T,
                     has_type (Ast.tApp qcons [T]) (T ‘→’ Ast.tApp list' [T] ‘→’ Ast.tApp list' [T])
| has_type_term' : has_type term' (Ast.tSort Ast.sSet)
| has_type_def' : has_type def' (Ast.tSort Ast.sSet ‘→’ Ast.tSort Ast.sSet)
| has_type_qmkInd : has_type qmkInd (string' ‘→’ nat' ‘→’ inductive')
(*| has_type_qstProp : has_type (qtSort ‘’ qsProp) (Ast.tSort (Ast.sType 1))
| has_type_qstSet : has_type (qtSort ‘’ qsSet) (Ast.tSort (Ast.sType 1))
| has_type_qstType : forall p p',
                      denote_positive p = Some p'
                      -> has_type (qtSort ‘’ (Ast.tApp qsType [p]))
                                  (Ast.tSort (Ast.sType (1 + p')))*)
| has_type_qsProp : has_type qsProp sort'
| has_type_qsSet : has_type qsSet sort'
| has_type_qsType : has_type qsType (positive' ‘→’ sort')
| has_type_qnAnon : has_type qnAnon name'
| has_type_qnNamed : has_type qnNamed (ident' ‘→’ name')
| has_type_qVmCast : has_type qVmCast cast_kind'
| has_type_qNativeCast : has_type qNativeCast cast_kind'
| has_type_qCast : has_type qCast cast_kind'
| has_type_qRevertCast : has_type qRevertCast cast_kind'
| has_type_qtRel : has_type qtRel (nat' ‘→’ term')
| has_type_qtVar : has_type qtVar (ident' ‘→’ term')
| has_type_qtMeta : has_type qtMeta (nat' ‘→’ term')
| has_type_qtEvar : has_type qtEvar (nat' ‘→’ term')
| has_type_qtSort : has_type qtSort (sort' ‘→’ term')
| has_type_qtCast : has_type qtCast (term' ‘→’ cast_kind' ‘→’ term' ‘→’ term')
| has_type_qtProd : has_type qtProd (name' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtLambda : has_type qtLambda (name' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtLetIn : has_type qtLetIn (name' ‘→’ term' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtApp : has_type qtApp (term' ‘→’ Ast.tApp list' [term'] ‘→’ term')
| has_type_qtConst : has_type qtConst (string' ‘→’ term')
| has_type_qtInd : has_type qtInd (inductive' ‘→’ term')
| has_type_qtConstruct : has_type qtConstruct (inductive' ‘→’ nat' ‘→’ term')
| has_type_qtCase : has_type qtCase (nat' ‘→’ term' ‘→’ term' ‘→’ Ast.tApp list' [term'] ‘→’ term')
| has_type_qtFix : has_type qtFix (mfixpoint' term' ‘→’ nat' ‘→’ term')
| has_type_qtUnknown : has_type qtUnknown (string' ‘→’ term')
| has_type_qmkdef : forall T, has_type qmkdef (name' ‘→’ T ‘→’ T ‘→’ nat' ‘→’ Ast.tApp def' [T]).
(* XXX TODO: How should this be done? *)
Axiom has_type_tLambda
: forall name name' A B body,
    (has_type (Ast.tRel 0) A -> has_type body B)
    -> has_type (Ast.tLambda name A body) (Ast.tProd name' A B).

Existing Class has_type.
Existing Instances
         has_type_tApp has_type_tApp_nil has_type_tApp_split
         has_type_qO has_type_qS
         has_type_qtRel has_type_qtVar has_type_qtMeta has_type_qtEvar has_type_qtSort has_type_qtCast has_type_qtProd has_type_qtLambda has_type_qtLetIn has_type_qtApp has_type_qtConst has_type_qtInd has_type_qtConstruct has_type_qtCase has_type_qtFix has_type_qtUnknown
         has_type_qtrue has_type_qfalse
         has_type_qAscii
         has_type_qEmptyString has_type_qString
         has_type_qxI has_type_qxO has_type_qxH
         has_type_qnil has_type_qcons
         has_type_qsProp has_type_qsSet has_type_qsType
         has_type_qnAnon has_type_qnNamed
         has_type_qVmCast has_type_qNativeCast has_type_qCast has_type_qRevertCast
         has_type_qmkInd has_type_qmkdef
         has_type_term' has_type_def'.

Instance quote_nat_has_type (n : nat)
: has_type (quote n) nat'.
Proof. induction n; simpl; exact _. Defined.

Instance quote_bool_has_type (x : bool)
: has_type (quote x) bool'.
Proof. destruct x; simpl; exact _. Defined.

Instance quote_ascii_has_type (x : Ascii.ascii)
: has_type (quote x) ascii'.
Proof. destruct x; simpl; try exact _. Defined.

Instance quote_string_has_type (x : string)
: has_type (quote x) string'.
Proof. induction x; simpl; try exact _. Defined.

Instance quote_ident_has_type (x : Ast.ident)
: has_type (quote x) string'
  := quote_string_has_type x.

Instance quote_positive_has_type (x : positive)
: has_type (quote x) positive'.
Proof. induction x; simpl; try exact _. Defined.

Instance quote_list_has_type {T T' U}
         `{Quotable T, has_type T' (Ast.tSort U), forall a : T, has_type (quote a) T'}
         (x : list T)
: has_type (quote_list T' x) (Ast.tApp list' [T']).
Proof. unfold quote; induction x; simpl; try exact _. Defined.

Instance quote_inductive_has_type (x : Ast.inductive)
: has_type (quote x) inductive'.
Proof. unfold quote; destruct x; simpl; try exact _. Defined.

Instance quote_sort_has_type (x : Ast.sort)
: has_type (quote x) sort'.
Proof. unfold quote; destruct x; try exact _. Defined.

Instance quote_name_has_type (x : Ast.name)
: has_type (quote x) name'.
Proof. unfold quote; destruct x; simpl; try exact _. Defined.

Instance quote_cast_kind_has_type (x : Ast.cast_kind)
: has_type (quote x) cast_kind'.
Proof. unfold quote; destruct x; simpl; try exact _. Defined.

Local Arguments quote_term_step : simpl never.

Fixpoint quote_term_has_type (x : Ast.term)
: has_type (quote x) term'.
Proof.
  destruct x; try (unfold quote; simpl; exact _).
  { unfold quote, term_quotable; simpl.
    unfold quote_term_step; simpl.
    repeat apply has_type_tApp_split.
    eapply has_type_tApp; try exact _; [].
    let ls := match goal with ls : list Ast.term |- _ => constr:ls end in
    induction ls; try exact _. }
  { unfold quote, term_quotable; simpl.
    unfold quote_term_step; simpl.
    repeat apply has_type_tApp_split.
    eapply has_type_tApp; try exact _; [].
    let ls := match goal with ls : list Ast.term |- _ => constr:ls end in
    induction ls; try exact _. }
  { unfold quote, term_quotable; simpl; unfold quote_term_step; simpl.
    destruct m as [ | [ ] ]; simpl; try exact _; [].
    repeat apply has_type_tApp_split.
    eapply has_type_tApp; try exact _; [].
    repeat apply has_type_tApp_split.
    eapply has_type_tApp; try exact _; [].
    repeat apply has_type_tApp_split.
    eapply has_type_tApp; try exact _; [].
    clear -quote_term_has_type.
    let ls := match goal with ls : list (Ast.def Ast.term) |- _ => constr:ls end in
    induction ls as [ | [ ] ]; simpl; try exact _. }
Defined.

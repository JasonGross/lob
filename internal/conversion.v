(* Runs on top of https://github.com/gmalecha/template-coq *)
Require Import Template.Template.


Require Import Coq.Strings.String.
Require Import Coq.Program.Program.
Require Import Coq.PArith.BinPos.
Local Open Scope string_scope.
Local Open Scope positive_scope.
Local Open Scope list_scope.

Definition Context := list Ast.term.
Delimit Scope context_scope with ctx.
Bind Scope context_scope with Context.
Notation ε := (@nil Ast.term : Context).
Definition context_extend (Γ : Context) (x : Ast.term) := cons x Γ.
Definition context_app (Γ Γ' : Context) := List.app Γ' Γ.
Notation "Γ ▻ x" := (context_extend Γ x) (at level 55, right associativity).
Notation "Γ ▻▻ Γ'" := (context_app Γ Γ') (at level 60, right associativity).
Print Ast.term.

Definition subst_n_name_def
           (subst_n_name : Ast.term -> Ast.term)
           (in_term : Ast.def Ast.term)
: Ast.def Ast.term
  := match in_term with
       | {| Ast.dname := dname ; Ast.dtype := dtype ; Ast.dbody := dbody ; Ast.rarg := rarg |}
         => {| Ast.dname := dname;
               Ast.dtype := subst_n_name dtype;
               Ast.dbody := subst_n_name dbody;
               Ast.rarg := rarg |}
     end.

Fixpoint subst_n_name (in_term : Ast.term) (subst_term : Ast.term) (var_n : nat) (name : Ast.name) {struct in_term} : Ast.term
  := match in_term with
       | Ast.tRel v => match Compare_dec.lt_eq_lt_dec v var_n with
                         | inleft (left _) => in_term
                         | inleft (right _) => subst_term
                         | inright _ => Ast.tRel (pred v)
                       end
       | Ast.tVar name0 => match name with
                             | Ast.nNamed name1
                               => if String.string_dec name0 name1
                                  then subst_term
                                  else in_term
                             | Ast.nAnon => in_term
                           end
       | Ast.tMeta _ => in_term
       | Ast.tEvar _ => in_term
       | Ast.tSort _ => in_term
       | Ast.tCast term0' kind term1'
         => Ast.tCast (subst_n_name term0' subst_term var_n name)
                      kind
                      (subst_n_name term1' subst_term var_n name)
       | Ast.tProd name' term0' term1'
         => let new_name := match name, name' with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then Ast.nAnon
                                   else name
                              | _, _ => name
                            end in
            Ast.tProd name'
                      (subst_n_name term0' subst_term (S var_n) new_name)
                      (subst_n_name term1' subst_term (S var_n) new_name)
       | Ast.tLambda name' term0' term1'
         => let new_name := match name, name' with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then Ast.nAnon
                                   else name
                              | _, _ => name
                            end in
            Ast.tLambda name'
                        (subst_n_name term0' subst_term (S var_n) new_name)
                        (subst_n_name term1' subst_term (S var_n) new_name)
       | Ast.tLetIn name' term0' term1' term2'
         => let new_name := match name, name' with
                              | Ast.nNamed n0, Ast.nNamed n1
                                => if String.string_dec n0 n1
                                   then Ast.nAnon
                                   else name
                              | _, _ => name
                            end in
            Ast.tLetIn name'
                       (subst_n_name term0' subst_term (S var_n) new_name)
                       (subst_n_name term1' subst_term (S var_n) new_name)
                       (subst_n_name term2' subst_term (S var_n) new_name)
       | Ast.tApp f args
         => Ast.tApp (subst_n_name f subst_term var_n name)
                     (List.map (fun term' => subst_n_name term' subst_term var_n name) args)
       | Ast.tConst _ => in_term
       | Ast.tInd _ => in_term
       | Ast.tConstruct _ _ => in_term
       | Ast.tCase n term0' term1' branches
         => Ast.tCase n
                      (subst_n_name term0' subst_term var_n name)
                      (subst_n_name term1' subst_term var_n name)
                      (List.map (fun term' => subst_n_name term' subst_term var_n name) branches)
       | Ast.tFix term0' n
         => Ast.tFix (List.map (subst_n_name_def (fun term' => subst_n_name term' subst_term var_n name)) term0')
                     n
       | Ast.tUnknown _ => in_term
     end.

Fixpoint context_subst_n (in_context : Context) (subst_term : Ast.term) (var_n : nat) (name : Ast.name) {struct in_context} : Context
  := match in_context with
       | nil => nil
       | cons T Ts => context_extend
                        (context_subst_n Ts subst_term (S var_n) name)
                        (subst_n_name T subst_term var_n name)
     end.

(** Quoting the rules from the appendix of the HoTT book *)

Print Ast.term.

Inductive convertible : Context -> Ast.term -> Ast.term -> Ast.term -> Type :=
with has_type : Context -> Ast.term -> Ast.term -> Type :=
(**
<<
(x₁ : A₁, ..., xₙ : Aₙ) ctx
-------------------------------- Vble
x₁ : A₁, ..., xₙ : Aₙ ⊢ xᵢ : Aᵢ
>> *)
| has_type_tRel_0 : forall T Γ univ,
                      has_type Γ T (Ast.tSort univ)
                      -> has_type (Γ ▻ T) (Ast.tRel 0) T
| has_type_tRel_S : forall T T' Γ n,
                      has_type Γ (Ast.tRel n) T
                      -> has_type (Γ ▻ T') (Ast.tRel (S n)) T.

Class Context_inf := mkContext : Context.
Definition Let_Context_inf_In (ctx : Context_inf) {T} (f : Context_inf -> T)
  := f ctx.

(**
<<
Γ ⊢ a : A     Γ, x : A, Δ ⊢ b : B
--------------------------------- Subst₁
   Γ, Δ[a/x] ⊢ b[a/x] : B[a/x]
>>

HoTT book says provable by induction.
*)
Lemma subst_1 {Γ a A Δ B b}
: has_type Γ a A -> has_type (Γ ▻ A ▻▻ Δ) b B
  -> has_type (Γ ▻▻ context_subst_n Δ a (List.length Γ) Ast.nAnon)%list
              (subst_n_name b a (List.length Γ) Ast.nAnon)
              (subst_n_name B a (List.length Γ) Ast.nAnon).
Proof.
  intros ht1 ht2.
Admitted.

(**


Local Opaque Compare_dec.lt_eq_lt_dec.
    simpl in *.
  simpl.
  induction ht2
Γ
Inductive has_type :  Context -> Ast.term -> Ast.term -> Type :=
| has_type_weaken : forall Γ Γ' T t,
                      has_type Γ t T
                      -> has_type (Γ ++ Γ') t T
| has_type_tRel_0 : forall T Γ,
                      has_type (Γ ▻ T) (Ast.tRel 0) T
| has_type_tRel_S : forall T T' Γ n,
                      has_type Γ (Ast.tRel n) T
                      -> has_type (Γ ▻ T') (Ast.tRel (S n)) T
| has_type_tApp : forall Γ A B f x,
                    has_type Γ f (A ‘→’ B)
                    -> has_type Γ x A
                    -> has_type Γ (Ast.tApp f [x]) B
| has_type_tApp_nil : forall Γ A x,
                        has_type Γ x A
                        -> has_type Γ (Ast.tApp x []) A
| has_type_tApp_split : forall Γ T f x1 x2 xs,
                          has_type Γ (Ast.tApp (Ast.tApp f [x1]) (cons x2 xs)) T
                          -> has_type Γ (Ast.tApp f (cons x1 (cons x2 xs))) T
(* TODO?: Make sure that the beta-expanded term is well-typed? *)
| has_type_beta_1_type : forall Γ t f T,
                           has_type Γ t (f (cbv_beta_1 T))
                           -> has_type Γ t (f T)
| has_type_eta_1_type : forall Γ t f T,
                          has_type Γ t (f T)
                          -> has_type Γ t (f (cbv_beta_1 T))
| has_type_beta_1_term : forall Γ f t T,
                           has_type Γ (f (cbv_beta_1 t)) T
                           -> has_type Γ (f t) T
| has_type_eta_1_term : forall Γ t f T,
                          has_type Γ (f t) T
                          -> has_type Γ (f (cbv_beta_1 t)) T
(** TODO?: Make sure that the arguments to [sigT] are well-typed? *)
| has_type_existT
  : forall Γ A P x y,
      (*let T := Ast.tApp ‘sigT’ [A; P] in
    has_type T (Ast.tSort U)
    -> has_type A (Ast.tSort U1
    -> has_type P (A ‘→’ Ast.tSort U2)*)
      has_type Γ x A
      -> has_type Γ y (Ast.tApp P [x])
      -> has_type Γ (Ast.tApp ‘existT’ [A; P; x; y]) (Ast.tApp ‘sigT’ [A; P])
| has_type_qO : forall Γ, has_type Γ qO nat'
| has_type_qS : forall Γ, has_type Γ qS (nat' ‘→’ nat')
| has_type_qxI : forall Γ, has_type Γ qxI (positive' ‘→’ positive')
| has_type_qxO : forall Γ, has_type Γ qxO (positive' ‘→’ positive')
| has_type_qxH : forall Γ, has_type Γ qxH positive'
| has_type_qtrue : forall Γ, has_type Γ qtrue bool'
| has_type_qfalse : forall Γ, has_type Γ qfalse bool'
| has_type_qAscii : forall Γ, has_type Γ qAscii (bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ ascii')
| has_type_qEmptyString : forall Γ, has_type Γ qEmptyString string'
| has_type_qString : forall Γ, has_type Γ qString (ascii' ‘→’ string' ‘→’ string')
| has_type_qnil : forall Γ T U, has_type Γ T (Ast.tSort U)
                              -> has_type Γ (Ast.tApp qnil [T]) (Ast.tApp list' [T])
| has_type_qcons : forall Γ T,
                     has_type Γ (Ast.tApp qcons [T]) (T ‘→’ Ast.tApp list' [T] ‘→’ Ast.tApp list' [T])
| has_type_term' : forall Γ, has_type Γ term' (Ast.tSort Ast.sSet)
| has_type_def' : forall Γ, has_type Γ def' (Ast.tSort Ast.sSet ‘→’ Ast.tSort Ast.sSet)
| has_type_qmkInd : forall Γ, has_type Γ qmkInd (string' ‘→’ nat' ‘→’ inductive')
(*| has_type_qstProp : has_type Γ (qtSort ‘’ qsProp) (Ast.tSort (Ast.sType 1))
| has_type_qstSet : has_type Γ (qtSort ‘’ qsSet) (Ast.tSort (Ast.sType 1))
| has_type_qstType : forall p p',
                      denote_positive p = Some p'
                      -> has_type Γ (qtSort ‘’ (Ast.tApp qsType [p]))
                                  (Ast.tSort (Ast.sType (1 + p')))*)
| has_type_qsProp : forall Γ, has_type Γ qsProp sort'
| has_type_qsSet : forall Γ, has_type Γ qsSet sort'
| has_type_qsType : forall Γ, has_type Γ qsType (positive' ‘→’ sort')
| has_type_qnAnon : forall Γ, has_type Γ qnAnon name'
| has_type_qnNamed : forall Γ, has_type Γ qnNamed (ident' ‘→’ name')
| has_type_qVmCast : forall Γ, has_type Γ qVmCast cast_kind'
| has_type_qNativeCast : forall Γ, has_type Γ qNativeCast cast_kind'
| has_type_qCast : forall Γ, has_type Γ qCast cast_kind'
| has_type_qRevertCast : forall Γ, has_type Γ qRevertCast cast_kind'
| has_type_qtRel : forall Γ, has_type Γ qtRel (nat' ‘→’ term')
| has_type_qtVar : forall Γ, has_type Γ qtVar (ident' ‘→’ term')
| has_type_qtMeta : forall Γ, has_type Γ qtMeta (nat' ‘→’ term')
| has_type_qtEvar : forall Γ, has_type Γ qtEvar (nat' ‘→’ term')
| has_type_qtSort : forall Γ, has_type Γ qtSort (sort' ‘→’ term')
| has_type_qtCast : forall Γ, has_type Γ qtCast (term' ‘→’ cast_kind' ‘→’ term' ‘→’ term')
| has_type_qtProd : forall Γ, has_type Γ qtProd (name' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtLambda : forall Γ, has_type Γ qtLambda (name' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtLetIn : forall Γ, has_type Γ qtLetIn (name' ‘→’ term' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtApp : forall Γ, has_type Γ qtApp (term' ‘→’ Ast.tApp list' [term'] ‘→’ term')
| has_type_qtConst : forall Γ, has_type Γ qtConst (string' ‘→’ term')
| has_type_qtInd : forall Γ, has_type Γ qtInd (inductive' ‘→’ term')
| has_type_qtConstruct : forall Γ, has_type Γ qtConstruct (inductive' ‘→’ nat' ‘→’ term')
| has_type_qtCase : forall Γ, has_type Γ qtCase (nat' ‘→’ term' ‘→’ term' ‘→’ Ast.tApp list' [term'] ‘→’ term')
| has_type_qtFix : forall Γ, has_type Γ qtFix (mfixpoint' term' ‘→’ nat' ‘→’ term')
| has_type_qtUnknown : forall Γ, has_type Γ qtUnknown (string' ‘→’ term')
| has_type_qmkdef : forall Γ T, has_type Γ qmkdef (name' ‘→’ T ‘→’ T ‘→’ nat' ‘→’ Ast.tApp def' [T])
| has_type_tLambda


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

Fixpoint cbv_beta_1 (term : Ast.term) : Ast.term
  := let cbv_beta_1_helper'
         := (fix cbv_beta_1_helper' (xs : list Ast.term) : list Ast.term
             := match xs with
                  | nil => nil
                  | cons x' xs' => cons (cbv_beta_1 x') (cbv_beta_1_helper' xs')
                end) in
     match term with
       | Ast.tApp term' nil
         => term'
       | Ast.tApp (Ast.tLambda orig_name typ body) (subst_in::xs')
         => Ast.tApp (cbv_beta_1_helper body orig_name typ 0 subst_in) xs'
       | Ast.tApp term' ls
         => Ast.tApp (cbv_beta_1 term') (cbv_beta_1_helper' ls)
       | Ast.tCast body cst typ
         => Ast.tCast (cbv_beta_1 body) cst (cbv_beta_1 typ)
       | Ast.tProd name typ body
         => Ast.tProd name (cbv_beta_1 typ) (cbv_beta_1 body)
       | Ast.tLambda name typ body
         => Ast.tLambda name (cbv_beta_1 typ) (cbv_beta_1 body)
       | Ast.tLetIn name typ bodyx body
         => Ast.tLetIn name (cbv_beta_1 typ) (cbv_beta_1 bodyx) (cbv_beta_1 body)
       | Ast.tConst _ => term
       | Ast.tInd _ => term
       | Ast.tConstruct _ _ => term
       | Ast.tCase _ _ _ _ => term
       | Ast.tFix _ _ => term
       | Ast.tUnknown _ => term
       | Ast.tRel _ | Ast.tVar _ | Ast.tMeta _ | Ast.tEvar _ | Ast.tSort _ => term
     end.

Inductive has_type :  Context -> Ast.term -> Ast.term -> Type :=
| has_type_weaken : forall Γ Γ' T t,
                      has_type Γ t T
                      -> has_type (Γ ++ Γ') t T
| has_type_tRel_0 : forall T Γ,
                      has_type (Γ ▻ T) (Ast.tRel 0) T
| has_type_tRel_S : forall T T' Γ n,
                      has_type Γ (Ast.tRel n) T
                      -> has_type (Γ ▻ T') (Ast.tRel (S n)) T
| has_type_tApp : forall Γ A B f x,
                    has_type Γ f (A ‘→’ B)
                    -> has_type Γ x A
                    -> has_type Γ (Ast.tApp f [x]) B
| has_type_tApp_nil : forall Γ A x,
                        has_type Γ x A
                        -> has_type Γ (Ast.tApp x []) A
| has_type_tApp_split : forall Γ T f x1 x2 xs,
                          has_type Γ (Ast.tApp (Ast.tApp f [x1]) (cons x2 xs)) T
                          -> has_type Γ (Ast.tApp f (cons x1 (cons x2 xs))) T
(* TODO?: Make sure that the beta-expanded term is well-typed? *)
| has_type_beta_1_type : forall Γ t f T,
                           has_type Γ t (f (cbv_beta_1 T))
                           -> has_type Γ t (f T)
| has_type_eta_1_type : forall Γ t f T,
                          has_type Γ t (f T)
                          -> has_type Γ t (f (cbv_beta_1 T))
| has_type_beta_1_term : forall Γ f t T,
                           has_type Γ (f (cbv_beta_1 t)) T
                           -> has_type Γ (f t) T
| has_type_eta_1_term : forall Γ t f T,
                          has_type Γ (f t) T
                          -> has_type Γ (f (cbv_beta_1 t)) T
(** TODO?: Make sure that the arguments to [sigT] are well-typed? *)
| has_type_existT
  : forall Γ A P x y,
      (*let T := Ast.tApp ‘sigT’ [A; P] in
    has_type T (Ast.tSort U)
    -> has_type A (Ast.tSort U1
    -> has_type P (A ‘→’ Ast.tSort U2)*)
      has_type Γ x A
      -> has_type Γ y (Ast.tApp P [x])
      -> has_type Γ (Ast.tApp ‘existT’ [A; P; x; y]) (Ast.tApp ‘sigT’ [A; P])
| has_type_qO : forall Γ, has_type Γ qO nat'
| has_type_qS : forall Γ, has_type Γ qS (nat' ‘→’ nat')
| has_type_qxI : forall Γ, has_type Γ qxI (positive' ‘→’ positive')
| has_type_qxO : forall Γ, has_type Γ qxO (positive' ‘→’ positive')
| has_type_qxH : forall Γ, has_type Γ qxH positive'
| has_type_qtrue : forall Γ, has_type Γ qtrue bool'
| has_type_qfalse : forall Γ, has_type Γ qfalse bool'
| has_type_qAscii : forall Γ, has_type Γ qAscii (bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ bool' ‘→’ ascii')
| has_type_qEmptyString : forall Γ, has_type Γ qEmptyString string'
| has_type_qString : forall Γ, has_type Γ qString (ascii' ‘→’ string' ‘→’ string')
| has_type_qnil : forall Γ T U, has_type Γ T (Ast.tSort U)
                              -> has_type Γ (Ast.tApp qnil [T]) (Ast.tApp list' [T])
| has_type_qcons : forall Γ T,
                     has_type Γ (Ast.tApp qcons [T]) (T ‘→’ Ast.tApp list' [T] ‘→’ Ast.tApp list' [T])
| has_type_term' : forall Γ, has_type Γ term' (Ast.tSort Ast.sSet)
| has_type_def' : forall Γ, has_type Γ def' (Ast.tSort Ast.sSet ‘→’ Ast.tSort Ast.sSet)
| has_type_qmkInd : forall Γ, has_type Γ qmkInd (string' ‘→’ nat' ‘→’ inductive')
(*| has_type_qstProp : has_type Γ (qtSort ‘’ qsProp) (Ast.tSort (Ast.sType 1))
| has_type_qstSet : has_type Γ (qtSort ‘’ qsSet) (Ast.tSort (Ast.sType 1))
| has_type_qstType : forall p p',
                      denote_positive p = Some p'
                      -> has_type Γ (qtSort ‘’ (Ast.tApp qsType [p]))
                                  (Ast.tSort (Ast.sType (1 + p')))*)
| has_type_qsProp : forall Γ, has_type Γ qsProp sort'
| has_type_qsSet : forall Γ, has_type Γ qsSet sort'
| has_type_qsType : forall Γ, has_type Γ qsType (positive' ‘→’ sort')
| has_type_qnAnon : forall Γ, has_type Γ qnAnon name'
| has_type_qnNamed : forall Γ, has_type Γ qnNamed (ident' ‘→’ name')
| has_type_qVmCast : forall Γ, has_type Γ qVmCast cast_kind'
| has_type_qNativeCast : forall Γ, has_type Γ qNativeCast cast_kind'
| has_type_qCast : forall Γ, has_type Γ qCast cast_kind'
| has_type_qRevertCast : forall Γ, has_type Γ qRevertCast cast_kind'
| has_type_qtRel : forall Γ, has_type Γ qtRel (nat' ‘→’ term')
| has_type_qtVar : forall Γ, has_type Γ qtVar (ident' ‘→’ term')
| has_type_qtMeta : forall Γ, has_type Γ qtMeta (nat' ‘→’ term')
| has_type_qtEvar : forall Γ, has_type Γ qtEvar (nat' ‘→’ term')
| has_type_qtSort : forall Γ, has_type Γ qtSort (sort' ‘→’ term')
| has_type_qtCast : forall Γ, has_type Γ qtCast (term' ‘→’ cast_kind' ‘→’ term' ‘→’ term')
| has_type_qtProd : forall Γ, has_type Γ qtProd (name' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtLambda : forall Γ, has_type Γ qtLambda (name' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtLetIn : forall Γ, has_type Γ qtLetIn (name' ‘→’ term' ‘→’ term' ‘→’ term' ‘→’ term')
| has_type_qtApp : forall Γ, has_type Γ qtApp (term' ‘→’ Ast.tApp list' [term'] ‘→’ term')
| has_type_qtConst : forall Γ, has_type Γ qtConst (string' ‘→’ term')
| has_type_qtInd : forall Γ, has_type Γ qtInd (inductive' ‘→’ term')
| has_type_qtConstruct : forall Γ, has_type Γ qtConstruct (inductive' ‘→’ nat' ‘→’ term')
| has_type_qtCase : forall Γ, has_type Γ qtCase (nat' ‘→’ term' ‘→’ term' ‘→’ Ast.tApp list' [term'] ‘→’ term')
| has_type_qtFix : forall Γ, has_type Γ qtFix (mfixpoint' term' ‘→’ nat' ‘→’ term')
| has_type_qtUnknown : forall Γ, has_type Γ qtUnknown (string' ‘→’ term')
| has_type_qmkdef : forall Γ T, has_type Γ qmkdef (name' ‘→’ T ‘→’ T ‘→’ nat' ‘→’ Ast.tApp def' [T])
| has_type_tLambda
  : forall Γ name name' A B body,
      has_type (A::Γ) body B
      -> has_type Γ (Ast.tLambda name A body) (Ast.tProd name' A B).

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
         has_type_term' has_type_def'
         has_type_tRel_S has_type_tRel_0.

Instance quote_nat_has_type {Γ} (n : nat)
: has_type Γ (quote n) nat'.
Proof. induction n; simpl; exact _. Defined.

Instance quote_bool_has_type {Γ} (x : bool)
: has_type Γ (quote x) bool'.
Proof. destruct x; simpl; exact _. Defined.

Instance quote_ascii_has_type {Γ} (x : Ascii.ascii)
: has_type Γ (quote x) ascii'.
Proof. destruct x; simpl; try exact _. Defined.

Instance quote_string_has_type {Γ} (x : string)
: has_type Γ (quote x) string'.
Proof. induction x; simpl; try exact _. Defined.

Instance quote_ident_has_type {Γ} (x : Ast.ident)
: has_type Γ (quote x) string'
  := quote_string_has_type x.

Instance quote_positive_has_type {Γ} (x : positive)
: has_type Γ (quote x) positive'.
Proof. induction x; simpl; try exact _. Defined.

Instance quote_list_has_type {Γ T T' U}
         `{Quotable T, has_type Γ T' (Ast.tSort U), forall a : T, has_type Γ (quote a) T'}
         (x : list T)
: has_type Γ (quote_list T' x) (Ast.tApp list' [T']).
Proof. unfold quote; induction x; simpl; try exact _. Defined.

Instance quote_inductive_has_type {Γ} (x : Ast.inductive)
: has_type Γ (quote x) inductive'.
Proof. unfold quote; destruct x; simpl; try exact _. Defined.

Instance quote_sort_has_type {Γ} (x : Ast.sort)
: has_type Γ (quote x) sort'.
Proof. unfold quote; destruct x; try exact _. Defined.

Instance quote_name_has_type {Γ} (x : Ast.name)
: has_type Γ (quote x) name'.
Proof. unfold quote; destruct x; simpl; try exact _. Defined.

Instance quote_cast_kind_has_type {Γ} (x : Ast.cast_kind)
: has_type Γ (quote x) cast_kind'.
Proof. unfold quote; destruct x; simpl; try exact _. Defined.

Local Arguments quote_term_step : simpl never.

Fixpoint quote_term_has_type {Γ} (x : Ast.term)
: has_type Γ (quote x) term'.
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

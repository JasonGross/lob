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

Definition Preterm := Ast.term.
Quote Definition Preterm' := Ast.term.
Definition Context := Ast.program.

Notation "‘Preterm’" := Preterm'.

Fixpoint contextLookupConstr (name : string) (ctx : Context)
: option Ast.term
  := match ctx with
       | Ast.PConstr name' term ctx'
         => if string_dec name name'
            then Some term
            else contextLookupConstr name ctx'
       | Ast.PType _ _ ctx'
         => contextLookupConstr name ctx'
       | Ast.PAxiom _ ctx'
         => contextLookupConstr name ctx'
       | Ast.PIn _
         => None
     end.

Fixpoint contextLookupType (name : string) (ctx : Context)
: option (list (Ast.ident * Ast.inductive_body))
  := match ctx with
       | Ast.PConstr _ _ ctx'
         => contextLookupType name ctx'
       | Ast.PType name' body ctx'
         => if string_dec name name'
            then Some body
            else contextLookupType name ctx'
       | Ast.PAxiom _ ctx'
         => contextLookupType name ctx'
       | Ast.PIn _
         => None
     end.

Fixpoint contextLookupAxiom (name : string) (ctx : Context)
: option unit
  := match ctx with
       | Ast.PConstr _ _ ctx'
         => contextLookupAxiom name ctx'
       | Ast.PType _ _ ctx'
         => contextLookupAxiom name ctx'
       | Ast.PAxiom name' ctx'
         => if string_dec name name'
            then Some tt
            else contextLookupAxiom name ctx'
       | Ast.PIn _
         => None
     end.

Fixpoint contextGetPIn (ctx : Context)
: Ast.term
  := match ctx with
       | Ast.PConstr _ _ ctx'
         => contextGetPIn ctx'
       | Ast.PType _ _ ctx'
         => contextGetPIn ctx'
       | Ast.PAxiom _ ctx'
         => contextGetPIn ctx'
       | Ast.PIn body
         => body
     end.

Notation "x ‘→’ y" := (Ast.tProd Ast.nAnon x y) (at level 99, right associativity, y at level 200).
Notation "x ‘’ y" := (Ast.tApp x (cons y nil )) (at level 15, left associativity).

Axiom X : Type.
Quote Definition qX := X.
Check qX : Preterm.
Notation "‘X’" := qX.

Definition box (T : Preterm) : Type
  := { t : Preterm & has_type t T }.

Notation "□" := box.

Axiom f : □ ‘X’ -> X.
Quote Definition qf := f.
Check qf : Preterm.
Notation "‘f’" := qf.

(*Quote Recursively Definition Γ :=
  (let dummy_sigma := sigT in
   let dummy_X := X in
   has_type : Preterm -> Preterm -> Type).*)

Notation get_unfold_one qrterm
  := (let x := match contextGetPIn qrterm as p
                     return match p with
                              | Ast.tConst _ => option Ast.term
                              | _ => unit
                            end
               with
                 | Ast.tConst name
                   => contextLookupConstr name qrterm
                 | _ => tt
               end in
      match x as x' return match x' with
                             | Some _ => _
                             | None => unit
                           end
      with
        | Some k => k
        | None => tt
      end).

Definition box' : Preterm.
Proof.
  let term := (eval cbv delta in box) in
  quote_term term (fun x => exact x).
Defined.
Print box'.
_unfolded := Eval cbv delta in box.
Quote Recursively Definition box'' := box_unfolded.
Definition box' := Eval simpl in get_unfold_one box''.

Notation "‘□’" := box'.

Fixpoint quote_nat (n : nat) : Preterm
  := match n with
       | O => qO
       | S n' => Ast.tApp qS [quote_nat n']
     end.

Instance nat_quotable : Quotable nat := quote_nat.
Instance quote_nat_has_type (n : nat)
: has_type (quote n) nat'.
Proof. induction n; simpl; exact _. Defined.


Definition quote_bool (b : bool) : Preterm
  := if b then qtrue else qfalse.

Instance bool_quotable : Quotable bool := quote_bool.

Instance quote_bool_has_type (x : bool)
: has_type (quote x) bool'.
Proof. destruct x; simpl; exact _. Defined.


Definition quote_ascii (x : Ascii.ascii) : Preterm
  := match x with
          | Ascii.Ascii x0 x1 x2 x3 x4 x5 x6 x7 => Ast.tApp qAscii [quote x0; quote x1; quote x2; quote x3; quote x4; quote x5; quote x6; quote x7]
     end.

Instance ascii_quotable : Quotable Ascii.ascii := quote_ascii.

Instance quote_ascii_has_type (x : Ascii.ascii)
: has_type (quote x) ascii'.
Proof. destruct x; simpl; try exact _. Defined.


Fixpoint quote_string (s : string) : Preterm
  := match s with
       | EmptyString => qEmptyString
       | String a s' => Ast.tApp qString [quote_ascii a; quote_string s']
     end.

Instance string_quotable : Quotable string := quote_string.

Instance quote_string_has_type (x : string)
: has_type (quote x) string'.
Proof. induction x; simpl; try exact _. Defined.


Definition quote_ident : Ast.ident -> Preterm
  := quote_string.

Instance ident_quotable : Quotable Ast.ident := quote_ident.

Instance quote_ident_has_type (x : Ast.ident)
: has_type (quote x) string'
  := quote_string_has_type x.

Fixpoint quote_positive (x : positive) : Preterm
  := match x with
       | xI p => Ast.tApp qxI [quote_positive p]
       | xO p => Ast.tApp qxO [quote_positive p]
       | xH => qxH
     end.

Instance positive_quotable : Quotable positive := quote_positive.

Instance quote_positive_has_type (x : positive)
: has_type (quote x) positive'.
Proof. induction x; simpl; try exact _. Defined.

Lemma denote_quote_positive (p : positive)
: denote_positive (quote_positive p) = Some p.
Proof.
  induction p; simpl; try (rewrite IHp; clear IHp); simpl; reflexivity.
Defined.

Instance universe_quotable : Quotable Ast.universe := quote_positive.


Fixpoint quote_list {T} `{Quotable T} T' (ls : list T) : Preterm
  := match ls with
       | nil => Ast.tApp qnil [T']
       | cons x xs => Ast.tApp qcons [T'; quote x; quote_list T' xs]
     end.

Instance list_quotable {T} `{Quotable T} T' : Quotable (list T) := quote_list T'.

Instance quote_list_has_type {T T' U}
         `{Quotable T, has_type T' (Ast.tSort U), forall a : T, has_type (quote a) T'}
         (x : list T)
: has_type (quote_list T' x) (list' ‘’ T').
Proof. unfold quote; induction x; simpl; try exact _. Defined.


Definition quote_inductive (x : Ast.inductive) : Preterm
  := match x with
       | Ast.mkInd x0 x1 => Ast.tApp qmkInd [quote x0; quote x1]
     end.

Instance inductive_quotable : Quotable Ast.inductive := quote_inductive.

Instance quote_inductive_has_type (x : Ast.inductive)
: has_type (quote x) inductive'.
Proof. unfold quote; destruct x; simpl; try exact _. Defined.


Definition quote_sort (x : Ast.sort) : Preterm
  := match x with
          | Ast.sProp  => qsProp
          | Ast.sSet  => qsSet
          | Ast.sType x0 => Ast.tApp qsType [quote x0]
     end.

Instance sort_quotable : Quotable Ast.sort := quote_sort.

Definition sort_next_level (x : Ast.sort) : Ast.universe
  := match x with
       | Ast.sType n => 1 + n
       | Ast.sProp | Ast.sSet => 1
     end.

(*Definition has_type_qsType'_helper p
: match p with
    | 1 => True
    | p' => has_type (Ast.tApp qsType [quote_positive (p' - 1)])
                     (Ast.tSort (Ast.sType p'))
  end.
Proof.
  destruct p; simpl in *;
  match goal with
    | [ |- has_type (qsType ‘’ ?p0) (Ast.tSort (Ast.sType ?p1)) ]
      => pose proof (has_type_qsType p0 (p1 - 1)) as H;
        simpl in H;
        match type of H with
          | _ -> has_type (qsType ‘’ ?p0') (Ast.tSort (Ast.sType ?p1'))
            => replace p0' with p0 in H;
              [ replace p1' with p1 in H;
                [ apply H
                | .. ]
              | .. ]
        end;
        try reflexivity
    | [ |- True ] => constructor
  end;
  rewrite Pos.sub_1_r, ?denote_quote_positive; simpl;
  try reflexivity.
  clear.
  destruct p; simpl; try reflexivity.
  rewrite Pos.succ_pred_double; reflexivity.
Defined.

Instance has_type_qsType'0 p
: has_type (Ast.tApp qsType [quote_positive (p~0 - 1)])
           (Ast.tSort (Ast.sType p~0))
  := has_type_qsType'_helper (p~0).
Instance has_type_qsType'1 p
: has_type (Ast.tApp qsType [quote_positive (p~1 - 1)])
           (Ast.tSort (Ast.sType p~1))
  := has_type_qsType'_helper (p~1).

Instance quote_sort_has_type0 (x : Ast.sort)
: has_type (quote x) (Ast.tSort (Ast.sType (sort_next_level x))).
Proof.
  unfold quote; destruct x as [ | | []]; simpl; unfold quote, universe_quotable; simpl; try exact _.
  { pose proof (has_type_qsType'0 (Pos.succ p)) as H.
    rewrite Pos.sub_1_r in H.
    simpl in *.
    rewrite Pos.pred_double_succ in H; simpl in *.
    exact H. }
  { pose proof (has_type_qsType'0 1) as H.
    simpl in *.
    exact H. }
Defined.*)

Instance quote_sort_has_type (x : Ast.sort)
: has_type (quote x) sort'.
Proof. unfold quote; destruct x; try exact _. Defined.

Definition quote_name (x : Ast.name) : Preterm
  := match x with
          | Ast.nAnon  => qnAnon
          | Ast.nNamed x0 => Ast.tApp qnNamed [quote x0]
     end.

Instance name_quotable : Quotable Ast.name := quote_name.

Instance quote_name_has_type (x : Ast.name)
: has_type (quote x) name'.
Proof. unfold quote; destruct x; simpl; try exact _. Defined.



Definition quote_cast_kind (x : Ast.cast_kind) : Preterm
  := match x with
          | Ast.VmCast  => qVmCast
          | Ast.NativeCast  => qNativeCast
          | Ast.Cast  => qCast
          | Ast.RevertCast  => qRevertCast
     end.

Instance cast_kind_quotable : Quotable Ast.cast_kind := quote_cast_kind.

Instance quote_cast_kind_has_type (x : Ast.cast_kind)
: has_type (quote x) cast_kind'.
Proof. unfold quote; destruct x; simpl; try exact _. Defined.

Section quote_term_helpers.
  Context (quote_term : Ast.term -> Preterm).

  Fixpoint quote_term_helper (xs : list Ast.term) : Preterm
    := match xs with
         | nil => qnil ‘’ term'
         | cons x' xs' => Ast.tApp qcons [term'; quote_term x'; quote_term_helper xs']
       end.

  Fixpoint quote_term_helper_def (xs : list (Ast.def Ast.term)) : Preterm
    := match xs with
         | nil => qnil ‘’ (def' ‘’ term')
         | cons {| Ast.dname := dname' ; Ast.dtype := dtype' ; Ast.dbody := dbody' ; Ast.rarg := rarg' |} xs'
           => Ast.tApp
                qcons
                [def' ‘’ term'; Ast.tApp qmkdef [quote dname'; quote_term dtype'; quote_term dbody'; quote rarg'];
                  quote_term_helper_def xs']
       end.

  Definition quote_term_step (x : Ast.term) : Preterm
    := match x with
         | Ast.tRel x0 => Ast.tApp qtRel [quote x0]
         | Ast.tVar x0 => Ast.tApp qtVar [quote x0]
         | Ast.tMeta x0 => Ast.tApp qtMeta [quote x0]
         | Ast.tEvar x0 => Ast.tApp qtEvar [quote x0]
         | Ast.tSort x0 => Ast.tApp qtSort [quote x0]
         | Ast.tCast x0 x1 x2 => Ast.tApp qtCast [quote_term x0; quote x1; quote_term x2]
         | Ast.tProd x0 x1 x2 => Ast.tApp qtProd [quote x0; quote_term x1; quote_term x2]
         | Ast.tLambda x0 x1 x2 => Ast.tApp qtLambda [quote x0; quote_term x1; quote_term x2]
         | Ast.tLetIn x0 x1 x2 x3 => Ast.tApp qtLetIn [quote x0; quote_term x1; quote_term x2; quote_term x3]
         | Ast.tApp x0 x1
           => Ast.tApp qtApp [quote_term x0; quote_term_helper x1]
         | Ast.tConst x0 => Ast.tApp qtConst [quote x0]
         | Ast.tInd x0 => Ast.tApp qtInd [quote x0]
         | Ast.tConstruct x0 x1 => Ast.tApp qtConstruct [quote x0; quote x1]
         | Ast.tCase x0 x1 x2 x3 => Ast.tApp qtCase [quote x0; quote_term x1; quote_term x2; quote_term_helper x3]
         | Ast.tFix x0 x1 => Ast.tApp qtFix [quote_term_helper_def x0; quote x1]
         | Ast.tUnknown x0 => Ast.tApp qtUnknown [quote x0]
       end.
End quote_term_helpers.

Fixpoint quote_term (x : Ast.term) : Preterm
  := quote_term_step quote_term x.

Instance term_quotable : Quotable Ast.term := quote_term.

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




Definition map_quote : list { T : Type & Quotable T * T }%type -> list Preterm
  := List.map (fun TvH : { T : Type & Quotable T * T }%type
               => @quote (projT1 TvH) (fst (projT2 TvH)) (snd (projT2 TvH))).

Notation " [[ x ;; .. ;; y ]] " := (cons (_; (_, x)) .. (cons (_; (_, y)) nil) ..) : list_scope.
Notation " [[ x ]] " := (cons (_; (_, x)) nil) : list_scope.


Definition quot := Eval cbv beta delta [qO qS qEmptyString qString qnAnon qAscii qnil qcons qmkdef qtInd qtFix qtCase qtUnknown qtRel qtConstruct qtEvar qtMeta qtVar qtApp qtConst qtSort qtCast qtProd inductive_quotable quote_ascii bool_quotable quote_bool (*quote_string quote_positive quote_nat*) ident_quotable quote_ident quote_name nat_quotable name_quotable quote quote_term sort_quotable cast_kind_quotable quote_sort qsSet qsProp qsType universe_quotable quote_inductive qmkInd] in quote_term.
Definition quot' : Preterm.
Proof.
  let t := (eval cbv delta [quote_term] in quote_term) in
  quote_term t (fun x => exact x).
Defined.

Notation "‘quote’" := quot'.

Notation "⌜ x ⌝" := (quote x).

Notation "‘λ’ ( x : T ) ‘⇒’ body"
  := (Ast.tLambda (Ast.nNamed x) T body) (at level 15).

Axiom has_type_f : has_type ‘f’ ((‘□’ ‘’ ⌜ ‘X’ ⌝) ‘→’ ‘X’).
Existing Instance has_type_f.

Definition App {A' B' : Preterm}
           (box_A'_impl'_B' : □ (A' ‘→’ B'))
           (box_A' : □ A')
: □ B'.
Proof.
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

Definition Quot {T' : Preterm}
           (box_T' : □ T')
: □ (‘□’ ‘’ ⌜ T' ⌝).
Proof.
  refine (Ast.tApp ‘existT’ [‘Preterm’; _; quote box_T'.1; _]; _).
  apply has_type_beta_1_type with (f := fun x => x); simpl.
  apply has_type_beta_1_type with (f := fun x => x); simpl.
  eapply has_type_existT.
  { apply quote_term_has_type. }
  { apply has_type_beta_1_type with (f := fun x => x); simpl.
    apply has_type_beta_1_type with (f := fun x => x); simpl.
    (** Need to somehow lift (quine?) typing derivation here *)
    exfalso; admit.
    Grab Existential Variables.
    admit. }
Defined.

Definition Quot' : Preterm.
Proof.
  let t := (eval cbv delta [Quot] in @Quot) in
  quote_term t (fun x => exact x).
Defined.

Notation "‘Quot’" := Quot'.

Definition L0 (h : Preterm) : Preterm
  := ‘□’ ‘’ (h ‘’ (quote h)) ‘→’ ‘X’.

Quote Definition L0' := (fun h : Preterm => ‘□’ ‘’ (h ‘’ (quote h)) ‘→’ ‘X’).

Notation "‘L0’" := L0'.

Definition L : Preterm
  := L0 ‘L0’.

Definition L' : Preterm
  := ‘L0’ ‘’ ⌜ ‘L0’ ⌝.

Notation "‘L’" := L'.

Definition Conv_has_type (box_box_L : □ (‘□’ ‘’ ⌜ L ⌝))
: has_type box_box_L.1 (‘□’ ‘’ ‘L’).
Proof.
  unfold box' in *.
  apply has_type_beta_1_type with (f := fun x => x); simpl.
  apply has_type_beta_1_type with (f := fun x => x); simpl.
  destruct box_box_L as [x h]; simpl.
  apply has_type_eta_1_type with (f := fun x => x) in h; simpl in h.
  apply has_type_eta_1_type with (f := fun x => x) in h; simpl in h.
  unfold quote, term_quotable in *.
  let T := match type of h with has_type _ ?T => constr:T end in
  let T' := (match eval pattern (quote_term L) in T with ?T' _ => constr:T' end) in
  let x := match type of h with has_type ?x ?T => constr:x end in
  revert h;
    set (T'' := T');
    change (has_type x (T'' (quote_term L)) -> has_type x (T'' ‘L’));
    clearbody T'';
    intro h.
  unfold L, L' in *.
  unfold quote, term_quotable in *.
  unfold L0 in *.
  unfold L0'.
  simpl in h.
  unfold quote_term_step in h.
  simpl in h.
  apply has_type_beta_1_type with (f := T''); simpl.
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

Definition lob : X.
Proof.
  refine ((fun (ℓ : □ L) => f (App ℓ (Conv (Quot ℓ))))
            (Ast.tLambda (Ast.nNamed "ℓ") (‘□’ ‘’ ‘L’) (‘f’ ‘’ (Ast.tApp ‘App’ [Ast.tRel 0; ‘Conv’ ‘’ (‘Quot’ ‘’ Ast.tRel 0)]));
             _)).
  apply has_type_tLambda.
  intro H.
  eapply has_type_tApp; try exact _; [].
  repeat apply has_type_tApp_split.
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

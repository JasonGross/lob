(* Runs on top of https://github.com/gmalecha/template-coq *)
Require Import Template.Template.

Global Set Asymmetric Patterns.

Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import Coq.Program.Program.
(*Require Import Coq.Program.Program.
Local Open Scope string_scope.
Local Open Scope positive_scope.*)

Class Quotable (T : Type) := quote : T -> Ast.term.

(** Some python code for [Quotable] things
<<<
def make_quote_definition(q_i_idents):
    for qi, i in q_i_idents:
        print('Quote Definition %s := %s.' % (qi, i))

def make_quote_for_type_match(q_i_n_idents):
    for qi, i, n in q_i_n_idents:
        ls1 = ' '.join('x%d' % idx for idx in range(n))
        ls2 = '[' + '; '.join('quote x%d' % idx for idx in range(n)) + ']'
        yield '          | %s %s => Ast.tApp %s %s' % (i, ls1, qi, ls2)

def make_quote_for_type(q_i_n_idents, qtype_name, type_name, rec=True):
    q_i_n_idents = list(q_i_n_idents)
    make_quote_definition([(q, i) for q, i, n in q_i_n_idents])
    print('')
    print('''%s quote_%s (x : %s) : Preterm
  := %smatch x with
%s
     end.
''' % (('Fixpoint' if rec else 'Definition'), qtype_name, type_name,
       ("""let x' := (quote_%s : Quotable %s) in
     """ % (qtype_name, type_name) if rec else ''),
       '\n'.join(make_quote_for_type_match(q_i_n_idents))))
    print('Instance %s_quotable : Quotable %s := quote_%s.' % (qtype_name, type_name, qtype_name))
    print('')


ls_inductive = (('mkInd', 2), )
make_quote_for_type((('q' + i, 'Ast.' + i, n) for i, n in ls_inductive), 'inductive', 'Ast.inductive', rec=False)
#ls_sort = (('sProp', 0), ('sSet', 0), ('sType', 1))
#make_quote_for_type((('q' + i, 'Ast.' + i, n) for i, n in ls_sort), 'sort', 'Ast.sort', rec=False)
#ls_name = (('nAnon', 0), ('nNamed', 1))
#make_quote_for_type((('q' + i, 'Ast.' + i, n) for i, n in ls_name), 'name', 'Ast.name', rec=False)
#ls_cast_kind = (('VmCast', 0), ('NativeCast', 0), ('Cast', 0), ('RevertCast', 0))
#make_quote_for_type((('q' + i, 'Ast.' + i, n) for i, n in ls_cast_kind), 'cast_kind', 'Ast.cast_kind', rec=False)
#qds = (('Rel', 1), ('Var', 1), ('Meta', 1), ('Evar', 1), ('Sort', 1), ('Cast', 3), ('Prod', 3), ('Lambda', 3), ('LetIn', 4), ('App', 2), ('Const', 1), ('Ind', 1), ('Construct', 2), ('Case', 4), ('Fix', 2), ('Unknown', 1))
#make_quote_for_type((('qt' + i, 'Ast.t' + i, n) for i, n in qds), 'term', 'Ast.term')
>>>
*)

Quote Definition sigT' := sigT.
Notation "‘sigT’" := sigT'.
Quote Definition existT' := existT.
Notation "‘existT’" := existT'.
Quote Definition prod' := prod.

Quote Definition nat' := nat.
Quote Definition qO := O.
Quote Definition qS := S.
Quote Definition bool' := bool.
Quote Definition qtrue := true.
Quote Definition qfalse := false.
Quote Definition ascii' := Ascii.ascii.
Quote Definition qAscii := Ascii.Ascii.
Quote Definition string' := string.
Quote Definition qEmptyString := EmptyString.
Quote Definition qString := String.
Quote Definition positive' := positive.
Quote Definition qxI := xI.
Quote Definition qxO := xO.
Quote Definition qxH := xH.
Quote Definition list' := list.
Quote Definition qnil := @nil.
Quote Definition qcons := @cons.
Quote Definition ind' := Ast.ind.
Quote Definition inductive' := Ast.inductive.
Quote Definition qmkInd := Ast.mkInd.
Quote Definition sort' := Ast.sort.
Quote Definition qsProp := Ast.sProp.
Quote Definition qsSet := Ast.sSet.
Quote Definition qsType := Ast.sType.
Check eq_refl : Ast.ident = string.
Definition ident' := string'.
Quote Definition name' := Ast.name.
Quote Definition qnAnon := Ast.nAnon.
Quote Definition qnNamed := Ast.nNamed.
Quote Definition cast_kind' := Ast.cast_kind.
Quote Definition qVmCast := Ast.VmCast.
Quote Definition qNativeCast := Ast.NativeCast.
Quote Definition qCast := Ast.Cast.
Quote Definition qRevertCast := Ast.RevertCast.
Quote Definition def' := Ast.def.
Quote Definition qmkdef := Ast.mkdef.
Quote Definition term' := Ast.term.
Quote Definition qtRel := Ast.tRel.
Quote Definition qtVar := Ast.tVar.
Quote Definition qtMeta := Ast.tMeta.
Quote Definition qtEvar := Ast.tEvar.
Quote Definition qtSort := Ast.tSort.
Quote Definition qtCast := Ast.tCast.
Quote Definition qtProd := Ast.tProd.
Quote Definition qtLambda := Ast.tLambda.
Quote Definition qtLetIn := Ast.tLetIn.
Quote Definition qtApp := Ast.tApp.
Quote Definition qtConst := Ast.tConst.
Quote Definition qtInd := Ast.tInd.
Quote Definition qtConstruct := Ast.tConstruct.
Quote Definition qtCase := Ast.tCase.
Quote Definition qtFix := Ast.tFix.
Quote Definition qtUnknown := Ast.tUnknown.

Definition mfixpoint' T := (Ast.tApp list' [Ast.tApp def' [T]]).

Fixpoint quote_nat (n : nat) : Ast.term
  := match n with
       | O => qO
       | S n' => Ast.tApp qS [quote_nat n']
     end.

Instance nat_quotable : Quotable nat := quote_nat.

Definition quote_bool (b : bool) : Ast.term
  := if b then qtrue else qfalse.

Instance bool_quotable : Quotable bool := quote_bool.

Definition quote_ascii (x : Ascii.ascii) : Ast.term
  := match x with
          | Ascii.Ascii x0 x1 x2 x3 x4 x5 x6 x7 => Ast.tApp qAscii [quote x0; quote x1; quote x2; quote x3; quote x4; quote x5; quote x6; quote x7]
     end.

Instance ascii_quotable : Quotable Ascii.ascii := quote_ascii.



Fixpoint quote_string (s : string) : Ast.term
  := match s with
       | EmptyString => qEmptyString
       | String a s' => Ast.tApp qString [quote_ascii a; quote_string s']
     end.

Instance string_quotable : Quotable string := quote_string.

Definition quote_ident : Ast.ident -> Ast.term
  := quote_string.

Instance ident_quotable : Quotable Ast.ident := quote_ident.

Fixpoint quote_positive (x : positive) : Ast.term
  := match x with
       | xI p => Ast.tApp qxI [quote_positive p]
       | xO p => Ast.tApp qxO [quote_positive p]
       | xH => qxH
     end.

Instance positive_quotable : Quotable positive := quote_positive.

Instance universe_quotable : Quotable Ast.universe := quote_positive.


Fixpoint quote_list {T} `{Quotable T} T' (ls : list T) : Ast.term
  := match ls with
       | nil => Ast.tApp qnil [T']
       | cons x xs => Ast.tApp qcons [T'; quote x; quote_list T' xs]
     end.

Instance list_quotable {T} `{Quotable T} T' : Quotable (list T) := quote_list T'.

Definition quote_inductive (x : Ast.inductive) : Ast.term
  := match x with
       | Ast.mkInd x0 x1 => Ast.tApp qmkInd [quote x0; quote x1]
     end.

Instance inductive_quotable : Quotable Ast.inductive := quote_inductive.



Definition quote_sort (x : Ast.sort) : Ast.term
  := match x with
          | Ast.sProp  => qsProp
          | Ast.sSet  => qsSet
          | Ast.sType x0 => Ast.tApp qsType [quote x0]
     end.

Instance sort_quotable : Quotable Ast.sort := quote_sort.

Definition quote_name (x : Ast.name) : Ast.term
  := match x with
          | Ast.nAnon  => qnAnon
          | Ast.nNamed x0 => Ast.tApp qnNamed [quote x0]
     end.

Instance name_quotable : Quotable Ast.name := quote_name.


Definition quote_cast_kind (x : Ast.cast_kind) : Ast.term
  := match x with
          | Ast.VmCast  => qVmCast
          | Ast.NativeCast  => qNativeCast
          | Ast.Cast  => qCast
          | Ast.RevertCast  => qRevertCast
     end.

Instance cast_kind_quotable : Quotable Ast.cast_kind := quote_cast_kind.


Section quote_term_helpers.
  Context (quote_term : Ast.term -> Ast.term).

  Fixpoint quote_term_helper (xs : list Ast.term) : Ast.term
    := match xs with
         | nil => Ast.tApp qnil [term']
         | cons x' xs' => Ast.tApp qcons [term'; quote_term x'; quote_term_helper xs']
       end.

  Fixpoint quote_term_helper_def (xs : list (Ast.def Ast.term)) : Ast.term
    := match xs with
         | nil => Ast.tApp qnil [Ast.tApp def' [term']]
         | cons {| Ast.dname := dname' ; Ast.dtype := dtype' ; Ast.dbody := dbody' ; Ast.rarg := rarg' |} xs'
           => Ast.tApp
                qcons
                [Ast.tApp def' [term']; Ast.tApp qmkdef [term'; quote dname'; quote_term dtype'; quote_term dbody'; quote rarg'];
                  quote_term_helper_def xs']
       end.

  Definition quote_term_step (x : Ast.term) : Ast.term
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

Fixpoint quote_term (x : Ast.term) : Ast.term
  := quote_term_step quote_term x.

Instance term_quotable : Quotable Ast.term := quote_term.

Local Arguments quote_term_step : simpl never.

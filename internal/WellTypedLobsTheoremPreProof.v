Require Import Coq.Setoids.Setoid Coq.Classes.CMorphisms.
Require Export Lob.Notations Lob.WellTypedLobsTheoremStatement.

(** The proof of the theorem *)

Ltac do_shelve tac := tac; [ shelve | | ].

Module Type TermPrimitives (Export LC : LobContext).
  Notation W := weakenTyp.

  Axiom weakenTerm : forall {Γ A B}, Term B -> Term (@weakenTyp Γ A B).

  Notation w := weakenTerm.

  Axiom substTyp_weakenTyp
  : forall {Γ A B a},
      @Term Γ (@substTyp Γ A (@weakenTyp Γ A B) a) -> @Term Γ B.
  Notation SW := substTyp_weakenTyp.

  Axiom tProd : forall {Γ} A, Typ (Γ ▻ A) -> Typ Γ.
  Definition tProd_nd : forall {Γ}, Typ Γ -> Typ Γ -> Typ Γ
    := fun Γ A B => @tProd Γ A (W B).
  Notation "A ‘→’ B" := (tProd A B) : typ_scope.
  Notation "A ‘→'’ B" := (tProd_nd A B) : typ_scope.

  Axiom tLambda : forall {Γ A B}, @Term (Γ ▻ A) B -> Term (A ‘→’ B).
  Definition tLambda_nd : forall {Γ A B},
                            @Term Γ B -> Term (A ‘→'’ B)
    := fun Γ A B b => @tLambda Γ A (W B) (w b).
  Notation "‘λ.’" := tLambda : term_scope.
  Notation "‘λ'.’" := tLambda_nd : term_scope.

  Axiom tApp : forall {Γ A B}
                      (f : Term (@tProd Γ A B))
                      (x : Term A),
                 Term (B ‘’ x).
  Definition tApp_nd : forall {Γ A B},
                         Term (@tProd_nd Γ A B)
                         -> Term A
                         -> Term B
    := fun Γ A B f x => SW (@tApp Γ A (W B) f x).
  Notation "f ‘’ₐ x" := (tApp f x) : term_scope.
  Notation "f ‘'’ₐ x" := (tApp_nd f x) : term_scope.

  Axiom weakenTyp_tProd : forall {Γ A B C},
                            Term (@weakenTyp Γ C (A ‘→'’ B))
                            -> Term (@weakenTyp Γ C A ‘→’ W (W B)).
  Definition weakenProd : forall {Γ A B C},
                            Term (A ‘→'’ B)
                            -> Term (@weakenTyp Γ C A ‘→’ W (W B))
    := fun Γ A B C x => weakenTyp_tProd (w x).
  Notation "w∀" := weakenProd.

  (*Axiom weakenTyp1 : forall {Γ A B}, Typ (Γ ▻ B) -> Typ (Γ ▻ A ▻ (weakenTyp B)).

  Axiom weakenTerm1 : forall {Γ A B C}, @Term (Γ ▻ B) C -> @Term (Γ ▻ A ▻ weakenTyp B) (@weakenTyp1 Γ A B C).

  Axiom weakenTyp2 : forall {Γ A B C}, Typ (Γ ▻ B ▻ C) -> Typ (Γ ▻ A ▻ (weakenTyp B) ▻ (weakenTyp1 C)).

  Axiom weakenTerm2 : forall {Γ A B C D}, Term D -> Term (@weakenTyp2 Γ A B C D).

  Axiom weakenTyp3 : forall {Γ A B C D}, Typ (Γ ▻ B ▻ C ▻ D) -> Typ (Γ ▻ A ▻ (weakenTyp B) ▻ (weakenTyp1 C) ▻ (weakenTyp2 D)).

  Axiom weakenTerm3 : forall {Γ A B C D E}, Term E -> Term (@weakenTyp3 Γ A B C D E).

  Axiom weakenTyp4 : forall {Γ A B C D E}, Typ (Γ ▻ B ▻ C ▻ D ▻ E) -> Typ (Γ ▻ A ▻ (weakenTyp B) ▻ (weakenTyp1 C) ▻ (weakenTyp2 D) ▻ (weakenTyp3 E)).

  Axiom weakenTerm4 : forall {Γ A B C D E F}, Term F -> Term (@weakenTyp4 Γ A B C D E F).

  Axiom weakenTyp5 : forall {Γ A B C D E F}, Typ (Γ ▻ B ▻ C ▻ D ▻ E ▻ F) -> Typ (Γ ▻ A ▻ (weakenTyp B) ▻ (weakenTyp1 C) ▻ (weakenTyp2 D) ▻ (weakenTyp3 E) ▻ (weakenTyp4 F)).

  Axiom weakenTerm5 : forall {Γ A B C D E F G}, Term G -> Term (@weakenTyp5 Γ A B C D E F G).

  Notation W := weakenTyp (only parsing).
  Notation W1 := weakenTyp1.
  Notation W2 := weakenTyp2.
  Notation W3 := weakenTyp3.
  Notation W4 := weakenTyp4.
  Notation W5 := weakenTyp5.
  Notation w := weakenTerm.
  Notation w1 := weakenTerm1.
  Notation w2 := weakenTerm2.
  Notation w3 := weakenTerm3.
  Notation w4 := weakenTerm4.
  Notation w5 := weakenTerm5.

  Axiom substTerm1 : forall {Γ A B C}
                            (c : Term C)
                            (a : Term A),
                       Term (@substTyp1 Γ A B C a).
  Notation "f ‘’₁ x" := (@substTerm1 _ _ _ _ f x) : term_scope.

  Axiom substTyp2 : forall {Γ A B C}
                           (D : Typ (Γ ▻ A ▻ B ▻ C))
                           (a : Term A),
                      Typ (Γ ▻ substTyp B a ▻ substTyp1 C a).
  Notation "f ‘’₂ x" := (@substTyp2 _ _ _ _ f x) : typ_scope.


  Axiom substTerm2 : forall {Γ A B C D}
                            (c : Term D)
                            (a : Term A),
                       Term (@substTyp2 Γ A B C D a).
  Notation "f ‘’₂ x" := (@substTerm2 _ _ _ _ _ f x) : term_scope.

  Axiom substTyp3 : forall {Γ A B C D}
                           (E : Typ (Γ ▻ A ▻ B ▻ C ▻ D))
                           (a : Term A),
                      Typ (Γ ▻ substTyp B a ▻ substTyp1 C a ▻ substTyp2 D a).
  Notation "f ‘’₃ x" := (@substTyp3 _ _ _ _ _ f x) : typ_scope.

  Axiom substTerm3 : forall {Γ A B C D E}
                            (e : Term E)
                            (a : Term A),
                       Term (@substTyp3 Γ A B C D E a).
  Notation "f ‘’₃ x" := (@substTerm3 _ _ _ _ _ _ f x) : term_scope.

  Axiom substTyp4 : forall {Γ A B C D E}
                           (F : Typ (Γ ▻ A ▻ B ▻ C ▻ D ▻ E))
                           (a : Term A),
                      Typ (Γ ▻ substTyp B a ▻ substTyp1 C a ▻ substTyp2 D a ▻ substTyp3 E a).
  Notation "f ‘’₄ x" := (@substTyp4 _ _ _ _ _ _ f x) : typ_scope.

  Axiom substTerm4 : forall {Γ A B C D E F}
                            (f : Term F)
                            (a : Term A),
                       Term (@substTyp4 Γ A B C D E F a).
  Notation "f ‘’₄ x" := (@substTerm4 _ _ _ _ _ _ _ f x) : term_scope.

  Axiom subst_weaken1_weaken_Typ
  : forall {Γ A B C a},
      Term (@substTyp _ _ (@weakenTyp1 Γ C A (@weakenTyp Γ A B)) a) -> Term (@weakenTyp _ C B).

  Axiom Subst1_Subst_Weaken_Weaken
  : forall {Γ C B A a b},
      @Term Γ ((A ‘→’ B ‘→’ C) ‘’₁ a ‘’ b)
      -> @Term Γ C.

  Axiom subst_Weaken1__weaken_Typ
  : forall {Γ T B A a},
      @Term (Γ ▻ T) (W (A ‘’ a))
      -> @Term (Γ ▻ T) (@weakenTyp1 _ _ _ A ‘’ @weakenTerm _ _ B a).

  Notation W1w := subst_Weaken1__weaken_Typ.

  Axiom Subst_Subst1_Weaken2__weaken__W1w
  : forall {Γ B C T A a b},
      @Term (Γ ▻ T) (W (A ‘’₁ a ‘’ b))
      -> @Term (Γ ▻ T) (@weakenTyp2 _ _ B _ A ‘’₁ w a ‘’ W1w (A := C) (w b)).

  Axiom Subst_Subst1_Subst_Weaken1_Weaken1
  : forall {Γ} {B C : Typ Γ} {D : Typ (Γ ▻ B)}
           {A : Typ (Γ ▻ C)}
           {a : @Term (Γ ▻ B ▻ D) (D ‘→’ B ‘→’ C)}
           {b : @Term Γ B}
           {c : @Term Γ (D ‘’ b)},
      @Term Γ (A ‘’ (Subst1_Subst_Weaken_Weaken (a ‘’₁ b ‘’ c)))
      -> @Term Γ (W1 (A := D) (W1 (A := B) (B := C) A) ‘’ a ‘’₁ b ‘’ c).

  Axiom Subst_Subst2__Weaken3_Subst2__Subst1_Weaken2_Weaken2__weaken__W1w_w__SS1W2wW1w_w_SS1SW1W1
  : forall {Γ}
           {T D : Typ Γ}
           {E : Typ (Γ ▻ D)}
           {B : Typ Γ}
           {C : Typ (Γ ▻ B)}
           {A : Typ (Γ ▻ B ▻ C)}
           {a : Term (E ‘→’ D ‘→’ B)}
           {b : Term D}
           {c : Term (E ‘’ b)}
           {d : Term (C ‘’ Subst1_Subst_Weaken_Weaken (a ‘’₁ b ‘’ c))},
      @Term (Γ ▻ T) (W (A ‘’₁ (Subst1_Subst_Weaken_Weaken (a ‘’₁ b ‘’ c)) ‘’ d))
      -> @Term (Γ ▻ T) (W3 (B := D) (C := E) (W2 (W2 (B := B) (C := C) A) ‘’₁ a) ‘’₂ w b ‘’₁ W1w (w c) ‘’ Subst_Subst1_Weaken2__weaken__W1w
                        (w (Subst_Subst1_Subst_Weaken1_Weaken1 d))).
*)
  (*Axiom subst_weaken1_weaken_Typ_inv
  : forall {Γ A B C a},
      Term (@weakenTyp _ C B) -> Term (@substTyp _ _ (@weakenTyp1 Γ C A (@weakenTyp Γ A B)) a).*)

(*Check ‘Term’%typ.
  Definition subst_weaken_many_Typ_0
  : forall {Γ A B C D E F G} {Z : Typ (Γ ▻ A ▻ B)} {Y} {a b c d e},
      Term (substTyp1
              (substTyp2
                 (substTyp3
                    (substTyp4
                       (@weakenTyp5 _ G _ _ _ _ _ (@weakenTyp1 _ F _ (@weakenTyp1 _ E _ (@weakenTyp1 _ D _ (@weakenTyp1 _ C _ Z)) ‘’ Y))) a) b) c) d ‘’ e)
      -> Type.
Arguments Term : clear implicits.
intros.
refine (@Term (Γ ▻ G) _).
refine (substTyp (substTyp1 (W2 Z) a) (_ (substTerm (substTerm1 (substTerm2 (substTerm3 (substTerm4 (w5 (w1 Y)) a) b) c) d) e))); shelve_unifiable.
pose @subst_weaken1_weaken_Typ.

      -> Term (substTyp1
              (substTyp2
                 (substTyp3
                    (substTyp4
                       (@weakenTyp5 _ G _ _ _ _ _ (@weakenTyp1 _ F _ (@weakenTyp1 _ E _ (@weakenTyp1 _ D _ (@weakenTyp1 _ C _ Z)) ‘’ Y))) a) b) c) d ‘’ e).
 "Term (ε ▻ ?A0)
    (substTyp1
       (substTyp2
          (substTyp3
             (substTyp4 (W5 (W1 (W1 (W1 (W1 ‘Term’)) ‘’ qsubstTyp))) ?t3)
             ?t) ?t0) f ‘’ x)" while it is expected to have type
 "Term (ε ▻ ?A0) (?A0 ‘→’ ‘□’ ‘’ ⌜ ‘X’ ⌝%typ)".
_*)

End TermPrimitives.

Module Type QuotedPrimitives (Export LC : LobContext) (Export TP : TermPrimitives LC).
  Axiom qcontext_extend : □ (‘Context’ ‘→’ ‘Typ’ ‘→'’ W ‘Context’).
  Notation "Γ ‘▻’ x" := (qcontext_extend ‘’ₐ Γ ‘'’ₐ x)%term : term_scope.
  Notation "Γ ‘▻’ x" := (Γ ‘▻’ x)%term : context_scope.

  (*Axiom VAR1 : forall {Γ A B}, @Term (Γ ▻ A ▻ B) (weakenTyp (weakenTyp A)).
  Notation "‘VAR₁’" := VAR1 : term_scope.*)

  (*Axiom qsubstTyp : @Term (ε ▻ ‘Context’ ▻ ‘Typ’ ▻ (W1 (W1 ‘Typ’) ‘’ qcontext_extend) ▻ W ‘Term’) (W (W (W ‘Typ’))).
  Notation "f ‘‘’’ x" := (substTerm (substTerm1 (substTerm2 (substTerm3 qsubstTyp _) _) f) x) : typ_scope.
  Axiom qsubstTerm : @Term (ε ▻ ‘Context’ ▻ ‘Typ’ ▻ (W1 (W1 ‘Typ’) ‘’ qcontext_extend) ▻ substTyp1 (W2 (W2 ‘Term’)) _ ▻ W (W ‘Term’))
                           (W1 (W1 (W1 (W1 ‘Term’)) ‘’ qsubstTyp)).
  Notation "f ‘‘’’ x" := (substTerm (substTerm1 (substTerm2 (substTerm3 (substTerm4 qsubstTerm _) _) _) f) x) : term_scope.

  (** XXX Is this actually true? *)
  Axiom Conv0_Typ
  : forall {qH0},
      □ (‘Typ’ ‘’ ⌜ ε ▻ ‘Term’ ‘’₁ ⌜ ε ⌝%ctx ‘’ qH0 ⌝%ctx)
      -> □ (‘Typ’ ‘’ (‘ε’ ‘▻’ qH0)%ctx).
  Axiom Conv0_Term
  : forall {T qH0 qH0'},
      Term (T ‘→’ ‘Term’ ‘’₁ ⌜ ε ▻ ‘Term’ ‘’₁ ⌜ ε ⌝%ctx ‘’ qH0 ⌝%ctx ‘’ qH0') ->
      Term (T ‘→’ ‘Term’ ‘’₁ (‘ε’ ‘▻’ qH0)%ctx ‘’ Conv0_Typ qH0').

  Axiom qquote_context : @Term (ε ▻ ‘Context’) (W ((substTyp1 ‘Term’ ‘ε’) ‘’ ⌜ ‘Context’ ⌝%typ)).*)

(*
  Definition qqempty_context := qquote_context ε.
  Notation "‘ε’" := qempty_context : term_scope.
  Notation "⌜ x ⌝" := (quote_context x) : context_scope.

  Axiom qTerm : Typ (ε ▻ ‘Context’ ▻ ‘Typ’).
  Notation "‘Term’" := qTerm : typ_scope.

  Definition qbox := (substTyp1 ‘Term’ ‘ε’).
  Notation "‘□’" := qbox : typ_scope.

  Axiom quote_typ : forall {Γ}, Typ Γ -> □ (‘Typ’ ‘’ ⌜ Γ ⌝%ctx).
  Notation "⌜ x ⌝" := (quote_typ x%typ) : typ_scope.
  Axiom quote_term : forall {Γ} {A : Typ Γ}, Term A -> □ ((substTyp1 ‘Term’ ⌜ Γ ⌝%ctx) ‘’ ⌜ A ⌝%typ).
  Notation "⌜ x ⌝" := (quote_term x%term) : term_scope.

  Notation "x ‘→’ y" := (@weakenTyp _ x%typ y) : typ_scope.
*)
  (*Axiom qsubstTyp : @Term (ε ▻ ‘Context’ ▻ ‘Typ’ ▻ (W1 (W1 ‘Typ’) ‘’ qcontext_extend) ▻ W ‘Term’) (W (W (W ‘Typ’))).

  Axiom qweakenTyp : forall {Γ A}, Typ Γ -> Typ (Γ ▻ A).
  Axiom substTyp1 : forall {Γ A B}
                           (C : Typ (Γ ▻ A ▻ B))
                           (a : Term A),
                      Typ (Γ ▻ substTyp B a).*)

End QuotedPrimitives.

Module Type TypeQuine (Export LC : LobContext) (Export LH : LobHypotheses LC) (Export TP : TermPrimitives LC).
  Axiom H0 : Typ ε.
  Definition H := Term H0.
  Definition qH0 := quote_typ H0.
  Definition qH := ((substTyp1 ‘Term’ _) ‘’ qH0)%typ.
  Notation "‘H’" := qH : typ_scope.
  Definition H0' := (‘H’ ‘→'’ ‘X’)%typ.
  Definition H' := Term H0'.
  Definition qH0' := quote_typ H0'.
  Definition qH' := ((substTyp1 ‘Term’ _) ‘’ qH0')%typ.
  Notation "‘H'’" := qH' : typ_scope.
  Axiom toH : H' -> H.
  Axiom fromH : H -> H'.
  Axiom qtoH : Term (‘H'’ ‘→'’ ‘H’).
  Axiom qfromH : Term (‘H’ ‘→'’ ‘H'’).
  Notation "‘toH’" := qtoH : term_scope.
  Notation "‘fromH’" := qfromH : term_scope.
End TypeQuine.

Module Lob1'
       (LC : LobContext)
       (LH : LobHypotheses LC)
       (Export TP : TermPrimitives LC)
       (Export QP : QuotedPrimitives LC TP)
       (Export TQ : TypeQuine LC LH TP)
<: LobsTheorem LC LH.
  (*Notation "f ‘‘’’₅ x" := ((w5 qsubstTerm) ‘’₄ _ ‘’₃ _ ‘’₂ _ ‘’₁ f ‘’ x)%term : term_scope.*)

  Definition lob : X.
  Proof.
Arguments Term : clear implicits.
    refine (let h : H := toH
                           (‘λ.’
                              ((w∀ (‘λ.’ ‘f’))
                                 ‘'’ₐ _))%term(*(subst_weaken1_weaken_Typ
                                ((w1 ‘f’)
                                   ‘’ (let f := Subst_Subst2__Weaken3_Subst2__Subst1_Weaken2_Weaken2__weaken__W1w_w__SS1W2wW1w_w_SS1SW1W1 (Conv0_Term ‘fromH’%term) : @Term (ε ▻ ‘H’) _ in
                                       let x := _ in
                                       (_ (f ‘‘’’₅ x)%term))))*) in
            f (fromH h ‘'’ₐ ⌜ h ⌝)%term); shelve_unifiable.

    refine (let k := (w∀ (tLambda ‘f’))%term in _); shelve_unifiable.
    unfold tProd_nd.
    unfold H'.
    unfold H0'.
     subst f.
refine (let k := (W4 (W2 (W2 ‘Term’) ‘’₁ qcontext_extend
            ‘→’ W1 (W1 ‘Typ’) ‘’ qcontext_extend ‘→’ ‘Term’) ‘’₃
                                                            w ‘ε’ )%typ in _); shelve_unifiable.
refine (let k' := (W3 ((W2 (W2 ‘Term’) ‘’₁ qcontext_extend
            ‘→’ W1 (W1 ‘Typ’) ‘’ qcontext_extend ‘→’ ‘Term’) ‘’₃
                                                           ‘ε’))%typ in _); shelve_unifiable.
pose ((W2 (W2 ‘Term’) ‘’₁ qcontext_extend
            ‘→’ W1 (W1 ‘Typ’) ‘’ qcontext_extend ‘→’ ‘Term’) ‘’₃
                                                             ‘ε’)%typ.
pose ((W2 (W2 ‘Term’) ‘’₁ qcontext_extend
            ‘→’ W1 (W1 ‘Typ’) ‘’ qcontext_extend ‘→’ ‘Term’) ‘’₃
                                                             ‘ε’)%typ.
(W4
           (W2 (W2 ‘Term’) ‘’₁ qcontext_extend
            ‘→’ W1 (W1 ‘Typ’) ‘’ qcontext_extend ‘→’ ‘Term’) ‘’₃
         w ‘ε’ ‘’₂ W1w (w qH0)
         ‘’₁ Subst_Subst1_Weaken2__weaken__W1w
               (w (Subst_Subst1_Subst_Weaken1_Weaken1 (Conv0_Typ qH0')))
         ‘’ Subst_Subst2__Weaken3_Subst2__Subst1_Weaken2_Weaken2__weaken__W1w_w__SS1W2wW1w_w_SS1SW1W1
              (Conv0_Term ‘fromH’))

(W4
           (W2 (W2 ‘Term’) ‘’₁ qcontext_extend
            ‘→’ W1 (W1 ‘Typ’) ‘’ qcontext_extend ‘→’ ‘Term’) ‘’₃
         w ‘ε’ ‘’₂ W1w (w qH0)
         ‘’₁ Subst_Subst1_Weaken2__weaken__W1w
               (w (Subst_Subst1_Subst_Weaken1_Weaken1 (Conv0_Typ qH0')))
         ‘’ Subst_Subst2__Weaken3_Subst2__Subst1_Weaken2_Weaken2__weaken__W1w_w__SS1W2wW1w_w_SS1SW1W1
              (Conv0_Term ‘fromH’))
    unfold qH' in *.
    pose qH0'.
    unfold qH in *.
    move t0 at top.
    pose ‘H'’%typ.
    unfold qH'.
    unfold qH in *.
    Unshelve

match eval unfold t in t with
  | ?f ?x => pose x
end.
pose (?t16@{x:=‘fromH’%term}).
let t := type of ?t16 in assert t.
unify ?t16 qH0'.

Arguments Term : clear implicits.
refine (let f := _ in
        let x := _ in
        let k := (substTerm (substTerm1 (substTerm2 (substTerm3 (substTerm4 (w5 qsubstTerm) _) _) _) f) x) in _); shelve_unifiable.
unfold qH.

(substTerm (substTerm1 (substTerm2 (substTerm3 (substTerm4 qsubstTerm _) _) _) f) x)


    Set Printing Implicit.
    unfold H', qH'.

  Axiom qLetIn : forall {Γ A B}, Term (

    Set Printing All.


, Typ (Γ ▻ A) -> Term A -> Typ Γ.
  Notation "f ‘’ x" := (@substTyp _ _ f x) : typ_scope.
  Axiom weakenTyp : forall {Γ A}, Typ Γ -> Typ (Γ ▻ A).
  Axiom substTerm : forall {Γ A} {B : Typ (Γ ▻ A)}


    Focus 2.


    refine ((fun (ℓ : □ L) => f (App (Conv2 ℓ) (Conv (Quot ℓ))))
              (Conv2_inv
                 (wttLambda_nd
                    (‘□’ ‘’ ‘L’)
                    (‘‘f’’ ‘’ ((‘‘App’’ ‘’ (qConv2 ‘‘VAR₀’’)) ‘’ ((*‘‘Conv’’ ‘’*) (‘‘Quote’’ ‘’ ‘‘VAR₀’’)))))));
    try exact _.
  Defined.
End Lob1'.


Module Type PretermPrimitives (Export LC : LobContext).
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

Module Type PreL (LC : LobContext) (Export PP : PretermPrimitives LC).

  Axiom wttLambda_nd : forall {Γ : Context} {B' : Preterm},
                       forall A' : Preterm, box' (Γ ▻ A') B' -> box' Γ (A' ‘→’ B').

  Axiom wttApp_1_nd : forall {Γ : Context} {A' B' : Preterm} {H : is_closed B'},
                        box' Γ (A' ‘→’ B') -> box' Γ A' -> box' Γ B'.

  Notation "x ‘’ y" := (wttApp_1_nd x%wtt y%wtt) : well_typed_term_scope.

  (*Axiom box'_weaken : forall {Γ A}, box' ε A -> box' Γ A.*)
End PreL.

Module Lob1 (LC : LobContext) (Import LH : LobHypotheses LC).

  Module Type PretermPrimitives' := PretermPrimitives LC.

  Module Type L (PP : PretermPrimitives') (Export PL : PreL LC PP).
    Axiom L : Preterm.
    Axiom qL : Preterm.
    Notation "‘L’" := qL.
  End L.

  Module Type PostL (PP : PretermPrimitives') (PL : PreL LC PP) (Export L' : L PP PL).
    Axiom App : let A' := ‘□’ ‘’ ‘L’ in
                let B' := ‘X’ in
                □ (A' ‘→’ B') -> □ A' -> □ B'.

    Axiom Conv : □ (‘□’ ‘’ ⌜ L ⌝) -> □ (‘□’ ‘’ ‘L’).

    Axiom Conv2 : □ L -> □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’).
    Axiom Conv2_inv : □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’) -> □ L.
    Axiom qConv2 : let Γ := (ε ▻ ‘□’ ‘’ ‘L’) in
                   box' Γ (‘□’ ‘’ ‘L’) -> box' Γ (‘□’ ‘’ (⌜ (‘□’ ‘’ ‘L’) ⌝ ‘‘→’’ ⌜ ‘X’ ⌝)).

    Axiom Quot : □ L -> □ (‘□’ ‘’ ⌜ L ⌝).

    Axiom qbApp
    : let Γ := (ε ▻ ‘□’ ‘’ ‘L’) in
      forall (A' := (⌜ ‘□’ ‘’ ‘L’ ⌝)%preterm)
             (B' := (⌜ ‘X’ ⌝)%preterm),
        box' Γ ((‘□’ ‘’ (A' ‘‘→’’ B')) ‘→’ ‘□’ ‘’ A' ‘→’ ‘□’ ‘’ B').

    Notation "‘‘App’’" := ((*box'_weaken*) qbApp) : well_typed_term_scope.

    (*Axiom qConv
  : □ (‘□’ ‘’ ⌜‘□’ ‘’ ⌜L ⌝ ⌝ ‘→’ ‘□’ ‘’ ⌜ ‘□’ ‘’ ‘L’ ⌝).

  Notation "‘‘Conv’’" := (box'_weaken qConv) : well_typed_term_scope.*)

    Axiom qQuote
    : let Γ := (ε ▻ ‘□’ ‘’ ‘L’) in
      let A := (‘□’ ‘’ ‘L’)%preterm in
      box' Γ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝))).

    Notation "‘‘Quote’’" := ((*box'_weaken*) qQuote) : well_typed_term_scope.

    Axiom box'_weaken : let Γ := (ε ▻ ‘□’ ‘’ ‘L’) in
                        forall {A} {H : is_closed A}, box' ε A -> box' Γ A.
  End PostL.
End Lob1.

Module Type Lob1H (Export LC : LobContext) (Export LH : LobHypotheses LC).
  Module Lob1' := Lob1 LC LH.
  Declare Module Export PP : PretermPrimitives LC.
  Declare Module Export PreL' : PreL LC PP.
  Declare Module Export L' : Lob1'.L PP PreL'.
  Declare Module Export PostL' : Lob1'.PostL PP PreL' L'.
End Lob1H.

Module Lob1' (LC : LobContext) (Import LH : LobHypotheses LC) (Import M : Lob1H LC LH)
<: LobsTheorem LC LH.
  Notation "‘‘f’’" := (box'_weaken wtt_qf) : well_typed_term_scope.

  Definition lob : X.
    refine ((fun (ℓ : □ L) => f (App (Conv2 ℓ) (Conv (Quot ℓ))))
              (Conv2_inv
                 (wttLambda_nd
                    (‘□’ ‘’ ‘L’)
                    (‘‘f’’ ‘’ ((‘‘App’’ ‘’ (qConv2 ‘‘VAR₀’’)) ‘’ ((*‘‘Conv’’ ‘’*) (‘‘Quote’’ ‘’ ‘‘VAR₀’’)))))));
    try exact _.
  Defined.
End Lob1'.

Module Type PretermReflectionPrimitives (Export LC : LobContext).
  Axiom qPreterm : Preterm.
  Notation "‘Preterm’" := qPreterm : preterm_scope.

  Axiom qquote : Preterm.
  Notation "‘quote’" := qquote : preterm_scope.
End PretermReflectionPrimitives.

Module Type TypingRules (Export LC : LobContext) (Export PP : PretermPrimitives LC).
  Axiom capture_avoiding_subst_0 : forall (in_term : Preterm)
                                          (new_value : Preterm),
                                     Preterm.
  Notation "x [ 0 ↦ y ]" := (capture_avoiding_subst_0 x y).
  Axiom convertible : Context -> Preterm -> Preterm -> Type.
  Axiom box'_respectful : forall {Γ A B},
                            convertible Γ A B
                            -> box' Γ A
                            -> box' Γ B.
  Axiom convertible_refl : forall {Γ}, Reflexive (convertible Γ).
  Axiom convertible_sym : forall {Γ}, Symmetric (convertible Γ).
  Axiom convertible_trans : forall {Γ}, Transitive (convertible Γ).
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

  Axiom tProd_Proper_convertible
  : forall Γ,
      Proper (convertible Γ ==> eq ==> convertible Γ) tProd.
  Existing Instance tProd_Proper_convertible.
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

Module Type PretermReflectionTypingRules (Export LC : LobContext) (Export PP : PretermPrimitives LC) (Export PRP : PretermReflectionPrimitives LC) (Export TR : TypingRules LC PP).
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
               ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ⌜ T ⌝))))
      -> box' Γ (‘□’ ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ ⌜ ⌜ T ⌝ ⌝))).

  Axiom box_quote_app_quote_inv
  : forall Γ T,
      box' Γ (‘□’ ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ ⌜ ⌜ T ⌝ ⌝)))
      -> box' Γ (‘□’
                  ‘’ (‘App’ ‘’ ⌜‘□’ ⌝ ‘’ (‘App’ ‘’ ⌜T ⌝ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ⌜ T ⌝)))).
End PretermReflectionTypingRules.

Module Type PostL_Assumptions (LC : LobContext) (Export PP : PretermPrimitives LC) (Export PRP : PretermReflectionPrimitives LC) (Export TR : TypingRules LC PP).
  Axiom Quot : forall T, □ T -> □ (‘□’ ‘’ ⌜ T ⌝).

  Section context.
    Context (qX qL0 : Preterm).
    Let Γ := (ε ▻ (‘□’
                    ‘’ (tLambda ‘Preterm’
                                (‘App’ ‘’ ⌜ ‘□’ ⌝
                                  ‘’ (‘App’ ‘’ ‘VAR₀’ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ‘VAR₀’))
                                  ‘‘→’’ ⌜ qX ⌝) ‘’ ⌜ qL0 ⌝))).

    Axiom qQuote
    : forall T,
        let A := (‘□’ ‘’ T)%preterm in
        box' Γ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝))).

    Axiom qbApp
    : forall A' B',
        box' Γ ((‘□’ ‘’ (A' ‘‘→’’ B')) ‘→’ (‘□’ ‘’ A') ‘→’ (‘□’ ‘’ B')).

    Axiom box'_weaken
    : forall {A} {H : is_closed A}, box' ε A -> box' Γ A.
  End context.

  Axiom App : forall {A' B'} {H : is_closed B'},
                □ (A' ‘→’ B') -> □ A' -> □ B'.

End PostL_Assumptions.

Module Lob2 (LC : LobContext) (Import LH : LobHypotheses LC).
  Module Lob1' := Lob1 LC LH.

  Module L (Export PP : PretermPrimitives LC) (Export PL : PreL LC PP) (Export PRP : PretermReflectionPrimitives LC) (Export TR : TypingRules LC PP) (Export PRTR : PretermReflectionTypingRules LC PP PRP TR)
  <: Lob1'.L PP PL.

    Definition L0 (h : Preterm) : Preterm
      := ((‘□’ ‘’ (h ‘’ (quote h))) ‘→’ ‘X’)%preterm.

    Definition qL0 : Preterm
      := tLambda
           ‘Preterm’
           (((‘App’ ‘’ ⌜ ‘□’ ⌝)
               ‘’ ((‘App’ ‘’ ‘VAR₀’ ‘’ (‘App’ ‘’ ⌜ ‘quote’ ⌝ ‘’ ‘VAR₀’))))
              ‘‘→’’
              ⌜ ‘X’ ⌝).

    Notation "‘L0’" := qL0.

    Definition L : Preterm
      := L0 ‘L0’.

    Definition qL : Preterm
      := ‘L0’ ‘’ ⌜ ‘L0’ ⌝.

    Notation "‘L’" := qL.
  End L.

  Module PostL (Export PP : PretermPrimitives LC) (Export PL : PreL LC PP) (Export PRP : PretermReflectionPrimitives LC) (Export TR : TypingRules LC PP) (Export PRTR : PretermReflectionTypingRules LC PP PRP TR) (LA : PostL_Assumptions LC PP PRP TR).
    Module L' := L PP PL PRP TR PRTR.
    Include L'.

    Module M <: Lob1'.PostL PP PL L'.

      Hint Rewrite convertible__qtApp__closed convertible__capture_avoiding_subst_0__tApp convertible__quote__closed convertible__quote__app convertible__capture_avoiding_subst_0__tVar0 convertible__qquote__closed convertible__capture_avoiding_subst_0__qtProd convertible__quote__qtProd convertible_beta_app_lambda : convdb.

      Local Ltac set_evars :=
        repeat match goal with
                 | [ |- appcontext[?E] ] => is_evar E; let e := fresh in set (e := E)
               end.

      Local Ltac subst_body :=
        repeat match goal with
                 | [ H := _ |- _ ] => subst H
               end.

      Local Ltac conv_rewrite
        := set_evars;
          repeat match goal with
                   | [ |- convertible _ ?x ?x ] => reflexivity
                   | [ |- convertible _ (?x ‘’ _) (?x ‘’ _) ]
                     => apply tApp_Proper_convertible; [ reflexivity | ]
                   | [ |- convertible _ (_ ‘‘→’’ _) (_ ‘‘→’’ _) ]
                     => apply qtProd_Proper_convertible
                   | [ |- convertible _ (_ ‘→’ ?x) _ ]
                     => apply tProd_Proper_convertible; [ | reflexivity ]
                   | _ => progress rewrite_strat repeat (topdown repeat (hints convdb))
                 (*| _ => progress rewrite ?convertible__capture_avoiding_subst_0__tApp, ?convertible__qtApp__closed, ?convertible__quote__closed, ?convertible__quote__app, ?convertible__capture_avoiding_subst_0__tVar0, ?convertible__qquote__closed, ?convertible__capture_avoiding_subst_0__qtProd, ?convertible__quote__qtProd, ?convertible_beta_app_lambda*)
                 end;
          subst_body.



      Definition Conv : □ (‘□’ ‘’ ⌜ L ⌝) -> □ (‘□’ ‘’ ‘L’).
      Proof.
        unfold box, L, qL.
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
            apply box_quote_app_quote. } }
      Defined.

      Definition Conv2 : □ L -> □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’)
        := fun x => x.
      Definition Conv2_inv : □ (‘□’ ‘’ ‘L’ ‘→’ ‘X’) -> □ L
        := fun x => x.
      Definition qConv2 (Γ := (ε ▻ ‘□’ ‘’ ‘L’))
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

      Global Instance convertible_Proper_flip_arrow {Γ}
      : Proper (convertible Γ ==> convertible Γ ==> flip arrow) (convertible Γ).
      Proof.
        intros ?? H ?? H' H''.
        rewrite H, H''.
        rewrite <- H'.
        reflexivity.
      Qed.

      Definition qbApp
      : let Γ := (ε ▻ ‘□’ ‘’ ‘L’) in
        forall (A' := (⌜‘□’ ‘’ ‘L’ ⌝)%preterm)
               (B' := (⌜‘X’ ⌝)%preterm),
          box' Γ ((‘□’ ‘’ (A' ‘‘→’’ B')) ‘→’ (‘□’ ‘’ A') ‘→’ (‘□’ ‘’ B'))
        := LA.qbApp _ _ _ _.

      Notation "‘‘App’’" := ((*box'_weaken*) qbApp) : well_typed_term_scope.

      Definition qQuote
      : let Γ := ε ▻ ‘□’ ‘’ ‘L’ in
        let A := (‘□’ ‘’ ‘L’)%preterm in
        box' Γ (A ‘→’ (‘□’ ‘’ (⌜ A ⌝)))
        := LA.qQuote _ _ _.

      Notation "‘‘Quote’’" := ((*box'_weaken*) qQuote) : well_typed_term_scope.

      Definition App : (let A' := ‘□’ ‘’ ‘L’ in
                        let B' := ‘X’ in
                        □ (A' ‘→’ B') -> □ A' -> □ B')
        := (@LA.App _ _ LH.qX_closed).

      Definition box'_weaken : let Γ := (ε ▻ ‘□’ ‘’ ‘L’) in
                               forall {A} {H : is_closed A}, box' ε A -> box' Γ A
        := @LA.box'_weaken _ _.

    End M.
  End PostL.
End Lob2.

Module Type Lob2H (Export LC : LobContext) (Export LH : LobHypotheses LC).
  Module Lob2' := Lob2 LC LH.
  Declare Module Export PP : PretermPrimitives LC.
  Declare Module Export PreL' : PreL LC PP.
  Declare Module Export PRP : PretermReflectionPrimitives LC.
  Declare Module Export TR : TypingRules LC PP.
  Declare Module Export PRTR : PretermReflectionTypingRules LC PP PRP TR.
  Declare Module Export LA : PostL_Assumptions LC PP PRP TR.
End Lob2H.

Module Lob2'0 (LC : LobContext) (LH : LobHypotheses LC) (M : Lob2H LC LH)
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
       (Export LC : LobContext)
       (Export LH : LobHypotheses LC)
       (Export PP : PretermPrimitives LC)
       (Export PreL' : PreL LC PP)
       (Export PRP : PretermReflectionPrimitives LC)
       (Export TR : TypingRules LC PP)
       (Export PRTR : PretermReflectionTypingRules LC PP PRP TR)
       (Export LA : PostL_Assumptions LC PP PRP TR)
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

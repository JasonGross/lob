Require Import Coq.Setoids.Setoid Coq.Classes.CMorphisms.
Require Export Lob.Notations Lob.WellTypedLobsTheoremStatement.
Require Export Lob.WellTypedLobsTheoremPreProof.

Axiom proof_admitted : False.
Ltac admit' := case proof_admitted.

Ltac do_shelve tac := tac; [ shelve | | ].

Local Infix "<->" := iffT : type_scope.

Module Type ContextPrimitives (Export LC : LobContext).
  Axiom weakenTerm : forall {Γ A B}, Term B -> Term (@weakenTyp Γ A B).
  Axiom tProd : forall {Γ} A, Typ (Γ ▻ A) -> Typ Γ.
  Notation "A ‘→’ B" := (tProd A%typ B%typ) : typ_scope.
  Axiom tLambda : forall {Γ A B}, @Term (Γ ▻ A) B -> Term (@tProd _ A B).
  Axiom weakenTyp1 : forall {Γ A B}, Typ (Γ ▻ B) -> Typ (Γ ▻ A ▻ (weakenTyp B)).
  Notation W1 := weakenTyp1.
  Notation W := weakenTyp.
  Axiom weakenTyp2 : forall {Γ A B C}, Typ (Γ ▻ B ▻ C) -> Typ (Γ ▻ A ▻ W B ▻ W1 C).
  Notation W2 := weakenTyp2.

  Axiom weakenTyp2_weakenTyp1 : forall {Γ A B C D},
                                  @Term (Γ ▻ A ▻ W B ▻ W1 C) (W2 (W D))
                                  -> @Term (Γ ▻ A ▻ W B ▻ W1 C) (W (W1 D)).
  Notation W2W1 := weakenTyp2_weakenTyp1.

  Axiom weakenTyp1_weakenTyp : forall {Γ A B C},
                                 @Term (Γ ▻ A ▻ W B) (W1 (W C))
                                 -> @Term (Γ ▻ A ▻ W B) (W (W C)).
  Notation W1W := weakenTyp1_weakenTyp.

  Axiom weakenTyp1_weakenTyp_inv
  : forall {Γ A B C},
      @Term (Γ ▻ A ▻ W B) (W (W C))
      -> @Term (Γ ▻ A ▻ W B) (W1 (W C)).
  Notation W1W' := weakenTyp1_weakenTyp_inv.

  Axiom weakenTyp1_weakenTyp1_weakenTyp
  : forall {Γ A B C T},
      @Term (Γ ▻ A ▻ B ▻ W (W C)) (W1 (W1 (W T)))
      -> @Term (Γ ▻ A ▻ B ▻ W (W C)) (W1 (W (W T))).
  Notation W1W1W := weakenTyp1_weakenTyp1_weakenTyp.

  Axiom weakenTyp_tProd : forall {Γ A B C},
                            Term (@weakenTyp Γ C (A ‘→’ B))
                            -> Term (@weakenTyp Γ C A ‘→’ W1 B).
  Axiom weakenTyp_tProd_inv
  : forall {Γ A B C},
      Term (@weakenTyp Γ C A ‘→’ W1 B)
      -> Term (@weakenTyp Γ C (A ‘→’ B)).
  Axiom weakenTyp_weakenTyp_tProd : forall {Γ A B C D},
                                      @Term (Γ ▻ C ▻ D) (W (W (A ‘→’ B)))
                                      -> @Term (Γ ▻ C ▻ D) (W (W A ‘→’ W1 B)).
  Axiom weakenTyp1_tProd : forall {Γ D A B C},
                             Term (@weakenTyp1 Γ C D (A ‘→’ B))
                             -> Term (@weakenTyp1 Γ C D A ‘→’ W2 B).
  Axiom tApp : forall {Γ A B}
                      (f : Term (@tProd Γ A B))
                      (x : Term A),
                 Term (B ‘’ x).
  Notation "f ‘’ₐ x" := (tApp f x) : term_scope.
  Axiom substTyp_weakenTyp1_Var0
  : forall {Γ A T},
      @Term (Γ ▻ A) (W1 T ‘’ ‘VAR₀’)
      -> @Term (Γ ▻ A) T.
  Notation SW1V := substTyp_weakenTyp1_Var0.
  Axiom weakenTyp_substTyp_tProd
  : forall {Γ T T' A B a},
      @Term (Γ ▻ T') (W (@tProd (Γ ▻ T) A B ‘’ a))
      -> @Term (Γ ▻ T') (W (@tProd Γ (A ‘’ a) (B ‘’₁ a))).
  Notation "WS∀" := weakenTyp_substTyp_tProd.
  Axiom substTyp2 : forall {Γ A B C}
                           (D : Typ (Γ ▻ A ▻ B ▻ C))
                           (a : Term A),
                      Typ (Γ ▻ substTyp B a ▻ substTyp1 C a).
  Notation "f ‘’₂ x" := (@substTyp2 _ _ _ _ f x) : typ_scope.
  Axiom substTyp1_tProd : forall {Γ T T' A B a},
                           Term (@tProd (Γ ▻ T ▻ T') A B ‘’₁ a)
                           -> Term (@tProd (Γ ▻ T' ‘’ a) (A ‘’₁ a) (B ‘’₂ a)).
  Notation "S₁∀" := substTyp1_tProd.
  Axiom substTyp3 : forall {Γ A B C D}
                           (E : Typ (Γ ▻ A ▻ B ▻ C ▻ D))
                           (a : Term A),
                      Typ (Γ ▻ substTyp B a ▻ substTyp1 C a ▻ substTyp2 D a).
  Notation "f ‘’₃ x" := (@substTyp3 _ _ _ _ _ f x) : typ_scope.
  Axiom substTyp2_tProd : forall {Γ T T' T'' A B a},
                           Term (@tProd (Γ ▻ T ▻ T' ▻ T'') A B ‘’₂ a)
                           -> Term (@tProd (Γ ▻ T' ‘’ a ▻ T'' ‘’₁ a) (A ‘’₂ a) (B ‘’₃ a)).
  Notation "S₂∀" := substTyp2_tProd.
  Axiom substTyp_weakenTyp
  : forall {Γ A B a},
      @Term Γ (@substTyp Γ A (@weakenTyp Γ A B) a) -> @Term Γ B.
  Notation SW := substTyp_weakenTyp.
  Axiom substTyp1_weakenTyp1
  : forall {Γ A B C a},
      @Term (Γ ▻ W B ‘’ a) ((@weakenTyp1 Γ A B C) ‘’₁ a) -> @Term (Γ ▻ B) C.
  Notation S₁W1 := substTyp1_weakenTyp1.
  Axiom substTyp_weakenTyp1_weakenTyp
  : forall {Γ T A B}
           {a : Term (W B)},
      @Term (Γ ▻ T) (W1 (W A) ‘’ a)
      -> @Term (Γ ▻ T) (W A).
  Notation SW1W := substTyp_weakenTyp1_weakenTyp.

  Axiom substTyp1_substTyp_weakenTyp2_weakenTyp
  : forall {Γ T' A B T}
           {a : @Term (Γ ▻ T') (W A)}
           {b : @Term (Γ ▻ T') (W1 B ‘’ a)},
      @Term (Γ ▻ T') (W2 (W T) ‘’₁ a ‘’ b)
      -> @Term (Γ ▻ T') (W1 T ‘’ a).

  Notation S₁₀W2W := substTyp1_substTyp_weakenTyp2_weakenTyp.

  Axiom substTyp1_substTyp_weakenTyp_inv
  : forall {Γ C T A} {a : @Term Γ C} {b : @Term Γ (T ‘’ a)},
      @Term Γ (A ‘’ a)
      -> @Term Γ (W A ‘’₁ a ‘’ b).

  Notation S₁₀W' := substTyp1_substTyp_weakenTyp_inv.

  Axiom substTyp1_substTyp_weakenTyp
  : forall {Γ C T A} {a : @Term Γ C} {b : @Term Γ (T ‘’ a)},
      @Term Γ (W A ‘’₁ a ‘’ b)
      -> @Term Γ (A ‘’ a).
  Notation S₁₀W := substTyp1_substTyp_weakenTyp.

  Axiom weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp_inv
  : forall {Γ A B C T T'}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (C ‘’₁ a ‘’ b)},
      @Term (Γ ▻ T') (W (T ‘’₁ a ‘’ b))
      -> @Term (Γ ▻ T') (W (W T ‘’₂ a ‘’₁ b ‘’ c)).

  Notation WS₂₁₀W' := weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp_inv.


  Axiom substTyp2_substTyp1_substTyp_weakenTyp
  : forall {Γ A B C T}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (C ‘’₁ a ‘’ b)},
      @Term Γ (W T ‘’₂ a ‘’₁ b ‘’ c)
      -> @Term Γ (T ‘’₁ a ‘’ b).

  Notation S₂₁₀W := substTyp2_substTyp1_substTyp_weakenTyp.

  Axiom weakenTyp_substTyp2_substTyp1_substTyp_tProd
  : forall {Γ T T' T'' T''' A B a b c},
      Term (@weakenTyp _ T''' (@tProd (Γ ▻ T ▻ T' ▻ T'') A B ‘’₂ a ‘’₁ b ‘’ c))
      -> Term (@tProd (Γ ▻ T''') (W (A ‘’₂ a ‘’₁ b ‘’ c)) (W1 (B ‘’₃ a ‘’₂ b ‘’₁ c))).
  Notation "WS₂₁₀∀" := weakenTyp_substTyp2_substTyp1_substTyp_tProd.

  Axiom substTyp3_substTyp2_substTyp1_substTyp_weakenTyp
  : forall {Γ A B C D T T'}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (C ‘’₁ a ‘’ b)}
           {d : @Term (Γ ▻ T') (W (D ‘’₂ a ‘’₁ b ‘’ c))},
      @Term (Γ ▻ T') (W1 (W T ‘’₃ a ‘’₂ b ‘’₁ c) ‘’ d)
      -> @Term (Γ ▻ T') (W (T ‘’₂ a ‘’₁ b ‘’ c)).

  Notation W1S₃₂₁₀W := substTyp3_substTyp2_substTyp1_substTyp_weakenTyp.

  Axiom weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp1
  : forall {Γ A B C T T'}
           {a : @Term Γ A}
           {b : Term (B ‘’ a)}
           {c : Term (C ‘’ a)},
      @Term (Γ ▻ T') (W (W1 T ‘’₂ a ‘’₁ b ‘’ S₁₀W' c))
      -> @Term (Γ ▻ T') (W (T ‘’₁ a ‘’ c)).

  Notation WS₂₁₀W1 := weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp1.

  Axiom substTyp1_substTyp_tProd
  : forall {Γ T T' A B a b},
      Term (@tProd (Γ ▻ T ▻ T') A B ‘’₁ a ‘’ b)
      -> Term (@tProd Γ (A ‘’₁ a ‘’ b) (B ‘’₂ a ‘’₁ b)).
  Notation "S₁₀∀" := substTyp1_substTyp_tProd.

  Axiom weakenTyp1_substTyp_weakenTyp1_inv
  : forall {Γ A T'' T' T}
           {a : @Term Γ A},
      @Term (Γ ▻ T'' ▻ W (T' ‘’ a)) (W1 (W (T ‘’ a)))
      -> @Term (Γ ▻ T'' ▻ W (T' ‘’ a)) (W1 (W T ‘’₁ a)).

  Notation W1S₁W' := weakenTyp1_substTyp_weakenTyp1_inv.

  Axiom weakenTyp1_substTyp_weakenTyp1
  : forall {Γ A T'' T' T}
           {a : @Term Γ A},
      @Term (Γ ▻ T'' ▻ W (T' ‘’ a)) (W1 (W T ‘’₁ a))
      -> @Term (Γ ▻ T'' ▻ W (T' ‘’ a)) (W1 (W (T ‘’ a))).

  Notation W1S₁W := weakenTyp1_substTyp_weakenTyp1.

  Axiom substTyp2_substTyp_substTyp_weakenTyp1_weakenTyp_weakenTyp
  : forall {Γ A} {T : Typ (Γ ▻ A)} {T' C B}
           {a : @Term Γ A}
           {b : @Term (Γ ▻ C ‘’ a) (B ‘’₁ a)}
           {c : @Term (Γ ▻ T') (W (C ‘’ a))},
      @Term (Γ ▻ T') (W1 (W (W T) ‘’₂ a ‘’ b) ‘’ c)
      -> @Term (Γ ▻ T') (W (T ‘’ a)).

  Notation S₂₀₀W1WW := substTyp2_substTyp_substTyp_weakenTyp1_weakenTyp_weakenTyp.

  Axiom weakenTyp_substTyp_substTyp_weakenTyp1
  : forall {Γ T' B A}
           {b : @Term Γ B}
           {a : @Term (Γ ▻ B) (W A)}
           {T : Typ (Γ ▻ A)},
      @Term (Γ ▻ T') (W (W1 T ‘’ a ‘’ b))
      -> @Term (Γ ▻ T') (W (T ‘’ (SW (a ‘’ b)))).
  Notation WS₀₀W1 := weakenTyp_substTyp_substTyp_weakenTyp1.

  Axiom weakenTyp_substTyp_substTyp_weakenTyp1_inv
  : forall {Γ T' B A}
           {b : @Term Γ B}
           {a : @Term (Γ ▻ B) (W A)}
           {T : Typ (Γ ▻ A)},
      @Term (Γ ▻ T') (W (T ‘’ (SW (a ‘’ b))))
      -> @Term (Γ ▻ T') (W (W1 T ‘’ a ‘’ b)).
  Notation WS₀₀W1' := weakenTyp_substTyp_substTyp_weakenTyp1_inv.
End ContextPrimitives.

Module TP
       (Export LC : LobContext)
       (Export CP : ContextPrimitives LC)
<: TermPrimitives LC.
  Notation W := weakenTyp.
  Definition weakenTerm : forall {Γ A B}, Term B -> Term (@weakenTyp Γ A B)
    := @weakenTerm.
  Notation w := weakenTerm.
  Definition tProd : forall {Γ} A, Typ (Γ ▻ A) -> Typ Γ
    := @tProd.
  Notation "A ‘→’ B" := (tProd A%typ B%typ) : typ_scope.
  Definition tLambda : forall {Γ A B}, @Term (Γ ▻ A) B -> Term (@tProd _ A B)
    := @tLambda.
  Notation "‘λ.’" := tLambda : term_scope.
  Definition weakenTyp1 : forall {Γ A B}, Typ (Γ ▻ B) -> Typ (Γ ▻ A ▻ (weakenTyp B))
    := @weakenTyp1.
  Notation W1 := weakenTyp1.
  Definition weakenTyp2 : forall {Γ A B C}, Typ (Γ ▻ B ▻ C) -> Typ (Γ ▻ A ▻ W B ▻ W1 C)
    := @weakenTyp2.
  Notation W2 := weakenTyp2.
  Definition weakenTyp_tProd : forall {Γ A B C},
                                 Term (@weakenTyp Γ C (A ‘→’ B))
                                 -> Term (@weakenTyp Γ C A ‘→’ W1 B)
    := @weakenTyp_tProd.
  Definition tApp : forall {Γ A B}
                      (f : Term (@tProd Γ A B))
                      (x : Term A),
                 Term (B ‘’ x)
    := @tApp.
  Notation "f ‘’ₐ x" := (tApp f x) : term_scope.
  Definition substTyp2 : forall {Γ A B C}
                           (D : Typ (Γ ▻ A ▻ B ▻ C))
                           (a : Term A),
                      Typ (Γ ▻ substTyp B a ▻ substTyp1 C a)
    := @substTyp2.
  Notation "f ‘’₂ x" := (@substTyp2 _ _ _ _ f x) : typ_scope.
  Definition substTyp3 : forall {Γ A B C D}
                                (E : Typ (Γ ▻ A ▻ B ▻ C ▻ D))
                                (a : Term A),
                           Typ (Γ ▻ substTyp B a ▻ substTyp1 C a ▻ substTyp2 D a)
    := @substTyp3.
  Notation "f ‘’₃ x" := (@substTyp3 _ _ _ _ _ f x) : typ_scope.
  Definition substTyp_weakenTyp
  : forall {Γ A B a},
      @Term Γ (@substTyp Γ A (@weakenTyp Γ A B) a) -> @Term Γ B
    := @substTyp_weakenTyp.
  Notation SW := substTyp_weakenTyp.
  Definition substTyp_weakenTyp1_weakenTyp
  : forall {Γ T A B}
           {a : Term (W B)},
      @Term (Γ ▻ T) (W1 (W A) ‘’ a)
      -> @Term (Γ ▻ T) (W A)
    := @substTyp_weakenTyp1_weakenTyp.
  Notation SW1W := substTyp_weakenTyp1_weakenTyp.
  Definition substTyp1_substTyp_weakenTyp_inv
  : forall {Γ C T A} {a : @Term Γ C} {b : @Term Γ (T ‘’ a)},
      @Term Γ (A ‘’ a)
      -> @Term Γ (W A ‘’₁ a ‘’ b)
    := @substTyp1_substTyp_weakenTyp_inv.
  Notation S₁₀W' := substTyp1_substTyp_weakenTyp_inv.
  Definition substTyp1_substTyp_weakenTyp
  : forall {Γ C T A} {a : @Term Γ C} {b : @Term Γ (T ‘’ a)},
      @Term Γ (W A ‘’₁ a ‘’ b)
      -> @Term Γ (A ‘’ a)
    := @substTyp1_substTyp_weakenTyp.
  Notation S₁₀W := substTyp1_substTyp_weakenTyp.
  Definition weakenTyp_substTyp2_substTyp1_substTyp_tProd
  : forall {Γ T T' T'' T''' A B a b c},
      Term (@weakenTyp _ T''' (@tProd (Γ ▻ T ▻ T' ▻ T'') A B ‘’₂ a ‘’₁ b ‘’ c))
      -> Term (@tProd (Γ ▻ T''') (W (A ‘’₂ a ‘’₁ b ‘’ c)) (W1 (B ‘’₃ a ‘’₂ b ‘’₁ c)))
    := @weakenTyp_substTyp2_substTyp1_substTyp_tProd.
  Notation "WS₂₁₀∀" := weakenTyp_substTyp2_substTyp1_substTyp_tProd.
  Definition substTyp3_substTyp2_substTyp1_substTyp_weakenTyp
  : forall {Γ A B C D T T'}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (C ‘’₁ a ‘’ b)}
           {d : @Term (Γ ▻ T') (W (D ‘’₂ a ‘’₁ b ‘’ c))},
      @Term (Γ ▻ T') (W1 (W T ‘’₃ a ‘’₂ b ‘’₁ c) ‘’ d)
      -> @Term (Γ ▻ T') (W (T ‘’₂ a ‘’₁ b ‘’ c))
    := @substTyp3_substTyp2_substTyp1_substTyp_weakenTyp.
  Notation W1S₃₂₁₀W := substTyp3_substTyp2_substTyp1_substTyp_weakenTyp.
  Definition weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp1
  : forall {Γ A B C T T'}
           {a : @Term Γ A}
           {b : Term (B ‘’ a)}
           {c : Term (C ‘’ a)},
      @Term (Γ ▻ T') (W (W1 T ‘’₂ a ‘’₁ b ‘’ S₁₀W' c))
      -> @Term (Γ ▻ T') (W (T ‘’₁ a ‘’ c))
    := @weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp1.
  Notation WS₂₁₀W1 := weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp1.
  Definition substTyp1_substTyp_tProd
  : forall {Γ T T' A B a b},
      Term (@tProd (Γ ▻ T ▻ T') A B ‘’₁ a ‘’ b)
      -> Term (@tProd Γ (A ‘’₁ a ‘’ b) (B ‘’₂ a ‘’₁ b))
    := @substTyp1_substTyp_tProd.
  Notation "S₁₀∀" := substTyp1_substTyp_tProd.
  Definition weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp_inv
  : forall {Γ A B C T T'}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (C ‘’₁ a ‘’ b)},
      @Term (Γ ▻ T') (W (T ‘’₁ a ‘’ b))
      -> @Term (Γ ▻ T') (W (W T ‘’₂ a ‘’₁ b ‘’ c))
    := @weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp_inv.
  Notation WS₂₁₀W' := weakenTyp_substTyp2_substTyp1_substTyp_weakenTyp_inv.
  Definition substTyp2_substTyp_substTyp_weakenTyp1_weakenTyp_weakenTyp
  : forall {Γ A} {T : Typ (Γ ▻ A)} {T' C B}
           {a : @Term Γ A}
           {b : @Term (Γ ▻ C ‘’ a) (B ‘’₁ a)}
           {c : @Term (Γ ▻ T') (W (C ‘’ a))},
      @Term (Γ ▻ T') (W1 (W (W T) ‘’₂ a ‘’ b) ‘’ c)
      -> @Term (Γ ▻ T') (W (T ‘’ a))
    := @substTyp2_substTyp_substTyp_weakenTyp1_weakenTyp_weakenTyp.
  Notation S₂₀₀W1WW := substTyp2_substTyp_substTyp_weakenTyp1_weakenTyp_weakenTyp.






  Definition substTyp_tProd : forall {Γ T A B a},
                                Term (@tProd (Γ ▻ T) A B ‘’ a)
                                -> Term (@tProd Γ (A ‘’ a) (B ‘’₁ a)).
  Proof.
    intros Γ T A B a x.
    eapply w in x.
    (eapply WS∀ in x).
    exact (SW (x ‘’ a)).
  Defined.
  Notation "S∀" := substTyp_tProd.
  Definition tProd_nd : forall {Γ}, Typ Γ -> Typ Γ -> Typ Γ
    := fun Γ A B => @tProd Γ A (W B).
  Notation "A ‘→'’ B" := (tProd_nd A%typ B%typ) : typ_scope.
  Definition tLambda_nd : forall {Γ A B},
                            @Term (Γ ▻ A) (W B) -> Term (A ‘→'’ B)
    := fun Γ A B b => @tLambda Γ A (W B) b.
  Notation "‘λ'.’" := tLambda_nd : term_scope.
  Definition tLambda_nd_anon : forall {Γ A B},
                            @Term Γ B -> Term (A ‘→'’ B)
    := fun Γ A B b => @tLambda Γ A (W B) (w b).
  Notation "‘λ''.’" := tLambda_nd_anon : term_scope.

  Definition untLambda : forall {Γ A B}, Term (@tProd _ A B) -> @Term (Γ ▻ A) B
    := fun Γ A B f
       => SW1V (weakenTyp_tProd (w f) ‘’ₐ ‘VAR₀’).

  Definition weakenTerm1 : forall {Γ A B C}, @Term (Γ ▻ B) C -> @Term (Γ ▻ A ▻ weakenTyp B) (@weakenTyp1 Γ A B C)
    := fun Γ A B C c
       => untLambda (weakenTyp_tProd (w (tLambda c)))%term.

  Notation w1 := weakenTerm1.

  Definition substTerm1 : forall {Γ A B C}
                                 (c : Term C)
                                 (a : Term A),
                            Term (@substTyp1 Γ A B C a)
    := fun Γ A B C c a => untLambda (S∀ (tLambda (tLambda c) ‘’ₐ a))%term.

  Notation "f ‘’₁ x" := (@substTerm1 _ _ _ _ f x) : term_scope.

  Definition substTerm2 : forall {Γ A B C D}
                                 (c : Term D)
                                 (a : Term A),
                            Term (@substTyp2 Γ A B C D a)
    := fun Γ A B C D c a =>
         untLambda (S₁∀ (untLambda (S∀ (tLambda (tLambda (tLambda c)) ‘’ₐ a))))%term.
  Notation "f ‘’₂ x" := (@substTerm2 _ _ _ _ _ f x) : term_scope.

  Definition substTerm3 : forall {Γ A B C D E}
                                 (e : Term E)
                                 (a : Term A),
                            Term (@substTyp3 Γ A B C D E a)
    := fun Γ A B C D E e a =>
         untLambda (S₂∀ (untLambda (S₁∀ (untLambda (S∀ (tLambda (tLambda (tLambda (tLambda e))) ‘’ₐ a))))))%term.
  Notation "f ‘’₃ x" := (@substTerm3 _ _ _ _ _ _ f x) : term_scope.

  Definition substTyp1_substTyp_weakenTyp_weakenTyp
  : forall {Γ T A B}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)},
      @Term Γ (W (W T) ‘’₁ a ‘’ b)
      -> @Term Γ T.
  Proof.
    intros Γ T A B a b x.
    apply S₁₀W, SW in x.
    exact x.
  Defined.

  Notation S₁₀WW := substTyp1_substTyp_weakenTyp_weakenTyp.

  Definition substTyp2_substTyp1_substTyp_weakenTyp_weakenTyp
  : forall {Γ A B C T}
           {a : @Term Γ A}
           {b : @Term Γ (B ‘’ a)}
           {c : @Term Γ (C ‘’₁ a ‘’ b)},
      @Term Γ (W (W T) ‘’₂ a ‘’₁ b ‘’ c)
      -> @Term Γ (T ‘’ a).
  Proof.
    intros Γ A B C T a b c x.
    apply S₂₁₀W, S₁₀W in x.
    exact x.
  Defined.
  Notation S₂₁₀WW := substTyp2_substTyp1_substTyp_weakenTyp_weakenTyp.

  Definition tApp_nd : forall {Γ A B},
                         Term (@tProd_nd Γ A B)
                         -> Term A
                         -> Term B
    := fun Γ A B f x => SW (@tApp Γ A (W B) f x).
  Notation "f ‘'’ₐ x" := (tApp_nd f x) : term_scope.

  Definition weakenTyp_tProd_nd : forall {Γ A B C},
                            Term (@weakenTyp Γ C (A ‘→'’ B))
                            -> Term (@weakenTyp Γ C A ‘→'’ W B).
  Proof.
    unfold tProd_nd.
    intros Γ A B C x.
    apply weakenTyp_tProd in x.
    refine (tLambda_nd _).
    refine (W1W (SW1V (weakenTyp_tProd (w x) ‘’ₐ ‘VAR₀’)))%term.
  Defined.

  Definition weakenTyp_tProd_nd_inv
  : forall {Γ A B C},
      Term (@weakenTyp Γ C A ‘→'’ W B)
      -> Term (@weakenTyp Γ C (A ‘→'’ B)).
  Proof.
    unfold tProd_nd.
    intros Γ A B C x.
    apply weakenTyp_tProd_inv.
    refine (tLambda (W1W' _)).
    refine (SW1V (weakenTyp_tProd (w x) ‘’ₐ ‘VAR₀’))%term.
  Defined.

  Definition weakenProd_nd : forall {Γ A B C},
                               Term (A ‘→'’ B)
                               -> Term (@weakenTyp Γ C A ‘→'’ W B)
    := fun Γ A B C x => weakenTyp_tProd_nd (w x).
  Notation "w→" := weakenProd_nd.

  Definition weakenProd : forall {Γ A B C},
                            Term (A ‘→’ B)
                            -> Term (@weakenTyp Γ C A ‘→’ W1 B)
    := fun Γ A B C x => weakenTyp_tProd (w x).
  Notation "w∀" := weakenProd.

  (*Definition weakenTyp_weakenTyp_tProd_nd
  : forall {Γ A B C D},
      @Term (Γ ▻ C ▻ D) (W (W (A ‘→'’ B)))
      -> @Term (Γ ▻ C ▻ D) (W (W A ‘→'’ W B)).
  Proof.
    unfold tProd_nd.
    intros Γ A B C D x.
    apply weakenTyp_weakenTyp_tProd, weakenTyp_tProd in x.
    apply weakenTyp_tProd_inv.
    refine (let x' := W1W1W (SW1V (weakenTyp_tProd (w x) ‘’ₐ ‘VAR₀’)) in _)%term.
    pose proof (tLambda_nd x') as x''.
    unfold tProd_nd in *.

    exact x''.
    Implicit Arguments Term [].


  Defined.

  Definition weaken_weakenProd_nd
  : forall {Γ A B C D},
      @Term Γ (A ‘→'’ B)
      -> @Term (Γ ▻ C ▻ D) (W (W A) ‘→'’ W (W B))
    := fun Γ A B C D x => w→ (w→ x).
  Notation "ww→" := weaken_weakenProd_nd.

  Definition weaken_weakenProd
  : forall {Γ A B C D},
      @Term Γ (A ‘→’ B)
      -> @Term (Γ ▻ C ▻ D) (W (W A) ‘→’ W1 (W1 B))
    := fun Γ A B C D x => weakenProd (weakenProd x).
  Notation "ww∀" := weaken_weakenProd.*)

  (*Definition VAR1
  : forall {Γ A B},
      @Term (Γ ▻ A ▻ B) (W (W A)).
  Proof.
    intros.
    refine (untLambda _).
    refine (tLambda_nd_anon ‘VAR₀’).
  Defined.

  Notation "‘VAR₁’" := VAR1.*)

  Definition weakenTyp_tProd_tProd_nd
  : forall {Γ A B C D},
      Term (@weakenTyp Γ D (A ‘→’ B ‘→'’ C))
      -> Term (@weakenTyp Γ D A ‘→’ W1 B ‘→'’ W1 C).
  Proof.
    intros Γ A B C D x.
    apply weakenTyp_tProd in x.
    refine (tLambda (tLambda (W2W1 (untLambda (weakenTyp1_tProd (SW1V (w∀ x ‘’ₐ ‘VAR₀’)))))))%term.
  Defined.

  Definition weakenProd_Prod_nd
  : forall {Γ A B C D},
      Term (A ‘→’ B ‘→'’ C)
      -> Term (@weakenTyp Γ D A ‘→’ W1 B ‘→'’ W1 C)
    := fun Γ A B C D x => weakenTyp_tProd_tProd_nd (w x).
  Notation "w∀→" := weakenProd_Prod_nd.

  Definition weakenTyp_tProd_nd_tProd_nd
  : forall {Γ A B C D},
      Term (@weakenTyp Γ D (A ‘→'’ B ‘→'’ C))
      -> Term (@weakenTyp Γ D A ‘→'’ W B ‘→'’ W C).
  Proof.
    intros Γ A B C D x.
    apply weakenTyp_tProd_nd in x.
    refine (tLambda _).
    refine (_ (weakenTyp_weakenTyp_tProd (w→ x ‘'’ₐ ‘VAR₀’) ))%term; intro x'; clear x.
    apply weakenTyp_tProd in x'.
    apply weakenTyp_tProd_inv.
    apply tLambda.
    refine (W1W1W _).
    exact (SW1V (w∀ x' ‘’ₐ ‘VAR₀’))%term.
  Defined.

  Definition weakenProd_nd_Prod_nd
  : forall {Γ A B C D},
      Term (A ‘→'’ B ‘→'’ C)
      -> Term (@weakenTyp Γ D A ‘→'’ W B ‘→'’ W C)
    := fun Γ A B C D x => weakenTyp_tProd_nd_tProd_nd (w x).
  Notation "w→→" := weakenProd_nd_Prod_nd.

  Definition substTyp2_substTyp1_substTyp_tProd
  : forall {Γ T T' T'' A B a b c},
      Term (@tProd (Γ ▻ T ▻ T' ▻ T'') A B ‘’₂ a ‘’₁ b ‘’ c)
      -> Term (@tProd Γ (A ‘’₂ a ‘’₁ b ‘’ c) (B ‘’₃ a ‘’₂ b ‘’₁ c)).
  Proof.
    intros Γ T T' T'' A B a b c x.
    exact (SW (weakenTyp_tProd_inv (WS₂₁₀∀ (w x)) ‘’ a))%term.
  Defined.
  Notation "S₂₁₀∀" := substTyp2_substTyp1_substTyp_tProd.

  Definition weakenTerm2 : forall {Γ A B C D}, @Term (Γ ▻ B ▻ C) D -> @Term (Γ ▻ A ▻ W B ▻ W1 C) (@weakenTyp2 Γ A B C D).
  Proof.
    intros Γ A B C D x.
    repeat apply tLambda in x.
    apply untLambda.
    (eapply w∀ in x).
    refine (weakenTyp1_tProd (w1 (SW1V (x ‘’ₐ ‘VAR₀’))))%term.
  Defined.
  Notation w2 := weakenTerm2.

  Definition substTyp_weakenTyp1_inv
  : forall {Γ A T' T}
           {a : @Term Γ A},
      @Term (Γ ▻ T' ‘’ a) (W (T ‘’ a))
      -> @Term (Γ ▻ T' ‘’ a) (W T ‘’₁ a).
  Proof.
    intros Γ A T' T a x.
    eapply w1 in x.
    eapply W1S₁W' in x.
    refine (S₁W1 (x ‘’₁ a))%term.
  Defined.
  Notation S₁W' := substTyp_weakenTyp1_inv.

  Definition substTyp_weakenTyp1
  : forall {Γ A T' T}
           {a : @Term Γ A},
      @Term (Γ ▻ T' ‘’ a) (W T ‘’₁ a)
      -> @Term (Γ ▻ T' ‘’ a) (W (T ‘’ a)).
  Proof.
    intros Γ A T' T a x.
    eapply w1 in x.
    eapply W1S₁W in x.
    refine (S₁W1 (x ‘’₁ a))%term.
  Defined.
  Notation S₁W := substTyp_weakenTyp1.

  Definition qfcomp_nd
  : forall {Γ A B C},
      @Term Γ (A ‘→'’ B)
      -> @Term Γ (B ‘→'’ C)
      -> @Term Γ (A ‘→'’ C).
  Proof.
    intros Γ A B C g f.
    apply tLambda.
    refine (w→ f ‘'’ₐ (w→ g ‘'’ₐ ‘VAR₀’))%term.
  Defined.
  Notation "f ‘∘’ g" := (qfcomp_nd g f) : term_scope.

  Definition substTyp_tProd_nd_tProd_nd
  : forall {Γ T A B C}
           {a : Term T},
      @Term Γ ((A ‘→'’ B ‘→'’ C) ‘’ a)
      -> @Term Γ ((A ‘’ a) ‘→'’ (B ‘’ a) ‘→'’ (C ‘’ a)).
  Proof.
    intros Γ T A B C a x.
    (apply S∀ in x).
    apply tLambda.
    apply weakenTyp_tProd_inv.
    apply tLambda.
    refine (W1S₁W (SW1V (w∀ (weakenTyp_tProd (weakenTyp_substTyp_tProd (S₁W (SW1V (w∀ x ‘’ₐ ‘VAR₀’))))) ‘’ₐ ‘VAR₀’)))%term.
  Defined.
  Notation "S→→" := substTyp_tProd_nd_tProd_nd.




  Definition substTyp_substTyp_weakenTyp1_inv_arr
  : forall {Γ B A}
           {b : @Term Γ B}
           {a : @Term (Γ ▻ B) (W A)}
           {T : Typ (Γ ▻ A)}
           {X},
      @Term Γ (T ‘’ (SW (a ‘’ b)) ‘→'’ X)
      -> @Term Γ (W1 T ‘’ a ‘’ b ‘→'’ X).
  Proof.
    intros Γ B A b a T X x.
    apply tLambda.
    refine (w→ x ‘'’ₐ WS₀₀W1 ‘VAR₀’)%term.
  Defined.
  Notation "S₀₀W1'→" := substTyp_substTyp_weakenTyp1_inv_arr.

  Definition substTyp_substTyp_weakenTyp1_arr_inv
  : forall {Γ B A}
           {b : @Term Γ B}
           {a : @Term (Γ ▻ B) (W A)}
           {T : Typ (Γ ▻ A)}
           {X},
      @Term Γ (X ‘→'’ T ‘’ (SW (a ‘’ b)))
      -> @Term Γ (X ‘→'’ W1 T ‘’ a ‘’ b).
  Proof.
    intros Γ B A b a T X x.
    apply untLambda in x.
    apply WS₀₀W1' in x.
    apply tLambda.
    exact x.
  Defined.
  Notation "S₀₀W1'←" := substTyp_substTyp_weakenTyp1_arr_inv.

  Definition substTyp_substTyp_weakenTyp1
  : forall {Γ B A}
           {b : @Term Γ B}
           {a : @Term (Γ ▻ B) (W A)}
           {T : Typ (Γ ▻ A)},
      @Term Γ (W1 T ‘’ a ‘’ b)
      -> @Term Γ (T ‘’ (SW (a ‘’ b)))
    := fun _ _ _ _ _ _ x => (SW (WS₀₀W1 (w x) ‘’ x))%term.
  Notation S₀₀W1 := substTyp_substTyp_weakenTyp1.

  Definition substTyp_substTyp_weakenTyp1_inv
  : forall {Γ B A}
           {b : @Term Γ B}
           {a : @Term (Γ ▻ B) (W A)}
           {T : Typ (Γ ▻ A)},
      @Term Γ (T ‘’ (SW (a ‘’ b)))
      -> @Term Γ (W1 T ‘’ a ‘’ b)
    := fun _ _ _ _ _ _ x => (SW (WS₀₀W1' (w x) ‘’ x))%term.
  Notation S₀₀W1' := substTyp_substTyp_weakenTyp1_inv.
End TP.

Module Type QuotedContextPrimitives
       (Import LC : LobContext)
       (Import CP : ContextPrimitives LC).
  Module Import TP' := TP LC CP.
  Axiom qtProd_nd
  : @Term (ε ▻ ‘Context’ ▻ ‘Typ’ ▻ W ‘Typ’) (W (W ‘Typ’)).
  Notation "‘tProd_nd’" := qtProd_nd.
  Notation "A ‘‘→'’’ B" := (S₂₁₀WW (‘tProd_nd’ ‘’₂ _ ‘’₁ A%typ ‘’ S₁₀W' B%typ))%term : typ_scope.
  Notation "A ‘‘→'’’ B" := (A ‘‘→'’’ B)%typ : term_scope.

  Axiom qtApp_nd
  : forall {Γ} {A : □ (‘Typ’ ‘’ Γ)} {B : □ (‘Typ’ ‘’ Γ)},
      □ (‘Term’ ‘’₁ Γ ‘’ (A ‘‘→'’’ B)
          ‘→'’ ‘Term’ ‘’₁ Γ ‘’ A
          ‘→'’ ‘Term’ ‘’₁ Γ ‘’ B).
  Notation "‘tApp_nd’" := qtApp_nd.
  Notation "f ‘‘'’’ₐ x" := (qtApp_nd ‘’₁ f ‘’ x)%term : term_scope.

  Axiom qquote_term : forall {A : Typ ε},
                        @Term ε (A ‘→'’ ‘Term’ ‘’₁ _ ‘’ ⌜ A ⌝%typ).
  Notation "‘quote_term’" := qquote_term : term_scope.

  Axiom qsigT : forall (T : Typ ε), Typ (ε ▻ T) -> Typ ε.
  Notation "‘sigT’" := qsigT.

  Axiom qprojT1 : forall {T : Typ ε} {P : Typ (ε ▻ T)}, □ (‘sigT’ T P ‘→'’ T).
  Notation "‘projT1’" := qprojT1.

  Axiom qprojT2 : forall {T : Typ ε} {P : Typ (ε ▻ T)}, @Term (ε ▻ ‘sigT’ T P) (W1 P ‘’ (w→ ‘projT1’ ‘'’ₐ ‘VAR₀’)).
  Notation "‘projT2’" := qprojT2.

  Axiom context_pick_if_rev
  : forall {P : Context -> Type}
           {Γ : Context}
           (dummy : P (ε ▻ ‘sigT’ ‘Context’ ‘Typ’))
           (val : P Γ),
      P (ε ▻ ‘sigT’ ‘Context’ ‘Typ’).

  Axiom context_pick_if_rev_refl
  : forall {P dummy val},
      @context_pick_if_rev P (ε ▻ ‘sigT’ ‘Context’ ‘Typ’) dummy val = val.

  Axiom qexistT : forall {T P} (x : Term T) (p : Term (P ‘’ x)), Term (‘sigT’ T P).
  Notation "‘existT’" := qexistT.

  Axiom qcontext_extend : @Term (ε ▻ ‘Context’ ▻ ‘Typ’) (W (W ‘Context’)).
  Notation "Γ ‘▻’ x" := (S₁₀WW (qcontext_extend ‘’₁ Γ%ctx ‘’ x%typ)%term) : term_scope.
  Notation "Γ ‘▻’ x" := (Γ ‘▻’ x)%term : context_scope.

  Axiom qsubstTyp
  : forall {Γ} {A : □ (‘Typ’ ‘’ Γ)},
      □ (‘Typ’ ‘’ (Γ ‘▻’ A)
          ‘→'’ ‘Term’ ‘’₁ Γ ‘’ A
          ‘→'’ ‘Typ’ ‘’ Γ).
  Notation "‘substTyp’" := qsubstTyp.
  Notation "f ‘‘’’ x" := (qsubstTyp ‘'’ₐ f ‘'’ₐ x)%term : term_scope.

  Axiom qcontext_pick_if
  : forall {P : Typ (ε ▻ ‘Context’)}
           (dummy : Term (P ‘’ quote_context (ε ▻ ‘sigT’ ‘Context’ ‘Typ’))),
      □ (‘Context’ ‘→’ P ‘→'’ W (P ‘’ ⌜ ε ▻ ‘sigT’ ‘Context’ ‘Typ’ ⌝%ctx)).

  Axiom Wquote_distr_qcontext_extend
  : forall {Γ T T'},
      @Term (ε ▻ T') (W (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝%ctx))
      <-> @Term (ε ▻ T') (W (‘Typ’ ‘’ (⌜ Γ ⌝ ‘▻’ ⌜ T ⌝)%ctx)).
  Notation "⌜W‘▻’⌝" := (fst Wquote_distr_qcontext_extend).
  Notation "⌜W‘◅’⌝" := (snd Wquote_distr_qcontext_extend).

  Definition quote_distr_qcontext_extend
  : forall {Γ T},
      □ (‘Typ’ ‘’ ⌜ Γ ▻ T ⌝%ctx)
      <-> □ (‘Typ’ ‘’ (⌜ Γ ⌝ ‘▻’ ⌜ T ⌝)%ctx).
  Proof.
    intros Γ T; split; intro x.
    { refine (SW ((fst Wquote_distr_qcontext_extend) (w x) ‘’ ‘ε’))%term. }
    { refine (SW ((snd Wquote_distr_qcontext_extend) (w x) ‘’ ‘ε’))%term. }
  Defined.
  Notation "⌜‘▻’⌝" := (fst quote_distr_qcontext_extend).
  Notation "⌜‘◅’⌝" := (snd quote_distr_qcontext_extend).

  Axiom qcontext_pick_if_refl_inv
  : forall {T dummy qqs},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜‘▻’⌝ ⌜ T ⌝%typ ‘‘’’ qqs)
             ‘‘→'’’
             (⌜‘▻’⌝ (S₁₀WW (substTyp_tProd (@qcontext_pick_if ‘Typ’ dummy ‘’ₐ ⌜ ε ▻ ‘sigT’ ‘Context’ ‘Typ’ ⌝%ctx) ‘’ₐ ⌜ T ⌝%typ))
                ‘‘’’ qqs))).
  Axiom qcontext_pick_if_refl
  : forall {T dummy qqs},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜‘▻’⌝ (S₁₀WW (substTyp_tProd (@qcontext_pick_if ‘Typ’ dummy ‘’ₐ ⌜ ε ▻ ‘sigT’ ‘Context’ ‘Typ’ ⌝%ctx) ‘’ₐ ⌜ T ⌝%typ))
              ‘‘’’ qqs)
             ‘‘→'’’
             (⌜‘▻’⌝ ⌜ T ⌝%typ ‘‘’’ qqs))).

  Axiom quote_typ_distr_tProd_nd
  : forall {H X},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ H ‘→'’ X ⌝%typ
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (⌜ H ⌝ ‘‘→'’’ ⌜ X ⌝)%typ).
  Notation "⌜→'⌝" := quote_typ_distr_tProd_nd.

  Axiom quote_typ_undistr_tProd_nd
  : forall {H X},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ (⌜ H ⌝ ‘‘→'’’ ⌜ X ⌝)%typ
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ H ‘→'’ X ⌝%typ).
  Notation "⌜←'⌝" := quote_typ_undistr_tProd_nd.

  Axiom qqfcomp_nd
  : forall {A B C},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ (A ‘‘→'’’ C)
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (C ‘‘→'’’ B)
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (A ‘‘→'’’ B)).
  Notation "g ‘‘∘’’ f" := (qqfcomp_nd ‘'’ₐ f ‘'’ₐ g)%term : term_scope.

  Axiom quote_distr_substTyp
  : forall {B A} {b : □ B},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (⌜ A ‘’ b ⌝ ‘‘→'’’ ⌜‘▻’⌝ ⌜ A ⌝%typ ‘‘’’ ⌜ b ⌝)).
  Notation "⌜‘’⌝" := quote_distr_substTyp.

  Axiom quote_undistr_substTyp
  : forall {B A} {b : □ B},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (⌜‘▻’⌝ ⌜ A ⌝%typ ‘‘’’ ⌜ b ⌝ ‘‘→'’’ ⌜ A ‘’ b ⌝)).
  Notation "⌜‘’⌝'" := quote_undistr_substTyp.

  Axiom qquote_term_under_app
  : forall {A} {f} {t : □ A},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (f ‘‘’’ ⌜ t ⌝ ‘‘→'’’ f ‘‘’’ (‘quote_term’ ‘'’ₐ t))).
  Notation "⌜⌜⌝⌝" := qquote_term_under_app.

  Axiom qquote_term_under_app_inv
  : forall {A} {f} {t : □ A},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (f ‘‘’’ (‘quote_term’ ‘'’ₐ t) ‘‘→'’’ f ‘‘’’ ⌜ t ⌝)).
  Notation "⌜⌜⌝⌝'" := qquote_term_under_app_inv.

  Axiom qbeta_nd_inv
  : forall {T A}
           {f : @Term (ε ▻ A) (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝%ctx))}
           {x : □ A}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝%typ)},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (((⌜‘▻’⌝ (SW (f ‘’ x))) ‘‘’’ y)
             ‘‘→'’’ ((‘λ'.’ (⌜W‘▻’⌝ f) ‘'’ₐ x) ‘‘’’ y))).

  Axiom qbeta_nd
  : forall {T A}
           {f : @Term (ε ▻ A) (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝%ctx))}
           {x : □ A}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝%typ)},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (((‘λ'.’ (⌜W‘▻’⌝ f) ‘'’ₐ x) ‘‘’’ y)
             ‘‘→'’’ ((⌜‘▻’⌝ (SW (f ‘’ x))) ‘‘’’ y))).

  Notation "‘β’" := qbeta_nd.
  Notation "‘β'’" := qbeta_nd_inv.

  Axiom beta_under_subst
  : forall {A B B'}
           {g : □ (A ‘→'’ B)}
           {x : □ A},
      □ (B' ‘’ SW (w→ g ‘'’ₐ ‘VAR₀’ ‘’ x))
      -> □ (B' ‘’ (g ‘'’ₐ x)).
  Notation β := beta_under_subst.

  Axiom beta_under_subst_inv
  : forall {A B B'}
           {g : □ (A ‘→'’ B)}
           {x : □ A},
      □ (B' ‘’ (g ‘'’ₐ x))
      -> □ (B' ‘’ SW (w→ g ‘'’ₐ ‘VAR₀’ ‘’ x)).
  Notation β' := beta_under_subst_inv.


  Axiom qsubstTerm_substTerm_weakenTerm1_S₂₀₀W1WW
  : forall {T' C B}
           {b : @Term ε (B ‘’ ‘ε’)}
           {c : @Term (ε ▻ T') (W (C ‘’ ‘ε’))}
           {d : @Term (ε ▻ C ‘’ ‘ε’ ▻ W B ‘’₁ ‘ε’) (W (W ‘Typ’) ‘’₂ ‘ε’)}
           {e : @Term ε T'},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ (SW (S₂₀₀W1WW (w1 (d ‘’ S₁W' (w b)) ‘’ c) ‘’ e))
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (S₂₁₀WW (d ‘’₁ SW (c ‘’ e) ‘’ S₁₀W' b))).
  Notation "‘ssw1’" := qsubstTerm_substTerm_weakenTerm1_S₂₀₀W1WW.

  Axiom qsubstTerm_substTerm_weakenTerm1_S₂₀₀W1WW_inv
  : forall {T' C B}
           {b : @Term ε (B ‘’ ‘ε’)}
           {c : @Term (ε ▻ T') (W (C ‘’ ‘ε’))}
           {d : @Term (ε ▻ C ‘’ ‘ε’ ▻ W B ‘’₁ ‘ε’) (W (W ‘Typ’) ‘’₂ ‘ε’)}
           {e : @Term ε T'},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ (S₂₁₀WW (d ‘’₁ SW (c ‘’ e) ‘’ S₁₀W' b))
          ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (SW (S₂₀₀W1WW (w1 (d ‘’ S₁W' (w b)) ‘’ c) ‘’ e))).
  Notation "‘ssw1'’" := qsubstTerm_substTerm_weakenTerm1_S₂₀₀W1WW_inv.

  Axiom qsubstTerm_qtApp_nd_qtApp_nd_distr
  : forall {T B C}
           {a : @Term ε (B ‘→'’ C ‘→'’ ‘Typ’ ‘’ ‘ε’)}
           {b : @Term ε (T ‘→'’ B)}
           {c : @Term ε (T ‘→'’ C)}
           {v : @Term ε T},
      (□ (‘Term’ ‘’₁ ‘ε’
           ‘’ ((SW ((w→→ a ‘'’ₐ (w→ b ‘'’ₐ ‘VAR₀’) ‘'’ₐ (w→ c ‘'’ₐ ‘VAR₀’) ‘’ v)))
                 ‘‘→'’’ (a ‘'’ₐ (b ‘'’ₐ v) ‘'’ₐ (c ‘'’ₐ v)))))%term.
  Notation "‘s→→’" := qsubstTerm_qtApp_nd_qtApp_nd_distr.

  Axiom qsubstTerm_qtApp_nd_qtApp_nd_undistr
  : forall {T B C}
           {a : @Term ε (B ‘→'’ C ‘→'’ ‘Typ’ ‘’ ‘ε’)}
           {b : @Term ε (T ‘→'’ B)}
           {c : @Term ε (T ‘→'’ C)}
           {v : @Term ε T},
      (□ (‘Term’ ‘’₁ ‘ε’
           ‘’ ((a ‘'’ₐ (b ‘'’ₐ v) ‘'’ₐ (c ‘'’ₐ v))
                 ‘‘→'’’ (SW ((w→→ a ‘'’ₐ (w→ b ‘'’ₐ ‘VAR₀’) ‘'’ₐ (w→ c ‘'’ₐ ‘VAR₀’) ‘’ v))))))%term.
  Notation "‘s←←’" := qsubstTerm_qtApp_nd_qtApp_nd_undistr.


  Axiom substTerm_distr_stuff
  : forall {B B' T}
           {f : □ (B ‘→’ B' ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝%ctx)))}
           {g : □ (‘sigT’ B B' ‘→'’ B)}
           {h : Term (CP.W1 B' ‘’ (w→ g ‘'’ₐ ‘VAR₀’))}
           {x : □ (‘sigT’ B B')}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝%typ)},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜‘▻’⌝
              (SW
                 (SW1W
                    (S₁₀W2W
                       (S∀ (weakenTyp1_tProd
                              (w1 (SW1V (w∀ f ‘’ₐ ‘VAR₀’)))
                              ‘’ (w→ g ‘'’ₐ ‘VAR₀’)) ‘’ₐ h)) ‘’ x)) ‘‘’’ y)
             ‘‘→'’’ ((⌜‘▻’⌝
                        (S₁₀WW
                           (S∀ (f ‘’ₐ (g ‘'’ₐ x)) ‘’ₐ β (S₀₀W1 (h ‘’ x))))) ‘‘’’ y)))%term.

  Axiom substTerm_undistr_stuff
  : forall {B B' T}
           {f : □ (B ‘→’ B' ‘→’ W (W (‘Typ’ ‘’ ⌜ ε ▻ T ⌝%ctx)))}
           {g : □ (‘sigT’ B B' ‘→'’ B)}
           {h : Term (CP.W1 B' ‘’ (w→ g ‘'’ₐ ‘VAR₀’))}
           {x : □ (‘sigT’ B B')}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝%typ)},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          (((⌜‘▻’⌝
               (S₁₀WW
                  (S∀ (f ‘’ₐ (g ‘'’ₐ x)) ‘’ₐ β (S₀₀W1 (h ‘’ x))))) ‘‘’’ y)
             ‘‘→'’’
             (⌜‘▻’⌝
                (SW
                   (SW1W
                      (S₁₀W2W
                         (S∀ (weakenTyp1_tProd
                                (w1 (SW1V (w∀ f ‘’ₐ ‘VAR₀’)))
                                ‘’ (w→ g ‘'’ₐ ‘VAR₀’)) ‘’ₐ h)) ‘’ x)) ‘‘’’ y)))%term.

  Axiom qexistT_iota_inv
  : forall {T A P}
           {x : □ A}
           {p : □ (P ‘’ x)}
           {f}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝%typ)},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜‘▻’⌝ (S₁₀WW (S∀ (f ‘’ₐ x) ‘’ₐ p)) ‘‘’’ y)
             ‘‘→'’’
             (⌜‘▻’⌝ (S₁₀WW (S∀ (f ‘’ₐ (‘projT1’ ‘'’ₐ ‘existT’ x p)) ‘’ₐ β (S₀₀W1 (‘projT2’ ‘’ ‘existT’ x p)))) ‘‘’’ y))).


  Axiom qexistT_iota
  : forall {T A P}
           {x : □ A}
           {p : □ (P ‘’ x)}
           {f}
           {y : □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ T ⌝%typ)},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’
          ((⌜‘▻’⌝ (S₁₀WW (S∀ (f ‘’ₐ (‘projT1’ ‘'’ₐ ‘existT’ x p)) ‘’ₐ β (S₀₀W1 (‘projT2’ ‘’ ‘existT’ x p)))) ‘‘’’ y)
             ‘‘→'’’ (⌜‘▻’⌝ (S₁₀WW (S∀ (f ‘’ₐ x) ‘’ₐ p)) ‘‘’’ y))).

  Axiom qidmap
  : forall {T},
      □ (‘Term’ ‘’₁ ‘ε’ ‘’ (T ‘‘→'’’ T)).
  Notation "‘idmap’" := qidmap.
End QuotedContextPrimitives.

Module LobMin
       (Import LC : LobContext)
       (Import LH : LobHypotheses LC)
       (Import CP : ContextPrimitives LC)
       (Import QCP : QuotedContextPrimitives LC CP).
  Module Import TP' := TP LC CP.
  Module Import QP <: QuotedPrimitives LC TP'.
    Include QCP.
    (*Definition qtProd_nd
    : @Term (ε ▻ ‘Context’ ▻ ‘Typ’ ▻ W ‘Typ’) (W (W ‘Typ’))
      := @qtProd_nd.
    Notation "‘tProd_nd’" := qtProd_nd.
    Notation "A ‘‘→'’’ B" := (S₂₁₀WW (‘tProd_nd’ ‘’₂ _ ‘’₁ A%typ ‘’ S₁₀W' B%typ))%term : typ_scope.
    Notation "A ‘‘→'’’ B" := (A ‘‘→'’’ B)%typ : term_scope.
    Definition qtApp_nd
    : forall {Γ} {A : □ (‘Typ’ ‘’ Γ)} {B : □ (‘Typ’ ‘’ Γ)},
        □ (‘Term’ ‘’₁ Γ ‘’ (A ‘‘→'’’ B)
            ‘→'’ ‘Term’ ‘’₁ Γ ‘’ A
            ‘→'’ ‘Term’ ‘’₁ Γ ‘’ B)
      := @qtApp_nd.
    Notation "‘tApp_nd’" := qtApp_nd.
    Notation "f ‘‘'’’ₐ x" := (qtApp_nd ‘’₁ f ‘’ x)%term : term_scope.
    Definition qquote_term : forall {A : Typ ε},
                               @Term ε (A ‘→'’ ‘Term’ ‘’₁ _ ‘’ ⌜ A ⌝%typ)
      := @qquote_term.
    Notation "‘quote_term’" := qquote_term : term_scope.
    Definition qsigT : forall (T : Typ ε), Typ (ε ▻ T) -> Typ ε
      := @qsigT.
    Notation "‘sigT’" := qsigT.
    Definition qexistT : forall {T P} (x : Term T) (p : Term (P ‘’ x)), Term (‘sigT’ T P)
      := @qexistT.
    Notation "‘existT’" := qexistT.
    Definition quote_sigma (Γv : { Γ : _ & Typ Γ }) : Term (‘sigT’ ‘Context’ ‘Typ’)
      := ‘existT’ ⌜ Γv.1 ⌝%ctx ⌜ Γv.2 ⌝%typ.
    Definition qcontext_extend : @Term (ε ▻ ‘Context’ ▻ ‘Typ’) (W (W ‘Context’))
      := @qcontext_extend.
    Notation "Γ ‘▻’ x" := (S₁₀WW (qcontext_extend ‘’₁ Γ ‘’ x%typ)%term) : term_scope.
    Notation "Γ ‘▻’ x" := (Γ ‘▻’ x)%term : context_scope.
    Definition qsubstTyp
    : forall {Γ} {A : □ (‘Typ’ ‘’ Γ)},
        □ (‘Typ’ ‘’ (Γ ‘▻’ A)
            ‘→'’ ‘Term’ ‘’₁ Γ ‘’ A
            ‘→'’ ‘Typ’ ‘’ Γ)
      := @qsubstTyp.
    Notation "‘substTyp’" := qsubstTyp.
    Notation "f ‘‘’’ x" := (qsubstTyp ‘'’ₐ f ‘'’ₐ x)%term : term_scope.
    Definition qqfcomp_nd
    : forall {A B C},
        □ (‘Term’ ‘’₁ ‘ε’ ‘’ (A ‘‘→'’’ C)
            ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (C ‘‘→'’’ B)
            ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (A ‘‘→'’’ B))
      := @qqfcomp_nd.
    Notation "g ‘‘∘’’ f" := (qqfcomp_nd ‘'’ₐ f ‘'’ₐ g)%term : term_scope.
    Definition quote_typ_distr_tProd_nd
    : forall {H X},
        □ (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ H ‘→'’ X ⌝%typ
            ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ (⌜ H ⌝ ‘‘→'’’ ⌜ X ⌝)%typ)
      := @quote_typ_distr_tProd_nd.
    Notation "⌜→'⌝" := quote_typ_distr_tProd_nd.
    Definition quote_typ_undistr_tProd_nd
    : forall {H X},
        □ (‘Term’ ‘’₁ ‘ε’ ‘’ (⌜ H ⌝ ‘‘→'’’ ⌜ X ⌝)%typ
            ‘→'’ ‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ H ‘→'’ X ⌝%typ)
      := @quote_typ_undistr_tProd_nd.
    Notation "⌜←'⌝" := quote_typ_undistr_tProd_nd.*)
    Definition context_pick_if
               {P : Context -> Type}
               {Γ : Context}
               (val : P Γ)
               (dummy : P (ε ▻ ‘sigT’ ‘Context’ ‘Typ’))
    : P (ε ▻ ‘sigT’ ‘Context’ ‘Typ’)
      := @context_pick_if_rev P Γ dummy val.
    Definition context_pick_if_refl
               {P val dummy}
    : @context_pick_if P (ε ▻ ‘sigT’ ‘Context’ ‘Typ’) val dummy = val
      := @context_pick_if_rev_refl P dummy val.


    Definition qcast : □ (‘sigT’ ‘Context’ ‘Typ’ ‘→'’ ‘Typ’ ‘’ (‘ε’ ‘▻’ ⌜ ‘sigT’ ‘Context’ ‘Typ’ ⌝))
      := (tLambda_nd (⌜W‘▻’⌝ (SW1W (S₁₀W2W (substTyp_tProd (weakenTyp1_tProd (w1 (SW1V (w∀ (@qcontext_pick_if ‘Typ’ ⌜ W (‘Typ’ ‘’ ‘ε’) ⌝%typ) ‘’ₐ ‘VAR₀’))) ‘’ (w→ ‘projT1’ ‘'’ₐ ‘VAR₀’)) ‘’ₐ ‘projT2’)))))%term.
    Notation "‘cast’" := qcast.

    Definition quote_sigma (Γv : { Γ : _ & Typ Γ }) : Term (‘sigT’ ‘Context’ ‘Typ’)
      := ‘existT’ ⌜ Γv.1 ⌝%ctx ⌜ Γv.2 ⌝%typ.



    Definition qcast_refl_app
    : forall {T}
             (qs := quote_sigma (ε ▻ ‘sigT’ ‘Context’ ‘Typ’; T)),
        □ (‘Term’ ‘’₁ ‘ε’ ‘’
            ((⌜ T ‘’ qs ⌝)
               ‘‘→'’’
               (‘cast’ ‘'’ₐ quote_sigma (ε ▻ ‘sigT’ ‘Context’ ‘Typ’; T)
                 ‘‘’’ (‘quote_term’ ‘'’ₐ qs)))).
    Proof.
      intros.
      refine (_ ‘‘∘’’ ⌜‘’⌝)%term.
      unfold qcast.
      refine (_ ‘‘∘’’ qcontext_pick_if_refl_inv)%term; shelve_unifiable.
      refine (_ ‘‘∘’’ ⌜⌜⌝⌝)%term; shelve_unifiable.
      refine (qbeta_nd_inv ‘‘∘’’ _)%term; shelve_unifiable.
      refine (substTerm_undistr_stuff ‘‘∘’’ _)%term; shelve_unifiable.
      unfold quote_sigma.
      refine (qexistT_iota_inv ‘‘∘’’ _)%term; shelve_unifiable.
      exact ‘idmap’.
    Defined.

    Notation "‘cast_refl’" := qcast_refl_app.

    Definition qcast_refl_app_inv
    : forall {T}
             (qs := quote_sigma (ε ▻ ‘sigT’ ‘Context’ ‘Typ’; T)),
        □ (‘Term’ ‘’₁ ‘ε’ ‘’
            ((‘cast’ ‘'’ₐ quote_sigma (ε ▻ ‘sigT’ ‘Context’ ‘Typ’; T)
               ‘‘’’ (‘quote_term’ ‘'’ₐ qs))
               ‘‘→'’’ (⌜ T ‘’ qs ⌝))).
    Proof.
      intros.
      refine (⌜‘’⌝' ‘‘∘’’ _)%term.
      unfold qcast.
      refine (qcontext_pick_if_refl ‘‘∘’’ _)%term; shelve_unifiable.
      refine (⌜⌜⌝⌝' ‘‘∘’’ _)%term; shelve_unifiable.
      refine (_ ‘‘∘’’ qbeta_nd)%term; shelve_unifiable.
      refine (_ ‘‘∘’’ substTerm_distr_stuff)%term; shelve_unifiable.
      unfold quote_sigma.
      refine (_ ‘‘∘’’ qexistT_iota)%term; shelve_unifiable.
      exact ‘idmap’.
    Defined.
    Notation "‘cast_refl'’" := qcast_refl_app_inv.


    Definition Conv0
    : forall {qH0 qX},
        @Term (ε ▻ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0)
              (W (‘Term’ ‘’₁ ‘ε’ ‘’ ⌜ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0 ‘→'’ qX ⌝%typ))
        -> @Term (ε ▻ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0)
                 (W
                    (‘Term’ ‘’₁ ‘ε’ ‘’ (⌜ ‘Term’ ‘’₁ ‘ε’ ‘’ qH0 ⌝ ‘‘→'’’ ⌜ qX ⌝)))
      := fun _ _ x => (w→ quote_typ_distr_tProd_nd ‘'’ₐ x)%term.

  End QP.

  Module Lob' := Lob LC LH TP' QP.
  Definition lob := Lob'.lob.
  Print Assumptions lob.
End LobMin.

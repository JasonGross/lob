{-# OPTIONS --without-K #-}
open import Relation.Binary.PropositionalEquality

{-# NON_TERMINATING #-}
undefined :     {A : Set}     A
undefined = undefined

cong   -dep :     {a b c} {A : Set a} {B : A     Set b} {C : Set c}
            (f : (x : A)     B x     C) {x y u v}     (H : x     y)     subst _ H u     v     f x u     f y v
cong   -dep f refl refl = refl

infixl 4 _,_
infix 5 _++
infix 5 ++_
infixl 10 _cw_

data Con : Set
data _++ : Con     Set

data Ty (   : Con) : Set
data Var :            Ty        Set
data Tm (   : Con) : Ty        Set

_   '_ :            Ty        Con
  ' :               ++

++_ :     {  }        ++     Con
_cw_ :     {  } A        ++     (      ' A) ++

_   _ :     {  } (   :    ++)     Ty (++   )        ++

lem-cw-   :                   ++   '   
lem-cw-  -++ :     {  } (   :    ++) X     ++ X cw   ' (++   )     ++ (       X)
lem-cw-  -++-2 :     {  } (   :    ++)     ++        ++   ' (++   )

W    :     {  } (   :    ++) (A : Ty   )     Ty (++   )     Ty (++ A cw   )
w    :     {  } (   :    ++) (B : Ty   ) {A}     Tm (++   ) A     Tm (++ B cw   ) (W       B A)
v    :     {  } (   :    ++) (B : Ty   ) {A}     Var (++   ) A     Var (++ B cw   ) (W       B A)

lem-cw-W    :     {  } (   :    ++) A X     ++ A cw (       X)     ++ (W       A X cw   ' (++ A cw   ))

lem-W   -1 :     {  } (   :    ++) A X     W    (  ' (++ A cw   )) (W       A X) (subst Ty (lem-cw-   _) (W       A X))     subst Ty (lem-cw-W    _ _ _) (W    (       X) A (subst Ty (lem-cw-  -++ _ _) (W    (  ' (++   )) X (subst Ty (lem-cw-  -++-2 _) X))))
lem-W   -2 :     {  } (   :    ++) A (B : Ty (++   )) X     W    (  ' (++ A cw   )) (W       A X) (subst Ty (lem-cw-   _) (W       A B))     subst Ty (lem-cw-W    _ _ _) (W    (       X) A (subst Ty (lem-cw-  -++ _ _) (W    (  ' (++   )) X (subst Ty (lem-cw-  -++-2 _) B))))

data Con where
      : Con
  _,_ :            Ty        Con

_   '_ = _,_

data _++ where
     :               ++
  _,_ :     {  } (   :    ++)     Ty (++   )        ++

_   _ = _,_
  ' =   

++       =   
++ (   , x) = ++    , x

A cw       =    (   , A)
A cw (   , x) = A cw    , W       A x

lem-cw-   =    _     refl
lem-cw-  -++ =    _ _     refl
lem-cw-  -++-2 =    _     refl
lem-cw-W    =    _ _ _     refl

data Ty (   : Con) where
  U : Ty   
--  El : Tm    U     Ty    -- this constructor causes problems for termination of weakening
           :     A     Ty (   , A)     Ty   
--           :     A     Ty (   , A)     Ty   

data Var where
  vz :     {   A}                 Var (   , A) (W    (     ) A A)
  vs :     {   A B}     Var    A     Var (   , B) (W    (     ) B A)

data Tm (   : Con) where
           :     {A B}     Tm (   , A) B     Tm    (         A B)
  var :     {A}     Var    A     Tm    A

-- W       A (El x) = El (w       A x)
-- W       A (         ty ty') =          (W       A ty) (W    (   , ty) A ty')

-- w       A (         tm) =          (w    (   , _) A tm)
-- w       A (var v) = var (v       A v)

W       A U = U
-- W       A (El x) = El (w       A x)
W       A (         ty ty') =          (W       A ty) (W    (   , ty) A ty')

w       A (         tm) =          (w    (   , _) A tm)
w       A (var v) = var (v       A v)

v    (     ) A v = vs v
v    (   , X) A vz = subst (   t     Var (++ A cw    , W       A X) t) (lem-W   -1 _ _ _) vz -- ACK!
v    (   , X) A (vs {A = B} v) = subst (   t     Var (++ A cw    , W       A X) t) (lem-W   -2 _ _ _ _) (vs (v       A v))

-- W    (  ' (++ A cw   )) (W       A X) (W       A X)     W    (       X) A (W    (  ' (++   )) X X)

{-lem-W   -2' :     {  } (   :    ++) A (X B : Ty (++   )) (B    : Ty (++    , B))
      subst (   z     Ty (++ A cw    , W       A X , z)) (lem-W   -2    A B X)
          (W    (  ' (++ A cw   ) , W       A B) (W       A X) (W    (   , B) A B   ))
        W    (       X , W    (  ' (++   )) X B) A (W    (  ' (++   ) , B) X B   )-}

subst-U-U :     {A : Set} {     ' : A} {f : A     Con} (H :          ')     subst (   z     Ty (f z)) H U     U
subst-U-U refl = refl

J :     {          } {A : Set    } {x : A} (P : (y : A)     x     y     Set       ) (k : P x refl) {y : A} (H : x     y)     P y H
J P k refl = k

subst-   :     {T : Set} {     ' : T} {f : T     Con} {X Y} (H :          ')     subst (   z     Ty (f z)) H (         X Y)              (subst (   z     Ty (f z)) H X) (J (     ' H     Ty (f   ' , subst (   z     Ty (f z)) H X)) Y H)
subst-   refl = refl

lem-W   -2    A U X = refl
lem-W   -2    A (         U U) X = refl
lem-W   -2    A (         (         Y Y   ) U) X = cong   -dep          (lem-W   -2    A (         Y Y   ) X) (subst-U-U (lem-W   -2    A (         Y Y   ) X))
lem-W   -2    A (         U (         Y    Y   )) X = cong   -dep (   Y    Y                 U (         Y    Y   )) helper {!!}
  where
    helper : W    (  ' (++ A cw   ) , W       A U) (W       A X) (W    (   , U) A Y   )    
               W    (       X , W    (  ' (++   )) X U) A (W    (  ' (++   ) , U) X Y   )
    helper = {!!}

    helper' : W    (  ' (++ {!!} cw {!!})) (W    {!!} {!!} {!!})
                (subst Ty (lem-cw-   (++ {!!} cw {!!})) (W    {!!} {!!} {!!}))     subst Ty (lem-cw-W    {!!} {!!} {!!})
                                                                                (W    ({!!}     {!!}) {!!}
                                                                                 (subst Ty (lem-cw-  -++ {!!} {!!})
                                                                                  (W    (  ' (++ {!!})) {!!} (subst Ty (lem-cw-  -++-2 {!!}) {!!}))))
    helper' = lem-W   -2 (       U) A {!!} {!!}
lem-W   -2    A (         (         Y Y   ) (         Y    Y   )) X = cong   -dep          (lem-W   -2    A (         Y Y   ) X) (trans (subst-   (lem-W   -2    A (         Y Y   ) X)) {!!})
{-lem-W   -2    A U X = refl
lem-W   -2    A (         B B   ) X = cong   -dep          (lem-W   -2    A B X) {!!} {-(trans (cong (subst (   z     Ty (++ A cw    , W       A X , z)) (lem-W   -2    A B X)) {!!})
                                                                 (trans helper {!lem-W   -2 ? A B    X!}))
  where helper : subst (   z     Ty (++ A cw    , W       A X , z)) (lem-W   -2    A B X) {!W    (  ' (++ A cw   ) , W       A B) (W       A X) (W    (   , B) A B   )!}
                       {!W    (       X , W    (  ' (++   )) X B) A (W    (  ' (++   ) , B) X B   )!}
        helper = {!!}-}-}

{-lem-W   -2'    A X U U = refl
lem-W   -2'    A X (         Y Y   ) U = {!!}
lem-W   -2'    A X Y (         Y    Y   ) = {!!}-}


lem-W   -1    A X = lem-W   -2    A X X{-
lem-W   -1    A (         X X   ) = cong   -dep          {!lem-W   -1    A !} {!!} {-
  where helper : W    (  ' (++          X X    cw {!!})) (W    {!!} (         X X   ) (_))
                   (subst Ty (lem-cw-   (++          X X    cw {!!})) (W    {!!} (         X X   ) (_)))
                      
                   subst Ty (lem-cw-W    {!!} (         X X   ) (_))
                   (W    ({!!}     _) (         X X   )
                    (subst Ty (lem-cw-  -++ {!!} (_))
                     (W    (  ' (++ {!!})) (_) (subst Ty (lem-cw-  -++-2 {!!}) (_)))))
        helper = lem-W   -1 {!!} (         X X   ) X-}
-}

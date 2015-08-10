{-# OPTIONS --without-K #-}
-- Rending the Program Runner
-- A proof of Lӧb′s theorem: quoted interpreters are inconsistent
-- Jason Gross

{- Title and some comments inspired by and drawn heavily from
   "Scooping the Loop Sniffer: A proof that the Halting Problem is
   undecidable", by Geoffrey K. Pullum
   (http://www.lel.ed.ac.uk/~gpullum/loopsnoop.html) -}

open import common

infixl 2 _▻_
infixl 3 _‘’_
infixr 1 _‘→’_

{- "Scooping the Loop Sniffer", with slight modifications for this
   code.

No general procedure for type-checking will do.
Now, I won’t just assert that, I’ll prove it to you.
I will prove that although you might work till you drop,
you cannot tell if computation will stop.

For imagine we have a procedure called P
that for specified input permits you to see
what specified source code, with all of its faults,
defines a routine that eventually halts.

You feed in your program, with suitable data,
and P gets to work, and a little while later
(in finite compute time) correctly infers
whether infinite looping behavior occurs.

If there will be no looping, then P prints out ‘Good.’
That means work on this input will halt, as it should.
But if it detects an unstoppable loop,
then P reports ‘Bad!’ — which means you’re in the soup.

Well, the truth is that P cannot possibly be,
because if you wrote it and gave it to me,
I could use it to set up a logical bind
that would shatter your reason and scramble your mind.

For a specified program, say ‶A″, one supplies,
the first step of this program called Q I devise
is to find out from P what’s the right thing to say
of the looping behavior of A run on ‶A″.

If P’s answer is ‘Bad!’, Q will suddenly stop.
But otherwise, Q will go back to the top,
and start off again, looping endlessly back,
till the universe dies and turns frozen and black.

And this program called Q wouldn’t stay on the shelf;
I would ask it to forecast its run on itself.
When it reads its own source code, just what will it do?
What’s the looping behavior of Q run on Q?

If P warns of infinite loops, Q will quit;
yet P is supposed to speak truly of it!
And if Q’s going to quit, then P should say ‘Good.’
Which makes Q start to loop! (P denied that it would.)

No matter how P might perform, Q will scoop it:
Q uses P’s output to make P look stupid.
Whatever P says, it cannot predict Q:
P is right when it’s wrong, and is false when it’s true!

I’ve created a paradox, neat as can be —
and simply by using your putative P.
When you posited P you stepped into a snare;
Your assumption has led you right into my lair.

So where can this argument possibly go?
I don’t have to tell you; I’m sure you must know.
A reductio: There cannot possibly be
a procedure that acts like the mythical P.

You can never find general mechanical means
for predicting the acts of computing machines;
it’s something that cannot be done. So we users
must find our own bugs. Our computers are losers! -}

{- Our program will act much like this Q, except that instead of saying that

  Q will go back to the top,
  and start off again, looping endlessly back,
  till the universe dies and turns frozen and black.

We would say something more like that

  Q will go back to the top,
  and ask for the output of A run on ‶A″,
  trusting P that execution will not run away.

Further more, we combine the type-checker and the interpreter; we show
there cannot be a well-typed quoted interpreter that interprets all
well-typed quoted terms directly, rather than having a separate phase
of type-checking.  Morally, they should be equivalent. -}

{- We start off by defining Contexts, Types, and Terms which are
well-typed by construction.

We will prove that assuming Lӧb′s theorem is consistent in a minimal
representation, and doesn′t require anything fancy to support it in a
model of the syntax.  Thus any reasonable syntax, which has a model,
will also have a model validating Lӧb′s theorem.

This last part is informal; it′s certainly conceivable that something
like internalized parametricity, which needs to do something special
with each constructor of the language, won't be able to do anything
with the quotation operator.

There's a much longer formalization of Lӧb′s theorem in this
repository which just assumes a quotation operator, and proves Lӧb′s
theorem by constructing it (though to build a quine, we end up needing
to decide equality of Contexts, which is fine); the quotation operator
is, in principle, definable, by stuffing the constructors of the
syntax into an initial context, and building up the quoted terms by
structural recursion.  This would be even more painful, though, unless
there′s a nice way to give specific quoted terms.

Now, down to business. -}

mutual
  -- Contexts are utterly standard
  data Context : Set where
    ε : Context
    _▻_ : (Γ : Context) → Type Γ → Context

  -- Types have standard substituition and non-dependent function
  -- types.
  data Type : Context → Set where
    _‘’_ : ∀ {Γ A} → Type (Γ ▻ A) → Term {Γ} A → Type Γ
    _‘→’_ : ∀ {Γ} → Type Γ → Type Γ → Type Γ
  -- We also require that there be a quotation of ‶Type ε″ (called
  -- ‘Typeε’), and a quotation of ‶Term ε″ (called ‘□’)
    ‘Typeε’ : Type ε
    ‘□’ : Type (ε ▻ ‘Typeε’)
  -- We don′t really need quoted versions of ⊤ and ⊥, but they are
  -- useful stating a few things after the proof of Lӧb′s theorem
    ‘⊤’ : ∀ {Γ} → Type Γ
    ‘⊥’ : ∀ {Γ} → Type Γ
  -- Note that you can add whatever other constructors to this data
  -- type you would like;

  data Term : {Γ : Context} → Type Γ → Set where
  -- We require the existence of a function (in the ambient language)
  -- that takes a type in the empty context, and returns the quotation
  -- of that type.
    ⌜_⌝ : Type ε → Term {ε} ‘Typeε’
  -- Finally, we assume Lӧb′s theorem; we will show that this syntax
  -- has a model.
    Lӧb : ∀ {X} → Term {ε} (‘□’ ‘’ ⌜ X ⌝ ‘→’ X) → Term {ε} X
  -- This is not strictly required, just useful for showing that some
  -- type is inhabited.
    ‘tt’ : ∀ {Γ} → Term {Γ} ‘⊤’

{- ‶□ T″ is read ‶T is provable″ or ‶T is inhabited″ or ‶the type of
syntactic terms of the syntactic type T″ or ‶the type of quoted terms
of the quoted type T″. -}

□ : Type ε → Set _
□ = Term {ε}

mutual
  {- Having an inhabitant of type ‶the interpretation of a given
  Context″ is having an inhabitant of the interpretation of every type
  in that Context.  If we wanted to represent more universes, we could
  sprinkle lifts and lowers, and it would not cause us trouble.  They
  are elided here for simplicity. -}
  Context⇓ : (Γ : Context) → Set
  Context⇓ ε = ⊤
  Context⇓ (Γ ▻ T) = Σ (Context⇓ Γ) (Type⇓ {Γ} T)

  -- Substitution and function types are interpreted standardly.
  Type⇓ : {Γ : Context} → Type Γ → Context⇓ Γ → Set
  Type⇓ (T ‘’ x) Γ⇓ = Type⇓ T (Γ⇓ , Term⇓ x Γ⇓)
  Type⇓ (A ‘→’ B) Γ⇓ = Type⇓ A Γ⇓ → Type⇓ B Γ⇓
  -- ‘Typeε’ is, unsurprisingly, interpreted as Type ε, the type of
  -- syntactic types in the empty context.
  Type⇓ ‘Typeε’ Γ⇓ = Type ε
  -- ‘□’ expects Term of Type ‘Typeε’ as the last element of the
  -- context, and represents the type of Terms of that Type.  We take
  -- the (already-interpreted) last element of the Context, and feed
  -- it to Term {ε}, to get the Set of Terms of that Type.
  Type⇓ ‘□’ Γ⇓ = Term {ε} (Σ.proj₂ Γ⇓)
  -- The rest of the interpreter, for types not formally needed in
  -- Lӧb′s theorem.
  Type⇓ ‘⊤’ Γ⇓ = ⊤
  Type⇓ ‘⊥’ Γ⇓ = ⊥

  Term⇓ : ∀ {Γ : Context} {T : Type Γ} → Term T → (Γ⇓ : Context⇓ Γ) → Type⇓ T Γ⇓
  -- Unsurprisingly, we interpret the quotation of a given source code
  -- as the source code itself.  (Defining the interpretation of
  -- quotation is really trivial.  Defining quotation itself is much
  -- tricker.)  Note that it is, I believe, essential, that every Type
  -- be quotable.  Otherwise Lӧb′s theorem cannot be internalized in
  -- our syntactic representation, and will require both being given
  -- both a type, and syntax which denotes to that type.
  Term⇓ ⌜ x ⌝ Γ⇓ = x
  -- Now, the interesting part.  Given an interpreter (P in the poem,
  -- □‘X’→X in this code), we validate Lӧb′s theorem (Q run on Q) by
  -- running the interpreter on ... Q run on Q!  It takes a bit of
  -- thinking to wrap your head around, but the types line up, and
  -- it′s beautifully simple.
  Term⇓ (Lӧb □‘X’→X) Γ⇓ = Term⇓ □‘X’→X Γ⇓ (Lӧb □‘X’→X)
  -- Inhabiting ⊤
  Term⇓ ‘tt’ Γ⇓ = tt

⌞_⌟ : Type ε → Set _
⌞ T ⌟ = Type⇓ T tt

‘¬’_ : ∀ {Γ} → Type Γ → Type Γ
‘¬’ T = T ‘→’ ‘⊥’

-- With our interpreter, we can chain Lӧb′s theorem with itself: if we
-- can prove that ‶proving ‘X’ is sufficient to make ‘X’ true″, then
-- we can already inhabit X.
lӧb : ∀ {‘X’} → □ (‘□’ ‘’ ⌜ ‘X’ ⌝ ‘→’ ‘X’) → ⌞ ‘X’ ⌟
lӧb f = Term⇓ (Lӧb f) tt

-- We can thus prove that it′s impossible to prove that contradictions
-- are unprovable.
incompleteness : ¬ □ (‘¬’ (‘□’ ‘’ ⌜ ‘⊥’ ⌝))
incompleteness = lӧb

-- We can also prove that contradictions are, in fact, unprovable.
soundness : ¬ □ ‘⊥’
soundness x = Term⇓ x tt

-- And we can prove that some things are provable, namely, ‘⊤’
non-emptyness : Σ (Type ε) (λ T → □ T)
non-emptyness = ‘⊤’ , ‘tt’

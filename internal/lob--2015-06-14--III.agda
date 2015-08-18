module lob--2015-06-14--III where


data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}

record Σ {X : Set} (F : X → Set) : Set where
  constructor _,_
  field fst : X
        snd : F fst


data ⊤ : Set where
  unit : ⊤

data Tree (X : Set) : Set where
  br : Tree X → Tree X → Tree X
  leaf : X → Tree X

indtree : {X : Set} → (P : Tree X → Set)
        → ((s t : Tree X) → P s → P t → P (br s t))
        → ((x : X) → P (leaf x))
        → (t : Tree X) → P t
indtree P b l (br s t) = b s t (indtree P b l s) (indtree P b l t)
indtree P b l (leaf x) = l x


data Preterm : Set where
  type : ℕ → Preterm
  pi : Preterm → Preterm → Preterm
  sig : Preterm → Preterm → Preterm
  bot : Preterm
  top : Preterm
  unit : Preterm
  var : ℕ → Preterm
  lam : Preterm → Preterm → Preterm
  app : Preterm → Preterm → Preterm
  tree : Preterm → Preterm
  br : Preterm → Preterm → Preterm → Preterm
  leaf : Preterm → Preterm → Preterm
  ind : Preterm → Preterm → Preterm → Preterm → Preterm → Preterm

‘λ→’ = lam

data _::_ : Preterm → Preterm → Set where
  ::type : (ℓ : ℕ) → type ℓ :: type (suc ℓ)
  -- ...

□ : Preterm → Set
□ T = Σ \(t : Preterm) → t :: T


num : ℕ → Preterm
num 0 = leaf top unit
num (suc n) = br top unit (num n)

data List (X : Set) : Set where
  nil : List X
  _,_ : X → List X → List X

infixr 1 _,_

list : List Preterm → Preterm
list nil = leaf top unit
list (x , xs) = br top x (list xs)

cons : ℕ → List Preterm → Preterm
cons n xs = br top (num n) (list xs)

‘type’ : Preterm → Preterm
‘type’ n = cons 0 (n , nil)

‘pi’ : Preterm → Preterm → Preterm
‘pi’ x f = cons 1 (x , f , nil)

‘sig’ : Preterm → Preterm → Preterm
‘sig’ x f = cons 2 (x , f , nil)

‘bot’ : Preterm
‘bot’ = cons 3 nil

‘top’ : Preterm
‘top’ = cons 4 nil

‘unit’ : Preterm
‘unit’ = cons 5 nil

‘var’ : Preterm → Preterm
‘var’ n = cons 6 (n , nil)

‘lam’ : Preterm → Preterm → Preterm
‘lam’ t b = cons 7 (t , b , nil)

‘app’ : Preterm → Preterm → Preterm
‘app’ f x = cons 8 (f , x , nil)

‘tree’ : Preterm → Preterm
‘tree’ x = cons 9 (x , nil)

‘br’ : Preterm → Preterm → Preterm → Preterm
‘br’ x l r = cons 10 (x , l , r , nil)

‘leaf’ : Preterm → Preterm → Preterm
‘leaf’ x y = cons 11 (x , y , nil)

‘ind’ : Preterm → Preterm → Preterm → Preterm → Preterm → Preterm
‘ind’ x p b l t = cons 12 (x , p , b , l , t , nil)


‘Preterm’ : Preterm
‘Preterm’ = tree top

‘Preterm’::type₀ : ‘Preterm’ :: type 0
‘Preterm’::type₀ = {!!}

‘□’ : Preterm
‘□’ = {!!}

_‘→’_ : Preterm → Preterm → Preterm
A ‘→’ B = pi A {!!}

quot : Preterm → Preterm
quot (type n) = ‘type’ (num n)
quot (pi x f) = ‘pi’ (quot x) (quot f)
quot (sig x f) = ‘sig’ (quot x) (quot f)
quot bot = ‘bot’
quot top = ‘top’
quot unit = ‘unit’
quot (var n) = ‘var’ (num n)
quot (lam x b) = ‘lam’ (quot x) (quot b)
quot (app f x) = ‘app’ (quot f) (quot x)
quot (tree x) = ‘tree’ (quot x)
quot (br x l r) = ‘br’ (quot x) (quot l) (quot r)
quot (leaf x y) = ‘leaf’ (quot x) (quot y)
quot (ind x p b l t) = ‘ind’ (quot x) (quot p) (quot b) (quot l) (quot t)


‘quot’ : Preterm
‘quot’ = {!!}

‘‘→’’ : Preterm
‘‘→’’ = {!!}

⌜_⌝ = quot

_‘’_ = app

infixl 1 _‘’_

postulate
  X        : Set
  ‘X’       : Preterm
  ‘X’::type₀ : ‘X’ :: type 0

App : {‘A’ ‘B’ : Preterm}
      → □ (‘A’ ‘→’ ‘B’)
      → □ ‘A’
      → □ ‘B’
App □‘A→B’ □‘A’ = {!!}

‘App’ : Preterm
‘App’ = {!!}


Quot : {‘T’ : Preterm}
       → □ ‘T’
       → □ (‘□’ ‘’ ⌜ ‘T’ ⌝)
Quot □T = {!!}

‘Quot’ : Preterm
‘Quot’ = {!!}


‘L₀’ : Preterm
‘L₀’ = (‘λ→’ ‘Preterm’ ((‘app’ ⌜ ‘□’ ⌝ (‘app’ (var 0) (‘quot’ ‘’ (var 0)))) ‘’ ‘‘→’’ ‘’ ⌜ ‘X’ ⌝ ))

L : Preterm
L = (λ (h : Preterm) → (app ‘□’ (app h (⌜ h ⌝))) ‘→’ ‘X’) ‘L₀’

‘L’ = app ‘L₀’ ⌜ ‘L₀’ ⌝


Conv : □ (‘□’ ‘’ ⌜ L ⌝) → □ (‘□’ ‘’ ‘L’)
Conv = {!!}

‘Conv’ : Preterm
‘Conv’ = {!!}


postulate
  f    : □ ‘X’ → X
  ‘f’  : Preterm
  d‘f’ : ‘f’ :: (app ‘□’ (quot ‘X’) ‘→’ ‘X’)

y : X
y = (λ (ℓ : □ L) → f (App ℓ (Conv (Quot ℓ))))
      ( ‘λ→’ (‘□’ ‘’ ‘L’) (‘f’ ‘’ (‘App’ ‘’ (var 0) ‘’ (‘Conv’ ‘’ (‘Quot’ ‘’ var 0))))
      , {!!})

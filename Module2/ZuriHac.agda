open import Agda.Builtin.Nat hiding (_+_; _*_; _<_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Int 
-- open import Agda.Builtin.List

data Greeting : Set where
  hello : Greeting
  goodbye : Greeting


greet : Greeting
greet = hello


f : Greeting → Greeting
f = λ x → x

_+_ : Nat → Nat → Nat 
zero + n = n 
(suc m) + n = suc (m + n)

infixr 10 _+_



maximum : Nat → Nat → Nat 
maximum zero y = y 
maximum (suc x) zero = suc x 
maximum (suc x) (suc y) = suc (maximum x y)


{-# NON_TERMINATING #-}
h : Bool -> Bool 
h x = h x



-- Hidden arguments
id : {A : Set} → A → A
id x = x 

id' : (A : Set) → A → A 
id' A x = x 


-- If then else as a function
if_then_else_ : {A : Set} → Bool → A → A -> A 
if true then x else y = x 
if false then x else y = y

-- test : Nat → Nat 
-- test x = if (x ≤ 9000) then 0 else 42 


-- Polymorphic datatypes
data List (A : Set) : Set where 
  [] : List A 
  _::_ : A → List A → List A   
infixr 5 _::_

exampleList : List Nat 
exampleList = 1 :: 2 :: 3 :: []

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- Tuple type
data _×_ (A B : Set) : Set where 
  _,_ : A → B → A × B 

fst : {A B : Set} → A × B → A 
fst (x , y) = x 

snd : {A B : Set} → A × B → B  
snd (x , y) = y



-- dependent types 

-- data Food : Set where 
--   pizza : Food 
--   cake : Food 
--   bread : Food 

data Flavour : Set where 
  cheesy : Flavour 
  chocolatey : Flavour 

data Food : Flavour → Set where 
  pizza : Food cheesy 
  cake : Food chocolatey
  bread : {f : Flavour} → Food f 


amountOfCheese : Food cheesy → Nat 
amountOfCheese pizza = 100 
amountOfCheese bread = 20


-- Vectors 

data Vec (A : Set) : Nat → Set where 
  [] : Vec A 0 
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)


myVec1 : Vec Nat 4 
myVec1 = 1 :: 2 :: 3 :: 4 :: [] 

myVec2 : Vec Nat 0
myVec2 = [] 

myVec3 : Vec (Bool → Bool) 1 
myVec3 =  id :: [] 

myVec4 : Vec Nat (2 + 2)
myVec4 = 1 :: 2 :: 3 :: 4 :: [] 


length : {A : Set} {n : Nat} → Vec A n → Nat
length [] = zero
length (x :: xs) = 1 + (length xs)

-- Dependent functions
zeroes : (n : Nat) → Vec Nat n 
zeroes zero = [] 
zeroes (suc n) = 0 :: zeroes n 

zeroes3 = zeroes 3


mapVec : {A B : Set} {n : Nat} → (A → B) → Vec A n → Vec B n 
mapVec _ [] = [] 
mapVec f (x :: xs) = (f x) :: (mapVec f xs)


-- Safe head and tail functions 

head : ∀ {A : Set} {n : Nat} → Vec A (suc n) → A 
head (x :: xs) = x 

tail : ∀ {A : Set} {n : Nat} → Vec A (suc n) → Vec A n 
tail (x :: xs) = xs


-- A safe lookup 

data Fin : Nat → Set where 
  zero : {n : Nat} → Fin (suc n)
  suc : {n : Nat} → Fin n → Fin (suc n)

zero3 one3 two3 : Fin 3 
zero3 = zero 
one3 = suc zero 
two3 = suc (suc zero)

noFinZero : {A : Set} → Fin 0 → A 
noFinZero () 


lookupVec : {A : Set} {n : Nat} → Vec A n → Fin n -> A  
lookupVec (x :: xs) zero = x 
lookupVec (x :: xs) (suc i) = lookupVec xs i 


testLookupVec = lookupVec myVec1 (suc zero)


-- The Curry-Howard Correspondence

-- a type that expresses that a given number n is even

data IsEven : Nat → Set where 
  e-zero : IsEven zero 
  e-suc2 : {n : Nat} → IsEven n → IsEven (suc (suc n))

6-is-even : IsEven 6 
6-is-even = e-suc2 (e-suc2 (e-suc2 e-zero))

-- 7-is-not-even : IsEven 7 → ⊥ 
-- 7-is-not-even (e-suc2 (e-suc2 (e-suc2 ())))

double : Nat → Nat 
double zero = zero 
double (suc m) = suc (suc (double m))

double-even : (n : Nat) -> IsEven (double n)
double-even zero = e-zero 
double-even (suc m) = e-suc2 (double-even m)


-- Induction in Agda 

-- proof : (n : Nat) → P n 
-- proof zero = ... 
-- proof (suc n) = ...


-- identity type 
data _≡_ {A : Set} : A → A → Set where 
  refl : {x : A} → x ≡ x 

one-plus-one : (1 + 1) ≡ 2 
one-plus-one = refl 

test₁ : length (42 :: []) ≡ 1
test₁ = refl 

test₂ : length (mapVec (1 +_) (0 :: 1 :: 2 :: [])) ≡ 3
test₂ = refl


-- Proving correctness of functions 

not : Bool → Bool 
not false = true 
not true = false

not-not : (b : Bool) → (not (not b) ≡ b)
not-not false = refl 
not-not true = refl


-- Pattern matching on refl 

castVec : {A : Set} {m n : Nat} → (m ≡ n) → Vec A m → Vec A n 
castVec refl xs = xs 


sym : {A : Set} {x y : A} → (x ≡ y) → (y ≡ x)
sym refl = refl 


cong : {A B : Set} {x y : A} → (f : A → B) → (x ≡ y) → (f x ≡ f y)
cong f refl = refl 


-- Equational reasoning in Agda 

[_] : {A : Set} → A → List A 
[ x ] = x :: [] 

reverse : {A : Set} → List A → List A 
reverse [] = [] 
reverse (x :: xs) = reverse xs ++ [ x ]  

-- Prove that reverse [ x ] = [ x ]

reverse-singleton : {A : Set} → (x : A) → (reverse [ x ] ≡ [ x ])
reverse-singleton x = refl

-- Equational reasoning + induction 

add-n-zero : (n : Nat) → (n + zero) ≡ n 
add-n-zero zero = refl 
add-n-zero (suc x) = cong suc (add-n-zero x)


-- Application 1: functor laws 
-- fmap id = id 
-- fmap (f . g) = fmap f . fmap g 


-- Application 3: Verifying a compiler 
-- comp-exec-eval : (e : Expr) → exec (comp e) [] ≡ [ eval e ]

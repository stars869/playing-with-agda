module Module1.PropositionsAsTypes where 

open import Agda.Builtin.Nat hiding (_<_; _-_)
open import Agda.Builtin.Bool 


-- 2.1 Propositions as types 
-- dependent types. 

-- 2.1.2 the equality type 
data _≡_ {A : Set} (x : A) : A -> Set where 
    refl : x ≡ x

-- Agda is able to simply compute this: 
11+4≡fifteen : (11 + 4) ≡ 15
-- 11+4≡fifteen =  {!  !}
11+4≡fifteen = refl 

{-
11+3≡fifteen : (11 + 3) ≡ 15
11+3≡fifteen = {!  !}
-}


data ⊥ : Set where 
data ⊤ : Set where 
    tt : ⊤


_≤_ : Nat → Nat → Set 
zero ≤ n = ⊤ 
suc m ≤ zero = ⊥
suc m ≤ suc n = m ≤ n 

zeroIsLessThanOrEqualTo100 : 0 ≤ 100
zeroIsLessThanOrEqualTo100 = tt 


-- Stric inequality 
_<_ : Nat -> Nat -> Set 
_ < zero = ⊥
zero < suc _ = ⊤
suc m < suc n = m < n   


-- A type-safe subtraction
_-_ : (m : Nat) → (n : Nat) → {p : n ≤ m} → Nat 
(m - zero) {tt} = m 
(zero - suc n) {()}
(suc m - suc n) {p} = (m - n) {p}
infixr 50 _-_

5minus3equals2 : (5 - 2) {tt} ≡ 3
5minus3equals2 = refl


-- 2.1.4 know length of vector at compile-time
data Vec (A : Set) : Nat -> Set where 
  [] : Vec A 0
  _::_ : {m : Nat} -> (a : A) → Vec A m → Vec A (1 + m)
infixr 5 _::_ 

take : ∀ {A length} -> (n : Nat) -> Vec A length -> {p : n ≤ length} -> Vec A n 
take zero v = [] 
take (suc m) (a :: v) {p} = a :: take m v {p}


concat : ∀ {A m n} -> Vec A m -> Vec A n -> Vec A (m + n)
concat [] v2 = v2 
concat (a :: v1) v2 = a :: concat v1 v2 


lookup : ∀ {A : Set} {length : Nat} -> Vec A length -> (index : Nat) -> {p : index < length} -> A 
lookup (a :: v) zero {p} = a 
lookup (a :: v) (suc n) {p} = lookup v n {p} 


-- Constructing a singleton
[_] : ∀ {A : Set} -> A -> Vec A 1 
[ a ] = a :: []


rightIndex : let 
  v : Vec Nat 4 
  v = 4 :: 5 :: 6 :: 7 :: []
  in lookup v 2 {tt} ≡ 6
rightIndex = refl


map : ∀ {A B : Set} -> {n : Nat} -> (A -> B) -> Vec A n -> Vec B n
map f [] = []
map f (x :: xs) = (f x) :: (map f xs)


pwise : ∀ {A B : Set} -> {n : Nat} -> Vec (A -> B) n -> Vec A n -> Vec B n 
pwise [] [] = [] 
pwise (f :: fs) (x :: xs) = (f x) :: (pwise fs xs)


replicate : ∀ {A n} -> A -> Vec A n 
replicate {n = zero} a = [] 
replicate {n = suc _} a = a :: (replicate a)


transpose : ∀ {A m n} -> Vec (Vec A n) m -> Vec (Vec A m) n 
transpose [] = replicate [] 
transpose (as :: ass) = pwise (pwise (replicate _::_) as) (transpose ass)


-- A proof showing transpose works
transposeWorks : ∀ {A : Set} {one two thr : A} -> transpose 
  (
    (one :: one :: one :: []) ::
    (two :: two :: two :: []) ::
    (thr :: thr :: thr :: []) :: [] 
  ) ≡
  (
    (one :: two :: thr :: []) :: 
    (one :: two :: thr :: []) :: 
    (one :: two :: thr :: []) :: []
  )
transposeWorks = refl


zipWith : ∀ {A B C n} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n 
zipWith f [] [] = [] 
zipWith f (a :: as) (b :: bs) = (f a b) :: (zipWith f as bs)


-- more dependent types 
record ∑ (A : Set) (B : (a : A) -> Set) : Set where 
  constructor _,_
  field 
    proj₁ : A 
    proj₂ : B proj₁ 

-- A function from booleans to types 
NatIfFalse,ListOfTopIfTrue : ∀ {n} -> Bool -> Set 
NatIfFalse,ListOfTopIfTrue false = Nat 
NatIfFalse,ListOfTopIfTrue {n} true = Vec ⊤ n 

dependentProd : ∀ {n} -> ∑ Bool (NatIfFalse,ListOfTopIfTrue {n})
dependentProd = false , 3

dependentProd₂ : ∑ Bool NatIfFalse,ListOfTopIfTrue
dependentProd₂ = true , (tt :: tt :: tt :: [])


-- dependentFunction : {A B : Set} -> (a : Nat) -> if 1 ≡ᵇ a then Vec Bool 2 else ⊤
-- dependentFunction zero = tt 
-- dependentFunction (suc zero) = true :: false :: [] 
-- dependentFunction (suc (suc x)) = tt 


-- The type/set of naturals greater than 5
GreaterThan5 : Set 
GreaterThan5 = ∑ Nat (λ n -> 5 < n)

valGreaterThan5 : GreaterThan5
valGreaterThan5 = 7 , tt 
{- 
valGreaterThan5₂ : GreaterThan5
valGreaterThan5₂ = 3 , {! type of hole: ⊥. Impossible to produce! !}
-}

GreaterThan : (n : Nat) -> Set 
GreaterThan n = ∑ Nat (λ m -> n < m)

nine : GreaterThan 7 
nine = 9 , tt 

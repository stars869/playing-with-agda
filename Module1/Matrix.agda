module Module1.Matrix where 

import Agda.Builtin.Nat as Nat 
open import Agda.Builtin.Nat hiding (_+_; _*_; zero)
open import Agda.Builtin.Bool 
open import Module1.PropositionsAsTypes


_ℕ≤ᵇ_ : Nat -> Nat -> Bool 
_ℕ≤ᵇ_ Nat.zero _ = true
_ℕ≤ᵇ_ (suc m) Nat.zero = false 
_ℕ≤ᵇ_ (suc m) (suc n) = m ℕ≤ᵇ n 


-- 3.1 Records and instance arguments: Agda's typeclasses 
record Num (C : Set) : Set where 
  field 
    _+_ : C -> C -> C 
    _*_ : C -> C -> C 

    zero : C 
    one : C 

    _≤ᵇ_ : C -> C -> Bool     
  infixl 19 _≤ᵇ_
  infixl 20 _+_ 
  infixl 21 _*_ 


open Num {{...}}


-- 3.2 Declaring instances 
numNat : Num Nat 
Num._+_ numNat = Nat._+_
Num._*_ numNat = Nat._*_
Num.zero numNat = 0 
Num.one numNat = 1 
Num._≤ᵇ_ numNat = _ℕ≤ᵇ_

instance 
  numNatInstance : Num Nat 
  numNatInstance = numNat 



-- 3.3 The matrix type and its functions

record Matrix (A : Set) (rows cols : Nat) : Set where 
  constructor 𝕄
  field 
    values : Vec (Vec A cols) rows 
open Matrix 


_+ᴹ_ : ∀ {A r c} {{numA : Num A}} -> Matrix A r c -> Matrix A r c -> Matrix A r c 
_+ᴹ_ (𝕄 m₁) (𝕄 m₂) = 𝕄 (zipWith (zipWith _+_) m₁ m₂)
infixl 29 _+ᴹ_

_*ᴹ_ : ∀ {A r c p} {{numA : Num A}} -> Matrix A r c -> Matrix A c p -> Matrix A r p 
_*ᴹ_ {A = A} (𝕄 m₁) (𝕄 m₂) = 𝕄 (map (λ row -> map (λ col -> sum (zipWith _*_ row col)) (transpose m₂)) m₁)
  where 
    sum : {a : Nat} -> Vec A a -> A 
    sum [] = zero 
    sum (x :: xs) = x + (sum xs)
infixl 30 _*ᴹ_


vecToColumnMatrix : ∀ {A} {n : Nat} -> Vec A n -> Matrix A n 1
vecToColumnMatrix v = 𝕄 (map (λ x -> [ x ]) v)

vecToRowMatrix : ∀ {A} {n : Nat} -> Vec A n -> Matrix A 1 n 
vecToRowMatrix v = 𝕄 [ v ]

_ᵀ : ∀ {A r c} -> Matrix A r c -> Matrix A c r
(𝕄 m) ᵀ = 𝕄 (transpose m)
infixl 45 _ᵀ

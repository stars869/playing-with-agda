module Introduction.Syntax where 

open import Agda.Builtin.Nat 
open import Agda.Builtin.Bool

-- 1.1 Sum types and values
-- constructors don't need to be uppercased
data Three : Set where 
    one : Three 
    two : Three 
    three : Three 

valueOfThree : Three 
valueOfThree = one 

valueOfThree₂ : Three 
valueOfThree₂ = two 


-- 1.2 Haskell's Either
data Either (A : Set) (B : Set) : Set where 
    left : A → Either A B 
    right : B → Either A B 

valueOfEither : {A : Set} → Either Nat A 
valueOfEither = left 10 


-- 1.3 Product types and values 
record Six : Set where 
    constructor myconst
    field 
        oneOf3 : Three
        oneOf2 : Bool

valueOfSix : Six 
valueOfSix = myconst three false



-- 1.4 Haskell's tuple 
record Pair (A : Set) (B : Set) : Set where 
    constructor pair 
    field
        proj₁ : A 
        proj₂ : B 

valueOfPair : Pair Nat Bool 
valueOfPair = pair 10 false 



-- 1.5 Functions, pattern matching
addTwoNumbers : Nat → Nat → Nat 
addTwoNumbers n m = n + m 

addThree : Nat → Three → Nat
addThree n one = n + 1
addThree n two = n + 2 
addThree n three = n + 3



-- 1.6 More syntactic things: let and where blocks, lambdas, mixfix operation
-- addThis_toThat_butOnlyIf_and_otherwisePickOne : Nat → Nat → Bool → Bool → Nat
-- addThis m toThat n butOnlyIf cond1 and cond2 otherwisePickOne = let 
--     cond1-and-cond2 = cond1 ^ cond2 
--     in if cond1-and-cond2 
--         then m + n 
--         else chosen cond1 cond2 
--       where chosen : Bool → Bool → Nat 
--             chosen c1 c2 whith c1 ∨ c2 
--             ... | false = m 
--             ... | true = n 

-- fifteen : Nat 
-- fifteen = addThis 15 toThat 5 butOnlyIf true and (5 <ᵇ 10) otherwisePickOne 

addFifteen : Nat → Nat 
addFifteen = λ n → addTwoNumbers n 15
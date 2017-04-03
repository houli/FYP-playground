module HungarianMatrixProof

import Data.Matrix
import Data.Vect.Quantifiers

%default total

public export
HungarianMatrix : (n : Nat) -> {auto p : n `GT` Z} -> Type
HungarianMatrix Z {p = LTEZero} impossible
HungarianMatrix Z {p = (LTESucc _)} impossible
HungarianMatrix (S k) {p = (LTESucc x)} = Matrix (S k) (S k) Int

columns : HungarianMatrix (S n) -> HungarianMatrix (S n)
columns = transpose

vectMin' : Ord a => a -> Vect n a -> a
vectMin' x [] = x
vectMin' x (y :: ys) with (compare x y)
  vectMin' x (y :: ys) | GT = vectMin' y ys
  vectMin' x (y :: ys) | EQ = vectMin' y ys
  vectMin' x (y :: ys) | LT = vectMin' x ys

vectMin : Ord a => Vect (S n) a -> a
vectMin (x :: xs) = vectMin' x xs

||| If we have a function to show `x` being in `zs` implies `x` being in `as`
||| and we can show `x` is in `y :: zs` then we can show `x` is in `y :: as`
congElem : (Elem x zs -> Elem x as) -> Elem x (y :: zs) -> Elem x (y :: as)
congElem _ Here = Here
congElem f (There later) = There (f later)

vectMinElem' : Ord a => (x : a) -> (ys : Vect n a) -> Elem (vectMin' x ys) (x :: ys)
vectMinElem' x [] = Here
vectMinElem' x (y :: ys) with (compare x y)
  vectMinElem' x (y :: ys) | GT = There (vectMinElem' y ys)
  vectMinElem' x (y :: ys) | EQ = There (vectMinElem' y ys)
  vectMinElem' x (y :: ys) | LT = congElem There (vectMinElem' x ys)

vectMinElem : Ord a => (xs : Vect (S n) a) -> Elem (vectMin xs) xs
vectMinElem (x :: xs) = vectMinElem' x xs

doSub' : Vect n Int -> Int -> Vect n Int
doSub' [] _ = []
doSub' (x :: xs) min = x - min :: doSub' xs min

doSub : Vect (S n) Int -> Int -> Vect (S n) Int
doSub xs min = doSub' xs min

||| Idris doesn't provide dependent integer elimination
||| This proof is taken as a basic postulate about integers
postulate minusSelfZero : {x : Int} -> x - x = 0

doSubElem0' : (x : Int) -> Elem min xs -> Elem 0 (doSub' xs min)
doSubElem0' x Here {min} = rewrite minusSelfZero {x = min} in Here
doSubElem0' x (There later) = There (doSubElem0' x later)

||| Subtracting the minimum from a row guarantees there is a `0` in the row
doSubElem0 : (xs : Vect (S n) Int) -> Elem min xs -> Elem 0 (doSub xs min)
doSubElem0 (min :: xs) Here = rewrite minusSelfZero {x = min} in Here
doSubElem0 (x :: xs) (There later) = There (doSubElem0' x later)

subSmallest' : Vect (S n) Int -> Vect (S n) Int
subSmallest' xs = doSub xs (vectMin xs)

||| Given a proof procedure for an element of a vector and a vector, create a
||| vector (All) of proofs for each element of the vector
proofMap : {P : a -> Type} -> ((x : a) -> P x) -> (xs : Vect n a) -> All P xs
proofMap _ [] = []
proofMap f (x :: xs) = f x :: proofMap f xs

||| Proving with the `Functor` interface `map` was too opaque?
||| Had to write my own version of `map` for `Vect`
myMap : (a -> b) -> Vect n a -> Vect n b
myMap _ [] = []
myMap f (x :: xs) = f x :: myMap f xs

subSmallest : HungarianMatrix (S n) -> HungarianMatrix (S n)
subSmallest xs = myMap subSmallest' xs

subSmallest'Elem0 : (xs : Vect (S n) Int) -> Elem 0 (subSmallest' xs)
subSmallest'Elem0 xs = doSubElem0 xs (vectMinElem xs)

||| Subtracting the minimum from all rows guarantees there is a `0` in any row
subSmallestAnyElem0 : (xs : HungarianMatrix (S n)) -> Any (Elem 0) (subSmallest xs)
subSmallestAnyElem0 (x :: xs) = Here (subSmallest'Elem0 x)

subSmallestAllElem0' : All (\x => Elem 0 (subSmallest' x)) xs -> All (Elem 0) (myMap subSmallest' xs)
subSmallestAllElem0' [] = []
subSmallestAllElem0' (prf :: prfs) = prf :: subSmallestAllElem0' prfs

||| Subtracting the minimum from all rows guarantees there is a `0` in all rows
subSmallestAllElem0 : (xs : HungarianMatrix (S n)) -> All (Elem 0) (subSmallest xs)
subSmallestAllElem0 xs = let prfs = proofMap {P = \z => Elem 0 (subSmallest' z)} subSmallest'Elem0 xs in
                         subSmallestAllElem0' prfs

||| Subtracting the minimum from all columns guarantees there is a `0` in all columns
subSmallestAllElem0Columns : (xs : HungarianMatrix (S n)) -> All (Elem 0) (subSmallest (columns xs))
subSmallestAllElem0Columns xs = subSmallestAllElem0 (columns xs)

step1 : HungarianMatrix (S n) -> (ys : HungarianMatrix (S n) ** All (Elem 0) ys)
step1 xs = (subSmallest xs ** subSmallestAllElem0 xs)

step2 : (xs : HungarianMatrix (S n) ** All (Elem 0) xs) -> (ys : HungarianMatrix (S n) ** All (Elem 0) ys)
step2 (xs ** _) = let ys = subSmallest $ columns xs in
                  (ys ** subSmallestAllElem0Columns xs)

export
hungarianMethod : HungarianMatrix (S n) -> HungarianMatrix (S n)
hungarianMethod xs = transpose (fst (step2 (step1 xs)))

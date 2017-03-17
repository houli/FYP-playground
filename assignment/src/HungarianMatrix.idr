module HungarianMatrix

import Data.Matrix

%default total
%access public export

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

subSmallest' : Vect (S n) Int -> Vect (S n) Int
subSmallest' xs = map (flip (-) $ (vectMin xs)) xs

subSmallest : HungarianMatrix (S n) -> HungarianMatrix (S n)
subSmallest xs = map subSmallest' xs

step1 : HungarianMatrix (S n) -> HungarianMatrix (S n)
step1 xs = subSmallest xs

step2 : HungarianMatrix (S n) -> HungarianMatrix (S n)
step2 xs = transpose $ subSmallest $ columns xs

module HungarianMatrix

import Data.Matrix

%default total
%access public export

||| A proof that some element is found in a matrix
data MatElem : a -> Matrix n m a -> Type where
     Here : MatElem x ((x :: ys) :: xs)
     There : (later : MatElem x xs) -> MatElem x (y::xs)

HungarianMatrix : (n : Nat) -> {auto p : n `GT` Z} -> Type
HungarianMatrix Z {p = LTEZero} impossible
HungarianMatrix Z {p = (LTESucc _)} impossible
HungarianMatrix (S k) {p = (LTESucc x)} = Matrix (S k) (S k) Int

columns : HungarianMatrix (S n) -> HungarianMatrix (S n)
columns = transpose

vectMin' : Ord a => a -> Vect n a -> a
vectMin' x [] = x
vectMin' x (y :: ys) = case compare x y of
                         GT => vectMin' y ys
                         _  => vectMin' x ys

vectMin : Ord a => Vect (S n) a -> a
vectMin (x :: xs) = vectMin' x xs

subSmallest' : Vect (S n) Int -> Vect (S n) Int
subSmallest' xs = let sub = vectMin xs in
  map (flip (-) $ sub) xs

subSmallest : HungarianMatrix (S n) -> HungarianMatrix (S n)
subSmallest xs = map subSmallest' xs

step1 : HungarianMatrix (S n) -> HungarianMatrix (S n)
step1 xs = subSmallest xs

step2 : HungarianMatrix (S n) -> HungarianMatrix (S n)
step2 xs = transpose $ subSmallest $ columns xs

step1Proof : HungarianMatrix (S n) -> (xs : HungarianMatrix (S n) ** MatElem 0 xs)
step1Proof xs = (subSmallest xs ** ?prf)

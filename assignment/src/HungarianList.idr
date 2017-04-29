module HungarianList

%default total

public export
Matrix : Type -> Type
Matrix a = List (List a)

public export
HungarianMatrix : Type
HungarianMatrix = Matrix Int

columns : Matrix a -> Matrix a
columns = transpose

listMin' : Ord a => a -> List a -> a
listMin' x [] = x
listMin' x (y :: ys) with (compare x y)
  listMin' x (y :: ys) | GT = listMin' y ys
  listMin' x (y :: ys) | EQ = listMin' y ys
  listMin' x (y :: ys) | LT = listMin' x ys

partial
listMin : Ord a => List a -> a
listMin (x :: xs) = listMin' x xs

partial
subSmallest : HungarianMatrix -> HungarianMatrix
subSmallest [] = []
subSmallest (x :: xs) = map (flip (-) $ (listMin x)) x :: subSmallest xs

partial
step1 : HungarianMatrix -> HungarianMatrix
step1 xs = subSmallest xs

partial
step2 : HungarianMatrix -> HungarianMatrix
step2 xs = transpose $ subSmallest $ columns xs

partial
export
hungarianMethod : HungarianMatrix -> HungarianMatrix
hungarianMethod xs = step2 (step1 xs)

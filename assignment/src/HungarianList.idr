module HungarianList

%default total
%access public export

columns : List (List a) -> List (List a)
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
subSmallest : List (List Int) -> List (List Int)
subSmallest [] = []
subSmallest (x :: xs) = map (flip (-) $ (listMin x)) x :: subSmallest xs

partial
step1 : List (List Int) -> List (List Int)
step1 xs = subSmallest xs

partial
step2 : List (List Int) -> List (List Int)
step2 xs = transpose $ subSmallest $ columns xs

partial
hungarianMethod : List (List Int) -> List (List Int)
hungarianMethod xs = step2 (step1 xs)

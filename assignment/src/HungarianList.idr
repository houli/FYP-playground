module HungarianList

%default total
%access public export

columns : List (List a) -> List (List a)
columns = transpose

listMin' : Ord a => a -> List a -> a
listMin' x [] = x
listMin' x (y :: ys) = case compare x y of
                         GT => listMin' y ys
                         _  => listMin' x ys

partial
listMin : Ord a => List a -> a
listMin (x :: xs) = listMin' x xs

partial
subSmallest : List (List Int) -> List (List Int)
subSmallest [] = []
subSmallest ([] :: xs) = [] :: subSmallest xs
subSmallest (x :: xs) = let sub = listMin x in
  map (flip (-) $ sub) x :: subSmallest xs

partial
step1 : List (List Int) -> List (List Int)
step1 xs = subSmallest xs

partial
step2 : List (List Int) -> List (List Int)
step2 xs = transpose $ subSmallest $ columns xs
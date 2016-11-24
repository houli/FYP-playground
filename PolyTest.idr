module PolyTest

import ProcessLib

%default total

data ListStuff elem  = Cons elem
                     | Index Nat

ListType : ListStuff elem -> Type
ListType (Cons _) = ()
ListType (Index _) = Maybe elem

typeEq : (elem : Type) -> (elem1 : Type) -> {auto ok : elem = elem1} -> elem = elem1
typeEq {ok} _ _ = ok

typeOf : a -> Type
typeOf {a} _ = a

listService : (list : List elem) -> Service ListType ()
listService {elem} list = do
  msg <- Respond (\msg => case msg of
    Cons _ => Pure ()
    Index idx => Pure (index' idx list))
  newList <- case msg of
    Just (Cons val) => Pure (val :: list)
    _ => Pure list
  Loop $ listService newList

procMain : Client ()
procMain = do
  serv <- Spawn $ listService (the (List Nat) [])
  Request serv (Cons 4)
  Request serv (Cons 0)
  Just val <- Request serv (Index 0)
    | Nothing => Action (putStrLn "Index not found")
  Action (putStrLn $ "value was " ++ show val)

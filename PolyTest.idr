module PolyTest

import ProcessLib

%default total

thingsEq : (x : a) -> (y : b) -> {auto ok : x = y} -> x = y
thingsEq {ok} _ _ = ok

typeOf : a -> Type
typeOf {a} _ = a

data ListStuff : Type -> Type where
  Cons : elem1 -> ListStuff elem1
  Index : Nat -> ListStuff elem1

ListType : ListStuff elem1 -> Type
ListType (Cons _) = ()
ListType {elem1} (Index _) = Maybe elem1

listService : (list : List elem) -> Service ListType ()
listService {elem} list = do
  msg <- Respond (\msg => case msg of
    Cons _ => Pure ()
    Index idx => Pure (index' idx list))
  newList <- case msg of
    Just (Cons {elem1} val) => Pure (val :: list)
    _ => Pure list
  Loop $ listService list

procMain : Client ()
procMain = do
  serv <- Spawn $ listService (the (List Nat) [])
  Request serv (Cons 4)
  Request serv (Cons 0)
  Just val <- Request serv (Index 0)
    | Nothing => Action (putStrLn "Index not found")
  Action (putStrLn $ "value was " ++ show val)

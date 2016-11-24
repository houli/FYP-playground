module ProcessLib

import System.Concurrency.Channels

%default total

export
data MessagePID : (iface : reqType -> Type) -> Type where
     MkMessage : PID -> MessagePID iface

public export
data ProcState = Ready | Looping | Sent

public export
data Process : (iface : reqType -> Type) -> Type -> (in_state : ProcState) -> (out_state : ProcState) -> Type where
     Request : MessagePID service_iface -> (req : service_reqType) -> Process iface (service_iface req) st st
     Respond : ((req : reqType) -> Process iface (iface req) Ready Ready) -> Process iface (Maybe reqType) st Sent
     Spawn : Process service_iface () Ready Looping -> Process iface (MessagePID service_iface) st st
     Loop : Inf (Process iface a Ready Looping) -> Process iface a Sent Looping
     Action : IO a -> Process iface a st st
     Pure : a -> Process iface a st st
     (>>=) : Process iface a st1 st2 -> (a -> Process iface b st2 st3) -> Process iface b st1 st3

public export
data Fuel = Dry | More (Lazy Fuel)

export partial
forever : Fuel
forever = More forever

export
run : Fuel -> Process iface t in_state out_state -> IO (Maybe t)
run Dry _ = pure Nothing
run fuel (Action act) = do res <- act
                           pure (Just res)
run fuel (Spawn proc) = do pid <- spawn (do run fuel proc
                                            pure ())
                           pure (Just (MkMessage pid))
run (More fuel) (Loop act) = run fuel act
run fuel (Request {service_iface} (MkMessage process) msg) = do
  Just chan <- connect process
       | _ => pure Nothing
  ok <- unsafeSend chan msg
  if ok then do Just x <- unsafeRecv (service_iface msg) chan
                     | Nothing => pure Nothing
                pure (Just x)
        else pure Nothing
run fuel (Respond {reqType} f) = do
  Just sender <- listen 1
       | Nothing => pure (Just Nothing)
  Just msg <- unsafeRecv reqType sender
       | Nothing => pure (Just Nothing)
  Just res <- run fuel (f msg)
       | Nothing => pure Nothing
  unsafeSend sender res
  pure (Just (Just msg))
run fuel (Pure val) = pure (Just val)
run fuel (act >>= next) = do Just x <- run fuel act
                                  | Nothing => pure Nothing
                             run fuel (next x)

public export
NoRecv : Void -> Type
NoRecv = const Void

public export
Service : (iface : reqType -> Type) -> Type -> Type
Service iface a = Process iface a Ready Looping

public export
Client : Type -> Type
Client a = Process NoRecv a Ready Ready

export partial
runProc : Process iface () in_state out_state -> IO ()
runProc proc = do run forever proc
                  pure ()

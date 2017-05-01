module RLE

-- Based on Idris example code
-- Further implemented to provide an intermediate representation
-- and to output RLE buffers to a compressed file

import Data.Bits
import Data.Vect

data RLE : Vect n Char -> Type where
     REnd  : RLE []
     RChar : {xs : Vect k Char} ->
             (n : Nat) -> (c : Char) -> (rs : RLE xs) ->
             RLE (replicate (S n) c ++ xs)

rle : (xs : Vect n Char) -> RLE xs
rle [] = REnd
rle (x :: xs) with (rle xs)
  rle (x :: []) | REnd = RChar 0 x REnd
  rle (x :: (c :: (replicate n c ++ ys))) | (RChar n c rs) with (decEq x c)
    rle (x :: (x :: (replicate n x ++ ys))) | (RChar n x rs) | (Yes Refl)
        = RChar (S n) x rs
    rle (x :: (c :: (replicate n c ++ ys))) | (RChar n c rs) | (No f)
        = RChar 0 x (RChar n c rs)

compress : Vect n Char -> String
compress xs with (rle xs)
  compress [] | REnd = ""
  compress (c :: (replicate n c ++ xs1)) | (RChar n c rs)
       = show (the Integer (cast (S n))) ++
           strCons c (compress xs1)

export
intermediate : {auto p : m `LTE` (S n)} -> Vect (S n) Char -> (m : Nat ** Vect (S m) (Nat, Char))
intermediate xs with (rle xs)
  intermediate (_ :: _) | REnd impossible
  intermediate (c :: (replicate n c ++ [])) | (RChar n c rs) = (_ ** [(S n, c)])
  intermediate (c :: (replicate n c ++ (z :: zs))) | (RChar n c rs)
    = let (_ ** ws) = intermediate (z :: zs)
        in (_ ** (S n, c) :: ws)

export
compressedBits : (n : Nat ** Vect (S n) (Nat, Char)) -> List (Bits 8)
compressedBits (Z ** ((n, c) :: [])) = [intToBits (cast n), intToBits (cast (ord c))]
compressedBits ((S x) ** ((n, c) :: xs)) = intToBits (cast n) :: intToBits (cast (ord c)) :: compressedBits (x ** xs)

export
compressString : String -> String
compressString xs = compress (fromList (unpack xs))

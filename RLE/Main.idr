module Main

import Data.Bits
import Data.Vect

import RLE

inter : (m : Nat ** Vect (S m) (Nat, Char))
inter = intermediate $ fromList $ unpack "11111111111foooobaaaarbaaaz"

main : IO ()
main = putStrLn $ show $ compressedBits inter

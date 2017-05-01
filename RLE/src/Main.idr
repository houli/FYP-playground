module Main

import Data.Bits
import Data.Buffer
import Data.Vect

import RLE

testString : String
testString = "11111111111foooobaaaarbaaaz"

inter : (m : Nat ** Vect (S m) (Nat, Char))
inter = intermediate $ fromList $ unpack testString

compressed : List (Bits 8)
compressed = compressedBits inter

writeCompressed' : List (Bits 8) -> Buffer -> Int -> List (IO ())
writeCompressed' [] buf loc = [pure ()]
writeCompressed' ((MkBits x) :: xs) buf loc = setByte buf loc x :: writeCompressed' xs buf (loc + 1)

writeCompressed : List (Bits 8) -> Buffer -> List (IO ())
writeCompressed xs buf = writeCompressed' xs buf 0

main : IO ()
main = do
  putStrLn ("Compressing: " ++ testString)
  putStrLn $ show compressed
  let bufferSize = cast $ 2 * (S (fst inter))
  Just buffer <- newBuffer bufferSize
    | Nothing => putStrLn "Failed to allocate buffer" -- If out of memory
  sequence_ $ writeCompressed compressed buffer -- Fill buffer
  Right file <- openFile "output.bin" WriteTruncate -- Get file handle
    | Left _ => putStrLn "Failed to get file handle"
  writeBufferToFile file buffer bufferSize
  putStrLn "Output written to output.bin"

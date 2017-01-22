module Main

import RLE

main : IO ()
main = putStrLn (compressString "11111111111foooobaaaarbaaaz")

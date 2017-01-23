module Main

import Data.Vect

import RLE

main : IO ()
main = putStrLn $ show $ intermediate $ fromList $ unpack "11111111111foooobaaaarbaaaz"

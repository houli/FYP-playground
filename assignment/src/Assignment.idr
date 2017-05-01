module Assignment

import Data.Vect

import HungarianList
import HungarianMatrix
import HungarianMatrixProof

namespace Main
  -- Test calling all 3 versions
  main : IO ()
  main = do
    putStrLn "Testing HungarianList module"
    putStrLn $ show $ HungarianList.hungarianMethod [[250, 400, 350], [400, 600, 350], [200, 400, 250]]

    putStrLn "Testing HungarianMatrix module"
    putStrLn $ show $ HungarianMatrix.hungarianMethod [[250, 400, 350], [400, 600, 350], [200, 400, 250]]

    putStrLn "Testing HungarianMatrixProof module"
    putStrLn $ show $ HungarianMatrixProof.hungarianMethod [[250, 400, 350], [400, 600, 350], [200, 400, 250]]

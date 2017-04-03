module Assignment

import Data.Vect

import HungarianList
import HungarianMatrix
import HungarianMatrixProof


namespace Main
  -- Test calling all 3 versions
  main : IO ()
  main = do
    putStrLn $ show $ HungarianList.hungarianMethod [[250, 400, 350], [400, 600, 350], [200, 400, 250]]
    putStrLn $ show $ HungarianMatrix.hungarianMethod [[250, 400, 350], [400, 600, 350], [200, 400, 250]]
    putStrLn $ show $ HungarianMatrixProof.hungarianMethod [[250, 400, 350], [400, 600, 350], [200, 400, 250]]

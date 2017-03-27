module Assignment

import Data.Vect

-- import HungarianList
-- import HungarianMatrix
import HungarianMatrixProof

-- Call into the proven version
main : IO ()
main = print $ hungarianMethod [[250, 400, 350], [400, 600, 350], [200, 400, 250]]

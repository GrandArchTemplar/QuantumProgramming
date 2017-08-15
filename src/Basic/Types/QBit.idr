module Basic.Types.QBit

import Data.Complex

%default total
%access public export

record QuantumState a where
  constructor QS
  amplitude : Complex a
  label : String

implementation (Num a, Neg a, Show a, Eq a, Ord a) => 
                                                     Show (QuantumState a) where
  show (QS amplitude label) = complexShow amplitude ++ "|" ++ label ++ ">" where
    complexShow : (Num a, Neg a, Show a, Eq a, Ord a) => Complex a -> String 
    complexShow (x :+ y) = if (x-x) == x 
                              then if (y-y) == y 
                                      then "0"
                                      else ?imShow
                              else ?f

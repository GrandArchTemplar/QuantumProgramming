module Basic.Interfaces.Conjugate

import Data.Complex

import Basic.Types.Matrix

%default total
%access public export

interface Conjugate space coSpace where
  conjug : space -> coSpace

implementation Neg a => Conjugate (Complex a) (Complex a) where
  conjug = conjugate

implementation Conjugate Double Double where
  conjug = id

implementation Conjugate Integer Integer where
  conjug = id

implementation Conjugate Nat Nat where
  conjug = id

implementation Conjugate Int Int where
  conjug = id

-- generate
implementation Conjugate space space => 
           Conjugate (Matrix (S n) (S m) space) (Matrix (S m) (S n) space) where
  conjug = fromVecVec . asCols . map conjug 

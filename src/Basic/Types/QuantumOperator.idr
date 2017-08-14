module Basic.Types.QuantumOperator

import Data.Complex

%default total
%access public export


--QOperator is a suggr for single QBit work
data QOperator : (a11, a12, a21, a22 : Complex Double) -> Type where
  QOp : (a11, a12, a21, a22 : Complex Double) -> QOperator a11 a12 a21 a22

-- compose of QOperators
(.) : QOperator a11 a12 a21 a22 -> QOperator b11 b12 b21 b22
    -> QOperator (a12*b21+a11*b11) (a12*b22+a11*b12) (a22*b21+a21*b11) (a22*b22+a21*b12) 
(QOp a11 a12 a21 a22) . (QOp b11 b12 b21 b22) = 
  QOp (a12*b21+a11*b11) (a12*b22+a11*b12) (a22*b21+a21*b11) (a22*b22+a21*b12) 



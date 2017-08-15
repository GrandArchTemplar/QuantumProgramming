module Basic.Types.TotalQbit

import Data.Complex
import Data.Vect

import Basic.Interfaces.Conjugate
import Basic.Types.Matrix
import Basic.Types.QuantumOperator

%default total
%access public export

infix 3 |>
data QState : (a : Complex Double) -> (s : String) -> Type where
       (|>) : (a : Complex Double) -> (s : String) -> QState a s
extract : QState a s -> Complex Double
extract (a |> _) = a

-- add two quantum state of one state which produce new quantum state 
-- of current state
(+) : QState a s -> QState b s -> QState (a + b) s
(a |> s) + (b |> s) = (a + b |> s)

qAbs :  Vect n (QState a s) -> Double
qAbs xs = foldl (+) 0 (map (sqr . magnitude . extract) xs) where
  sqr : Double -> Double
  sqr x = x * x

infix 2 >><< 
data TotalQbit : (qS1 : QState a s) -> (qS2 : QState a s) -> Type where
        (>><<) : (qS1 : QState a s) -> (qS2 : QState a s) -> TotalQbit qS1 qS2


TQSZero : Type
TQSZero = QState (1:+0) "0"

QSZero : TQSZero
QSZero = 1:+0|>"0"

TQSOne : Type
TQSOne = QState (0:+1) "1"

QSOne : TQSOne
QSOne = 0:+1|>"1"

TestTotalQbit : TotalQbit (1:+0 |> "0") (1:+0|>"0")
TestTotalQbit = 1:+0|>"0">><<1:+0|>"0"

data QBit : Complex Double -> Complex Double -> Type where
  StdQBit : (z : Complex Double) -> (o : Complex Double) -> QBit z o
--  AltQBit : (p : Complex Double) -> (n : Complex Double) -> QBit p n

infix 1 =$ 
(=$) : QOperator q11 q12 
                 q21 q22 -> QBit a b 
                         -> QBit (a * q11 + b * q12) 
                                 (a * q21 + b * q22)
(QOp q11 q12 q21 q22) =$ (StdQBit a b) = StdQBit (a * q11 + b * q12) 
                                                 (a * q21 + b * q22)
--(QOp q11 q12 q21 q22) =$ (AltQBit a b) = AltQBit (a * q11 + b * q12) 
--                                                 (a * q21 + b * q22)

changeFormOperator : QOperator ((1 / sqrt(2)):+0) ((1 / sqrt(2)):+0) 
                               ((1 / sqrt(2)):+0) ((1 / sqrt(2)):+0)
changeFormOperator = QOp ((1 / sqrt(2)):+0) ((1 / sqrt(2)):+0) 
                         ((1 / sqrt(2)):+0) ((1 / sqrt(2)):+0)

--changeForm : QBit (x1 :+ y1) 
--                  (x2 :+ y2) 
--                      -> QBit (((x1 + x2) / sqrt 2) :+ ((y1 + y2) / sqrt 2)) 
--                              (((x1 - x2) / sqrt 2) :+ ((y1 - y2) / sqrt 2))
--changeForm (StdQBit (x1 :+ y1) (x2 :+ y2)) = 
--  AltQBit (((x1 + x2) / sqrt 2) :+ ((y1 + y2) / sqrt 2)) 
--          (((x1 - x2) / sqrt 2) :+ ((y1 - y2) / sqrt 2))
--changeForm (AltQBit (x1 :+ y1) (x2 :+ y2)) = 
--  StdQBit (((x1 + x2) / sqrt 2) :+ ((y1 + y2) / sqrt 2)) 
--          (((x1 - x2) / sqrt 2) :+ ((y1 - y2) / sqrt 2))


transform : QBit a b -> Matrix 2 1 (Complex Double) 
transform (StdQBit a b) = Raws [a] (Raws [b] [])

--transform (AltQBit a b) = ?p

infix 5 <||>
(<||>) : QBit a b -> QBit c d -> Matrix 1 1 (Complex Double)
qb1 <||> qb2 = (conjug . transform $ qb1) * transform qb2
infix 5 >||<
(>||<) : QBit a b -> QBit c d -> Matrix 2 2 (Complex Double)
qb1 >||< qb2 = (transform qb1) * (conjug . transform $ qb2)




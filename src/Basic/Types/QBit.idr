module Basic.Types.TotalQbit

import Data.Complex
import Data.Vect

import Basic.Types.Matrix
import Basic.Types.QuantumOperator

%default total
%access public export

infix 3 |>
data QState : (a : Complex Double) -> (s : String) -> Type where
  (|>) : (a : Complex Double) -> (s : String) -> QState a s
extract : QState a s -> Complex Double
extract (a |> _) = a

-- add two quantum state of one state which produce new quantum state current state
(+) : QState a s -> QState b s -> QState (a + b) s
(a |> s) + (b |> s) = (a + b |> s)

qAbs :  Vect n (QState a s) -> Double
qAbs xs = foldl (+) 0 (map (sqr . magnitude . extract) xs) where
  sqr : Double -> Double
  sqr x = x * x

infix 2 >><< 
data TotalQbit : (qS1 : QState a s) -> (qS2 : QState a s) {--> {prf : Dec (qAbs [qState1, qState2] = 1)--} -> Type where
  (>><<) : (qS1 : QState a s) -> (qS2 : QState a s) {--> (prf : Dec (qAbs [qState1, qState2] = 1))--} -> TotalQbit qS1 qS2


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
  AltQBit : (p : Complex Double) -> (n : Complex Double) -> QBit p n

infix 1 =$ 
(=$) : QOperator q11 q12 q21 q22 -> QBit a b -> QBit (a * q11 + b * q12) (a * q21 + b * q22)
(QOp q11 q12 q21 q22) =$ (StdQBit a b) = StdQBit (a * q11 + b * q12) (a * q21 + b * q22)
(QOp q11 q12 q21 q22) =$ (AltQBit a b) = AltQBit (a * q11 + b * q12) (a * q21 + b * q22)



module Base.Types.QBit

import Data.Complex
import Data.Vect

%default total
%access public export

infix 3 |>
data QState : (a : Complex Double) -> (s : String) -> Type where
  (|>) : (a : Complex Double) -> (s : String) -> QState a s
extract : QState a s -> Complex Double
extract (a |> _) = a

-- add two quantum state whic produce new quantum state
-- ma
(+) : QState a s -> QState b s -> QState (a + b) s
(a |> s) + (b |> s) = (a + b |> s)

qAbs :  Vect n (QState a s) -> Double
qAbs xs = foldl (+) 0 (map (sqr . magnitude . extract) xs) where
  sqr : Double -> Double
  sqr x = x * x

infix 2 >><< 
data QBit : (qS1 : QState a s) -> (qS2 : QState a s) {--> {prf : Dec (qAbs [qState1, qState2] = 1)--} -> Type where
  (>><<) : (qS1 : QState a s) -> (qS2 : QState a s) {--> (prf : Dec (qAbs [qState1, qState2] = 1))--} -> QBit qS1 qS2


TQSZero : Type
TQSZero = QState (1:+0) "0"

QSZero : TQSZero
QSZero = 1:+0|>"0"

TQSOne : Type
TQSOne = QState (0:+1) "1"

QSOne : TQSOne
QSOne = 0:+1|>"1"



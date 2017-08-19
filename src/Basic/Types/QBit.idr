module Basic.Types.QBit

import Data.Complex
import Data.Vect

import Utilll.Accomodation

%default total
%access public export

record QuantumState a where
  constructor QS
  amplitude : Complex a
  label : String

%name QuantumState qs, qs1, qs2, qs3
implementation (Num a, Neg a, Show a, Eq a, Ord a) 
                  => Show (QuantumState a) where
  show (QS amplitude label) = complexShow amplitude ++ "|" ++ label ++ ">" where
    complexShow : Complex a -> String 
    complexShow (x :+ y) = 
      if x == x + x 
         then imShow y
         else if y <= y + y
                 then show x ++ "+" ++ imShow y
                 else show x ++ imShow y where
                      imShow : a -> String
                      imShow y = 
                        if y > y + y 
                           then "-" ++ imPosShow (negate y)
                           else imPosShow y where
                                imPosShow : (y : a) ->  String
                                imPosShow y = if y /= y + y 
                                                 then if y * y == y
                                                         then "i"
                                                         else show y ++ "i"
                                                 else "0"
                                                                      

qMap : (f : Complex a -> Complex b) -> QuantumState a -> QuantumState b
qMap f (QS amplitude label) = QS (f amplitude) label

implementation Eq a => Eq (QuantumState a) where
  (QS amplitude1 label1) == (QS amplitude2 label2) = 
    (amplitude1 == amplitude2) && (label1 == label2)
implementation [vectorization] Ord a =>  Ord (QuantumState a) where
  compare (QS amplitude1 label1) (QS amplitude2 label2) = compare label1 label2

qPredicate : (p : Complex a -> Bool) -> QuantumState a -> Bool
qPredicate p (QS amplitude label) = p amplitude

conjugateQS : Neg a => QuantumState a -> QuantumState a
conjugateQS = qMap conjugate

record QBit a where
  constructor QB
  states : List (QuantumState a)
%name QBit qb, qb1, qb2, qb3
partial
implementation (Num a, Neg a, Show a, Eq a, Ord a) 
                => Show (QBit a) where
  show (QB []) = ""                 
  show (QB (x :: [])) = show x            
  show (QB (x :: qb@(y :: xs))) = show x ++ " + " 
    ++ show (QB qb)

toAmplList : QBit a -> List (Complex a)
toAmplList (QB states) = map amplitude states

toLabelList : QBit a -> List String
toLabelList (QB states) = map label states

fromList : List (Complex a) -> List String -> QBit a
fromList xs ys = QB (zipWith QS xs ys)

refine : Ord a => QBit a -> List (QuantumState a)
refine (QB states) = sort @{vectorization} states

toFineList : Ord a => QBit a -> List (Complex a)
toFineList (QB states) = map amplitude (sort @{vectorization} states)

fromFineList : List (Complex a) -> QBit a 
fromFineList xs = QB (zipWith QS xs (accomod "01" (degree (length xs) 2)))

liftQBit : (f : List (QuantumState a) -> List (QuantumState b)) -> QBit a -> QBit b
liftQBit f (QB states) = QB (f states)

infix 2 <~>
(<~>) : Neg a => QuantumState a -> QuantumState a -> QuantumState a
(QS amplitude1 label1) <~> (QS amplitude2 label2) = QS (amplitude1 * amplitude2) (label1 ++ label2)

entangle : Neg a => QBit a -> QBit a -> QBit a
entangle (QB states1) (QB states2) = QB [|states1 <~> states2|]

conjugateQBit : Neg a => QBit a -> QBit a
conjugateQBit = liftQBit (map conjugateQS)



test : QBit Int
test = QB [(QS (1:+(-1)) "0"), (QS (0:+1) "1")]

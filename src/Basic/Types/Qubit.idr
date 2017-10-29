module Basic.Types.Qubit

import Data.Complex
import Data.Vect
import Effects
import Effect.Random
import Utils.Accomodation
import Utils.ComplexAddon

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
implementation [vectorization] Eq a => Ord (QuantumState a) where
  compare (QS amplitude1 label1) (QS amplitude2 label2) = compare label1 label2

qPredicate : (p : Complex a -> Bool) -> QuantumState a -> Bool
qPredicate p (QS amplitude label) = p amplitude

conjugateQS : Neg a => QuantumState a -> QuantumState a
conjugateQS = qMap conjugate

record Qubit a where
  constructor QB
  states : List (QuantumState a)
%name Qubit qb, qb1, qb2, qb3
partial
implementation (Num a, Neg a, Show a, Eq a, Ord a) 
                => Show (Qubit a) where
  show (QB [])                  = ""                 
  show (QB (x :: []))           = show x            
  show (QB (x :: qb@(y :: xs))) = show x ++ " + " 
    ++ show (QB qb)

toAmplList : Qubit a -> List (Complex a)
toAmplList (QB states) = map amplitude states

toLabelList : Qubit a -> List String
toLabelList (QB states) = map label states

fromList : List (Complex a) -> List String -> Qubit a
fromList xs ys = QB (zipWith QS xs ys)

refine : Ord a => Qubit a -> List (QuantumState a)
refine (QB states) = sort @{vectorization} states

toFineList : Eq a => Qubit a -> List (Complex a)
toFineList (QB states) = map amplitude (sort @{vectorization} states)

fromFineList : List (Complex a) -> Qubit a 
fromFineList xs = QB (zipWith QS xs (accomod "01" (degree (length xs) 2)))

liftQubit : (f : List (QuantumState a) -> List (QuantumState b)) 
              -> Qubit a -> Qubit b
liftQubit f (QB states) = QB (f states)

infix 2 <~>
(<~>) : Neg a => QuantumState a -> QuantumState a -> QuantumState a
(QS amplitude1 label1) <~> (QS amplitude2 label2) = 
  QS (amplitude1 * amplitude2) (label1 ++ label2)

entangle : Neg a => Qubit a -> Qubit a -> Qubit a
entangle (QB states1) (QB states2) = QB [|states1 <~> states2|]

conjugateQubit : Neg a => Qubit a -> Qubit a
conjugateQubit = liftQubit (map conjugateQS)

scalarProduct : (Neg a, Eq a) => Qubit a -> Qubit a -> a
scalarProduct qb1 qb2 = realPart 
                        (sum 
                          (Prelude.List.zipWith (*) 
                                                (toFineList qb1) 
                                                (toFineList qb2)))

norm : (Cast a Double, Cast Double a, Neg a, Eq a) => Qubit a -> a
norm qb = (cast . sqrt . cast) (scalarProduct qb (conjugateQubit qb))

normalize : (Cast a Double, Cast Double a, Neg a, Eq a, Fractional a) => 
            Qubit a -> Qubit a
normalize qb = liftQubit ((map . qMap) 
             (cast . 
             (\x => x / (((sqrt . cast) 
                          (scalarProduct qb (conjugateQubit qb))):+0)) . 
             cast)) qb

extract : (Cast a Double, Cast Double a, Neg a, Eq a) => 
          Qubit a -> Eff String [RND]
extract qb = helper (map cast (toAmplList qb)) (toLabelList qb) where
  helper : List (Complex Double) -> List String-> Eff String [RND]
  helper ampl labels = help (part 0 ampl) labels where
    part : Double -> List (Complex Double) -> List Double
    part prev [] = []
    part prev ((x :+ y) :: xs) = curr :: part curr xs where
      curr : Double
      curr = prev + x * x + y * y
    help : List Double -> List String -> Eff String [RND]
    help [] _            = pure "Nothing"
    help ds@(x :: xs) ys = 
      do rand <- assert_total (rndInt 0 (transmute (last ds)))
         findAns (zip (map transmute ds) ys) rand
      where
        transmute : Double -> Integer
        transmute x = cast (1000000000 * x)
        findAns : List (Integer, String) -> Integer -> Eff String [RND]
        findAns [] _                 = pure "Nothing"
        findAns ((p, label) :: xs) r = case p < r of
                                            False => findAns xs r
                                            True  => pure label


qubitZero : Qubit Double
qubitZero = QB ([(QS (1 :+ 0) "0"), 
                (QS (0 :+ 0) "1")])

qubitOne : Qubit Double
qubitOne = QB ([(QS (0 :+ 0) "0"), 
                (QS (1 :+ 0) "1")])

qubitPlus : Qubit Double
qubitPlus = QB ([(QS ((1 / sqrt 2) :+ 0) "0"), 
                 (QS ((1 / sqrt 2) :+ 0) "1")])

qubitMinus : Qubit Double
qubitMinus = QB ([(QS ((1    / sqrt 2) :+ 0) "0"), 
                  (QS (((-1) / sqrt 2) :+ 0) "1")])

qubitPhiPlus : Qubit Double
qubitPhiPlus = QB ([(QS ((1 / sqrt 2) :+ 0) "00"), 
                    (QS ((1 / sqrt 2) :+ 0) "11")])

qubitPhiMinus : Qubit Double
qubitPhiMinus = QB ([(QS ((1    / sqrt 2) :+ 0) "00"), 
                     (QS (((-1) / sqrt 2) :+ 0) "11")])

qubitPsiPlus : Qubit Double
qubitPsiPlus = QB ([(QS ((1 / sqrt 2) :+ 0) "01"), 
                    (QS ((1 / sqrt 2) :+ 0) "10")])

qubitPsiMinus : Qubit Double
qubitPsiMinus = QB ([(QS ((1    / sqrt 2) :+ 0) "01"), 
                     (QS (((-1) / sqrt 2) :+ 0) "10")])



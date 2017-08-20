module Utils.Accomodation

import Data.Vect
%hide Data.Vect.(::) 
%default total
%access public export

accomod : String -> Nat -> List String
accomod x k = helper (sort (map (pack . (\x => [x])) (unpack x))) k where
  helper : List String -> Nat -> List String
  helper alph Z = []
  helper alph (S Z) = alph
  helper alph (S (S k)) = pure (++) <*> alph <*> helper alph (S k)

degree : Nat -> Nat -> Nat
degree x k = helper x k 0 1 where
  helper : Nat -> Nat -> Nat -> Nat -> Nat
  helper x k r acc = case x < acc of
                        False => assert_total (helper x k (S r) (acc * k))
                        True => r



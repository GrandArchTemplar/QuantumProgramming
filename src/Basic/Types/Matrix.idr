module Basic.Types.Matrix

import Data.Vect

%default total
%access public export

--n -- raws
--m -- columns
--infix 7 <:
--infix 7 !:
data Matrix : (n : Nat) -> (m : Nat) -> (a : Type) -> Type where
--  Nil : Matrix 0 0 a
--  AsCols : Vect n a -> Matrix n m a -> Matrix n (S m) a
  Nil : Matrix 0 m a
  Raws : Vect m a -> Matrix n m a -> Matrix (S n) m a

%name Matrix mt, mt1, mt2, mt3
Operator : (n : Nat) -> (a : Type) -> Type
Operator n a = Matrix n n a

test : Matrix 2 3 Nat
test = (Raws [1, 2, 3] (Raws [4, 5, 6] Nil))

toVecVec : Matrix n m a -> Vect n (Vect m a)
toVecVec [] = []
toVecVec (Raws xs mt) = xs :: toVecVec mt

fromVecVec : Vect n (Vect m a) -> Matrix n m a
fromVecVec [] = Nil
fromVecVec (x :: xs) = Raws x (fromVecVec xs)

asRaws : Matrix n m a -> Vect n (Vect m a)
asRaws [] = []
asRaws (Raws xs mt) = xs :: asRaws mt

asCols : Matrix (S n) m a -> Vect m (Vect (S n) a)
asCols (Raws xs []) = map (\x => [x]) xs
asCols (Raws xs (Raws ys mt)) = zipWith (::) xs (asCols (Raws ys mt))

infix 7 <#>
(<#>) : Num a => Vect (S n) a -> Vect (S n) a -> a
a <#> b = sum (zipWith (*) a b)

(+) : Num a => Matrix n m a -> Matrix n m a -> Matrix n m a 
[] + [] = []
(Raws xs mt1) + (Raws ys mt2) = Raws (zipWith (+) xs ys)  (mt1 + mt2)

(*) : Num a => Matrix (S n) (S m) a 
            -> Matrix (S m) (S k) a -> Matrix (S n) (S k) a
mt * mt1 = fromVecVec(helper (asRaws mt) (asCols mt1)) where
  helper : Num a => Vect (S n) (Vect (S m) a) 
                 -> Vect (S k) (Vect (S m) a) -> Vect (S n) (Vect (S k) a)
  helper (x :: []) y = map (x <#>) y :: []
  helper (x :: (z :: xs)) y = map (x <#>) y :: helper (z :: xs) y
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------


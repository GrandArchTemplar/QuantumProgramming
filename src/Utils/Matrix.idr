module Utils.Matrix

import Utils.Conjugate

%default total
%access public export

Vector : Type -> Type
Vector = List 
%name Vector xv, yv, zv

Matrix : Type -> Type
Matrix = Vector . Vector
%name Matrix xm, ym, zm

apply : Num a => Matrix a -> Vector a -> Vector a
apply xm xv = map (\row => sum (zipWith (*) row xv)) xm 

transpose : Matrix a -> Matrix a
transpose [] = []
transpose (x :: xs) = zipWith (::) x xs

mmap : (a -> b) -> Matrix a -> Matrix b
mmap f = map (map f) 

implementation Conjugate space coSpace => Conjugate (Matrix space) (Matrix coSpace) where
  conjug = Utils.Matrix.transpose . mmap conjug 

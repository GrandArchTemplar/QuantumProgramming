module Utils.ComplexAddon

import Data.Complex

%default total
%access public export

implementation (Fractional a, Neg a) => Fractional (Complex a) where
    (/) (a:+b) (c:+d) = let
                          real = (a*c+b*d)/(c*c+d*d)
                          imag = (b*c-a*d)/(c*c+d*d)
                        in
                          (real:+imag)

implementation (Cast a b) => Cast (Complex a) (Complex b) where
  cast (x :+ y) = (cast x :+ cast y) 

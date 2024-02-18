module K11

punkt2d : Type
punkt2d = (Double, Double)

punkt : Nat -> Type
punkt Z     = Unit
punkt (S Z) = Double
punkt (S n) = (Double, punkt n)

xy : punkt 2
xy = (2.0,4.0)
 
xyz : punkt 3
xyz = (3.0,6.0,3.0)

nullpunkt : (d : Nat) -> punkt d
nullpunkt 0 = ()
nullpunkt (S 0) = 0.0
nullpunkt (S (S k)) = (0.0, nullpunkt (S k))

--nullpunkt 0 ==> ()
--nullpunkt 1 ==> 0.0
--nullpunkt 2 ==> (0.0, 0.0)

add: (d:Nat) -> punkt d -> punkt d -> punkt d
add 0 () () = ()
add (S 0) x y = x + y
add (S (S k)) (x1, p1) (x2, p2) = (x1 + x2, add (S k) p1 p2)

--add 0 () () ==> ()
--add 1 1.0 2.0 ==> 3.0
--add 3 (0.2, 0.2, 4.0) (1.0, 2.0, 0.2) ==> (1.2, 2.2, 4.2)


sum : (d : Nat) -> List (punkt d) -> punkt d
sum 0 [] = ()
sum k [] = nullpunkt k
sum k (x :: xs) = add k x (sum k xs)

--sum 0 [] ==> ()
--sum 2 [(1.0,1.0), (2.0,2.0)] ==> (3.0, 3.0)


data Vect : (k : Nat) -> (a : Type) -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a
 
Eq a => Eq (Vect k a) where
    [] == []             = True
    (x :: y) == (z :: w) = x==z && y==w

append : Vect n a -> Vect m a -> Vect (n + m) a
append []        ys = ys
append (x :: xs) ys = x :: append xs ys

zipVect : Vect n a -> Vect n b -> Vect n (a,b)
zipVect [] [] = Nil
zipVect (x :: xs) (y :: ys) = (x, y) :: zipVect xs ys

--zipVect [1,2,3] ['a', 'b', 'c'] == [(1, 'a'), (2, 'b'), (3, 'c')]

replaceVect : a -> (n:Nat) -> Vect (1+n+k) a -> Vect (1+n+k) a
replaceVect a 0 (x :: xs) = a :: xs
replaceVect a (S j) (x :: xs) = x :: replaceVect a j xs 

--replaceVect 'x' 0 ['a','b','c','d'] == ['x', 'b', 'c', 'd']
--replaceVect 'x' 1 ['a','b','c','d'] == ['a', 'x', 'c', 'd']
--replaceVect 'x' 2 ['a','b','c','d'] == ['a', 'b', 'x', 'd']
module K6

import Data.Nat

data Tree a = Leaf | Branch (Tree a) a (Tree a)
 
Eq a => Eq (Tree a) where
  Leaf == Leaf = True
  (Branch x y z) == (Branch w v s) =  x==w && y==v && z==s
  _ == _ = False
 
--mis liidesele --mis tüübile 
Functor Tree where
  map f Leaf = Leaf
  map f (Branch l x r) = Branch (map f l) (f x) (map f r)


Foldable Tree where
  foldr f b Leaf = b
  foldr f b (Branch l x r) = foldr f (f x (foldr f b r)) l


len : Foldable t => t a -> Int
len t = foldr (\elem, acc => acc + 1) 0 t

--saab operaatori argumendina kutsuda -- perioriteet 7 --syntaks
infix 7 :/:
data Rat = (:/:) Nat Nat
 
-- normaliseerimine
norm : Rat -> Rat
norm (_   :/:   0) = 0 :/: 0
norm (0   :/:   _) = 0 :/: 1
-- z=0 S=1+n
norm (S a :/: S b) =
    --leitakse suurim ühistegur
    let n = gcd (S a) (S b) in
    (S a) `div` n :/: (S b) `div` n
 
-- muud operatsioonid:
-- (a :/: b) == (c :/: d) = a*d == b*c
-- (a :/: b) +  (c :/: d) = a*d + b*c :/: b*d
-- (a :/: b) *  (c :/: d) = a*c :/: b*d
-- (a :/: b) /  (c :/: d) = a*d :/: b*c
-- pöörd (a :/: b) = b :/: a
 
neljandik : Rat
neljandik = 1 :/: 4
 
pool : Rat
pool = 1 :/: 2

--Defineerige Eq liides ratsionaalarvudele. 
Eq Rat where
    (a :/: b) == (c :/: d) = a*d == b*c

--Defineerige Num liides ratsionaalarvudele. 
Num Rat where
    (a :/: b) + (c :/: d) = a*d + b*c :/: b*d
    (a :/: b) * (c :/: d) = a*c :/: b*d
    fromInteger x = fromInteger x :/: 1

--Defineerige Fractional liides ratsionaalarvudele. 
Fractional Rat where
    (a :/: b) /  (c :/: d) = norm $ a*d :/: b*c
    recip (a :/: b) = b :/: a


variandidList : List Int -> List (List Int)
variandidList = traverse (\ x => [x,-x])


--Functor List where
--  --map :  (a -> b) -> List a -> List b
--  map f []          = []
--  map f ((::) x xs) = (::) (f x) (map f xs)
--Traversable List where
--  --traverse :  Applicative h => (a -> h b) -> List a -> h (List b)
--  traverse f []      =  pure []
--  traverse f (x::xs) =  pure (::) <*> (f x) <*> (traverse f xs)


Traversable Tree where
  traverse g Leaf = pure Leaf
  traverse g (Branch l x r) = pure Branch <*> (traverse g l) <*> (g x) <*> (traverse g l)
 
variandidTree : Tree Int -> List (Tree Int)
variandidTree = traverse (\ x => [x,-x])
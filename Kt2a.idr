%default total
 
-- 1) leia kõik reedeksid
 
-- (λg. (λy. (λx.y) g) x)
 
 
-- 2) beeta-redutseeri normaalkujule normaal- ja aplikatiivjärjekorras
 
-- (λx. (λx.x)) ((λx. x) x)
 
 
-- 3) tüübi tuletamine
-- "Joonista" tüübituletuspuu, kirjuta välja kõik kitsendused ja
-- lahenda kogu avaldise tüüp ɣ2.
-- 
-- Lihtsustuseks:
--  * ei pea kirjutama xᵅ ∈ Γ
--  * kitsendusi ei pea kirjutama puu sisse  (mis oli slaididel roheline)
-- 
 
-- ⊢ (λxᵅ¹. ((λyᵅ². (λzᵅ³. yᵅ⁴)ˠ¹)ˠ³ xᵅ⁵)ᵝ¹)ˠ²
  
 
 
 
-- 4) sõltuvate tüüpidega programmeerimine

data TreeShape : Type where
  LeafShape : TreeShape
  NodeShape : (l : TreeShape) -> (r : TreeShape) -> TreeShape
 
data Tree : TreeShape -> Type -> Type where
  Leaf : Tree LeafShape a
  Node : (left : Tree l a) -> (this : a) -> (right : Tree r a) ->
       Tree (NodeShape l r) a
 
Eq TreeShape where
    LeafShape == LeafShape  = True
    LeafShape == (NodeShape l r)  = False
    (NodeShape l r) == LeafShape  = False
    (NodeShape l r) == (NodeShape x y)  =
        l==x && r==y
 
Eq a => Eq (Tree s a) where
    Leaf == Leaf = True
    (Node left this right) == (Node x y z) =
        left == x && this == y && right == z


data Vect : Nat -> Type -> Type where
    Nil  : Vect 0 a
    (::) : a -> Vect n a -> Vect (1+n) a
 
fromNat : Nat -> TreeShape
fromNat 0 = LeafShape
fromNat (S k) = NodeShape LeafShape (fromNat k)

vecToTree : Vect n a -> Tree (fromNat n) a
vecToTree [] = Leaf
vecToTree (x :: xs) = Node Leaf x (vecToTree xs)

-- vecToTree [1,2,3] == Node Leaf 1 (Node Leaf 2 (Node Leaf 3 Leaf))
-- vecToTree [] == the (Tree LeafShape Nat) Leaf
-- vecToTree [2] == Node Leaf 2 Leaf


-- 5) tõestamine Idris2-s
 
infixl 10 /\
data (/\) : Type -> Type -> Type where
    ConI : a -> b
        ------
        -> a /\ b
 
infixl 11 \/
data (\/) : Type -> Type -> Type where
    DisjIl :   a
            ------
        -> a \/ b
 
    DisjIr :   b
            ------
        -> a \/ b
 
VoidE : Void
        ----
    ->    b
VoidE q impossible

not : Type -> Type 
not a = a -> Void
 
decidable : Type -> Type
decidable a = a \/ not a 

doubleNegElim : Type -> Type
doubleNegElim a = not (not a) -> a

peirce : Type -> Type -> Type
peirce p q = ((p -> q) -> p) -> p

-- Tõesta väide:  decidable a -> doubleNegElim a

test1 : decidable a -> doubleNegElim a
test1 (DisjIl x) = ?test1_1
test1 (DisjIr x) = ?test1_2
-- a V not a --> not not a
-- a --> not not a
-- not a --> not not a 


-- 6) lineaarsed tüübid

-- Kvantitatiivses tüübisüsteemis on arvud 0, 1 ja suva. 
-- Üks võimalus saada ülejäänud naturaalarve on teha arvuga 1 ressurssidest vektor pikkusega n.

-- abifunktsioon testimiseks
add10 : (1 _ : Nat) -> Nat
add10 x = case x of { Z => 10; S z => 11+z }

namespace Lin
    public export
    data Vect : Nat -> Type -> Type where
        Nil  : Lin.Vect 0 a
        (::) : (1 _ : a) -> (1 _ : Lin.Vect n a) -> Lin.Vect (S n) a

Eq a => Eq (Lin.Vect k a) where
    [] == []             = True
    (x :: y) == (z :: w) = x==z && y==w

-- Implementeeri funktsioon mapLin, mis rakendab lineaarset funktsiooni kõigi lineaarse listi elementidele.

mapLin : ((1 _ :a)->b) -> (1 _: Lin.Vect n a) -> Lin.Vect n b
mapLin f [] = []
mapLin f (x ::xs) = (f x) :: mapLin f xs   

-- mapLin add10 [] == []
-- mapLin add10 [1] == [11]
-- mapLin add10 [1,2,3,4] == [11, 12, 13, 14]
module K10

--Implikatsiooni väljaviimise
-- ?f ?x : (a->b) -> a
--         ----------- 
--      ->      b

--Implikatsiooni sissetoomise
-- (\ x => ?y) :   a
--                 .
--                 .
--                 .
--                 b
--               ------
--          ->   a -> b


-- ainult täielikud funktsioonid tagavad turvalisuse
%default total 

--Konjunktsioon
infixl 10 /\
data (/\) : Type -> Type -> Type where
    ConI : a -> b
           ------
        -> a /\ b
 
-- Väljaviimise reegleid ise defineerima ei pea aga saame nende paikapidavust kontrollida.
conEl : a /\ b
        ------
     ->   a
 
-- Reegel kehtib, kui saame anda definitsiooni.
conEl (ConI a b) = a
 
conEr : a /\ b
        ------
     ->   b
 
conEr (ConI a b) = b

--Disjunktsioon
infixl 11 \/
data (\/) : Type -> Type -> Type where
    DisjIl :   a
             ------
          -> a \/ b
 
    DisjIr :   b
             ------
          -> a \/ b
 
disjE : (a\/b)  ->  (a -> c)  ->  (b -> c) 
        ----------------------------------
    ->               c
disjE (DisjIl x) f g = f x
disjE (DisjIr x) f g = g x



%hide Not  -- juba std. teegis olemas

--Eitus ja väärus 
data Not : Type -> Type where
    NotI :   (a -> Void)
             -----------
          ->    Not a
 
NotE : Not a -> a
       ----------
    ->    Void
 
NotE (NotI f) = f
 
--data Void : Type where
---- meelega jäetud tühjaks
 
 
VoidE : Void
        ----
    ->    b
VoidE q impossible


--Lausearvutuse ülesanne ex1 a = a /\ (b -> c) /\ (a -> b) = Cast(ConI (ConI x z) y)
ex1 :  a /\ (b -> c) /\ (a -> b)  ->  c
ex1 (ConI (ConI x z) y) = z (y x)

--Kalmeri lemmikväide:
--(Vihje: kasuta lambdat)
ex2 : a \/ Not a -> (a -> b) \/ (b -> a)
ex2 (DisjIl a) = DisjIr (\b => a)
-- ex2 (DisjIr x) = DisjIl (\a => VoidE (NotE x a))
ex2 (DisjIr (NotI f)) = DisjIl (\a => VoidE (f a))


--Paaris
data Even : Nat -> Type where
    Even_Zero : --------
                 Even 0
 
    Even_Succ :    Even n
                ------------
              -> Even (2+n)
 
even4 : Even 4
even4 = Even_Succ (Even_Succ Even_Zero)

even8 : Even 8
even8 = Even_Succ (Even_Succ even4)
 
plusEvenEven :  Even n -> Even m
               ------------------
             ->    Even (n+m)
plusEvenEven Even_Zero b = b
plusEvenEven (Even_Succ n) m = Even_Succ (plusEvenEven n m)
 
 
multEvenEven :  Even n -> Even m
               ------------------
             ->    Even (n*m)
multEvenEven Even_Zero b = Even_Zero
multEvenEven (Even_Succ x) b = plusEvenEven b (plusEvenEven b (multEvenEven x b))


--Paaris/paaritu
data Odd : Nat -> Type where
    Odd_one : --------
               Odd 1
 
    Odd_Succ :    Odd n
                -----------
              -> Odd (2+n)
 
odd7 : Odd 7
odd7 = Odd_Succ (Odd_Succ (Odd_Succ Odd_one))
 
evenOdd :   Even n
          ----------
        -> Odd (1+n)
evenOdd Even_Zero = Odd_one
evenOdd (Even_Succ x) = Odd_Succ (evenOdd x)
 
 
plusOddOdd :  Odd n  ->  Odd m
             -------------------
           ->     Even (n+m)
plusOddOdd Odd_one Odd_one = Even_Succ Even_Zero  
plusOddOdd Odd_one (Odd_Succ x) = Even_Succ (plusOddOdd Odd_one x)
plusOddOdd (Odd_Succ x) b = Even_Succ (plusOddOdd x b)


plusEvenOdd :  Even n  ->  Odd m
             -------------------
           ->     Odd (n+m)
plusEvenOdd Even_Zero Odd_one = Odd_one
plusEvenOdd Even_Zero (Odd_Succ x) = Odd_Succ (plusEvenOdd Even_Zero x)
plusEvenOdd (Even_Succ x) b = Odd_Succ (plusEvenOdd x b)


plusNullOdd :    Odd m
              ------------
            -> Odd (m+0)
plusNullOdd Odd_one = Odd_one
plusNullOdd (Odd_Succ x) = Odd_Succ (plusNullOdd x)



--data (=) : Type -> Type -> Type where
--    Refl : {a:Type}
--        ----------
--        -> a = a

--  rewrite .. in .. : a=b -> Pb 
--                     ----------
--                 ->     Pa

--  myrewrite : (p:a -> Type) -> {x:a} -> {y:a} -> x=y -> p y -> p x
--  myrewrite p Refl h = h

plusNull :   (n:Nat)
            ---------
          -> n+0 = n
plusNull 0 = Refl -- kui vasak ja parem võrdsed
plusNull (S k) = rewrite plusNull k in Refl
-- (S (plus k 0) = S k)
-- ((plus k 0) = k)
-- plussNull : k -> k + 0 = k
-- S k = S K
plusAssoc : (m:Nat) -> (n:Nat) -> (q:Nat)
            ------------------------------
          ->  m + (n + q) = (m + n) + q
plusAssoc 0 n q = Refl
plusAssoc (S k) n q = rewrite plusAssoc k n q in Refl
-- S (plus k (plus n q)) = S (plus (k n) q)
-- (plus k (plus n q)) = (plus (plus k n) q)
-- (k + (n + q)) = ((k + n) + q)
-- plusAssoc : m -> n -> q -> m + (n + q) = (m + n) + q
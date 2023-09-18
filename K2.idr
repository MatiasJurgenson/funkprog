module K2
import Data.Monoid.Exponentiation --rlwrap idris2 --find-ipkg K2.idr

fst : (a, b) -> a
fst (a, _) = a


-- varjame sisseehitatud listi pikkuse arvutuse
%hide Prelude.List.length
 
length : List a -> Int
length [] = 0
length (x::xs) = 1 + length xs


-- varjame sisseehitatud konkateneerimise arvutuse
%hide Prelude.Types.List.(++)
 
infixr 7 ++ -- kasutame kahe argumendi keskel --paremasotsatiivne -- number 7 on perioteet -- ++ mille kohta käib
(++) : List a -> List a -> List a
(++) [] ys = ys
(++) (x::xs) ys =  x :: K2.(++) xs ys -- listi lisamine
-- lisab kõik x listis olevad elemendid ükshaaval ja siis lisab kõik y listi elemendid


replicate : Int -> a -> List a
replicate 0 x = []
replicate n x = x :: replicate (n-1) x 


take : Int -> List a -> List a
take _ [] = []
take 0 (x::xs) = []
take n (x::xs) = x :: take (n-1) xs


sum : List Integer -> Integer
sum [] = 0
sum (x::xs) = x + sum xs


drop : Int -> List a -> List a
drop _ [] = []
drop 0 xs = xs
drop n (x::xs) = drop (n-1) xs


--peidame sisseehitatud funktsiooni
%hide Prelude.Types.List.reverse
 
reverse : List a -> List a
--reverse [] = []
--reverse (x::xs) = (reverse xs) :: x
reverse xs = reverse' xs []
    where
        reverse' : List a -> List a -> List a
        reverse' [] acc = acc
        reverse' (x::xs) acc = reverse' xs (x::acc)


esimesed : List (a, b) -> List a
esimesed [] = []
esimesed ((x,y)::xs) = x :: esimesed xs


otsi : Integer -> List Integer -> Bool
otsi _ [] = False -- kui list tühi siis ei leidu
otsi n (x::xs) = f n
    where 
        f : Integer -> Bool
        f n with (n==x)
            f n | True = True
            f n | False = otsi n xs -- kui arv ole võrde siis vaatame kas järgmine arv on otsitav

dropLast : List a -> List a
dropLast [] = []
dropLast [_] = [] -- kui üheelemdiniline list siis tagastab tühja
dropLast (x::xs) = x :: dropLast xs -- kui list on suurem kui 1 lisab x ja läheb edasi

--Sõne ja tähemärkide listi vahel teisendamiseks kasuta funktsioone 'unpack' ja 'pack'. 
lisa' : Int -> Char -> List Char -> List Char
lisa' _ c [] = [c]
lisa' 0 c cs = c :: cs -- lisab vastavasse kohta
lisa' i c (x::xs) = 
    case (i<0) of -- otsib kohta kuhu lisada
        True => c :: x :: xs
        False => x :: lisa' (i-1) c xs    


lisa : Int -> Char -> String -> String 
lisa i x ys = pack (lisa' i x (unpack ys))


arvuta : List (Double, Nat) -> Double -> Double
arvuta [] _ = 0
arvuta ((a,n) :: xs) x = a * x ^ n + arvuta xs x

--tärn

-- x :: asi kuni leiab \

--lines' : List Char -> List Char -> List String -> List String
--lines' [] acc stringAcc = ((pack acc) :: stringAcc)
--lines (x::xs) acc stringAcc = f x
--    where 
--        f : Char -> String
--        f x with (x=='\')
--            f x | True = lines' xs [] ((pack acc) :: stringAcc)
--            f x | False = lines' xs (x :: acc) stringAcc
--
abi : List Char -> List Char
abi [] = []
abi (x::xs) = f x 
    where 
        f : Char -> List Char
        f x with (x=='\n')
            f x | True = []
            f x | False = x :: abi xs
            

lines : String -> List String
lines "" = []
lines x = pack (abi (unpack x)) :: []


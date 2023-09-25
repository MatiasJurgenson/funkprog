module K3

-- foldr (#) a [x1, x2, ..., xn] = x1 # (x2 # (... # (xn # a)))
foldr : (a -> b -> b) -> b -> List a -> b
foldr _ a []        = a
foldr f a (x :: xs) = f x (K3.foldr f a xs)

-- foldl (#) a [x1, x2, ..., xn] = (((a # x1) # x2) # ...) # xn

-- funk --baas --lit
foldl : (b -> a -> b) -> b -> List a -> b
foldl _ a []        = a
foldl f a (x :: xs) = K3.foldl f (f a x) xs

-- map f [x1, x2, ..., xn] = [f x1, f x2, ..., f xn]
map : (a -> b) -> List a -> List b
map _ []        = []
map f (x :: xs) = f x :: map f xs

--näited
sumList : List Int -> Int
sumList []     = 0
sumList (x :: xs) = x + sumList xs

sumList' : List Int -> Int
sumList' = K3.foldr (+) 0

--ül-d
filter'' : (a -> Bool) -> List a -> List a
filter'' f [] = [] 
filter'' f (x::xs) = if (f x)
    then x :: filter'' f xs --kui tõene lisab listi
    else filter'' f xs --vale korral ei lisa

filter' : (a -> Bool) -> List a -> List a
filter' f xs = K3.foldr (\x,acc => if (f x)
    then x :: acc
    else acc) [] xs 

filter''' : (a -> Bool) -> List a -> List a
filter''' f xs = K3.foldr g [] xs
    where 
    g : a -> List a -> List a
    g x xs = if (f x) then x :: xs else xs


nullid1 : List Int -> Int
nullid1 [] = 0
nullid1 (0::xs) = 1 + nullid1 xs
nullid1 (_::xs) = nullid1 xs

nullid2 : List Int -> Int
nullid2 xs = K3.foldr (\x,acc => 
    if (x==0)
    then 1 + acc
    else acc) 0 xs

nullid2' : List Int -> Int
nullid2' xs = K3.foldr f 0 xs
    where 
    f : Int -> Int -> Int 
    f 0 acc = 1 + acc 
    f x acc = acc

--funktsioonidega sum ja map
nullid3 : List Int -> Int
nullid3 xs = sum (K3.map f xs) -- kui on 0 teeb üheks, kui muu siis 0-ks ja võtab sum siis saamegi 0-de summa
    where
    f : Int -> Int
    f x = if (x==0) then 1 else 0


nullid4 : List Int -> Nat
nullid4 xs = length (filter' (==0) xs)
-- nullid4 xs = length $ filter' (==0) xs
-- nullid4 xs = length . filter' (==0) 


nullid5 : List Int -> Int
nullid5 xs = sum [ 1 | x <- xs, x == 0] --käime listi läbi, võtame elemendi, kui kehtib tingimus, lisatakse 1

length' : List a -> Int
length' xs = K3.foldl (\acc,x => 1+acc) 0 xs


productList : List Int -> Int
-- funktsioon --baas --list
productList xs = K3.foldr (*) 1 xs  


append' : List a -> List a -> List a
append' xs ys = K3.foldr (::) ys xs


isEven : Nat -> Bool
isEven Z         = True
isEven (S Z)     = False
isEven (S (S n)) = isEven n
 
all' : (a -> Bool) -> List a -> Bool
all' f xs = K3.foldr (\x,acc => acc && f x) True xs


reverse' : List a -> List a
reverse' = K3.foldl rev df
  where
    df : List a --baasjuht
    df = []
    rev : List a -> a -> List a
    rev xs y = y :: xs


eemaldaNullid : List Int -> List Int
eemaldaNullid = K3.foldr rem df
  where
    df : List Int
    df = []
    rem : Int -> List Int -> List Int
    rem x ys = if (x>0) then x::ys else ys

--map sum
allEqual : List Int -> Bool
allEqual [] = True
allEqual (x::xs) = g (K3.foldr (*) 1 (K3.map f xs)) -- kui arv on võrdne algse x-ga siis muudab 1-ks muidu 0-ks. korrutame kokku, kui 0 siis false, kui 1 siis true
    where
    f : Int -> Int
    f y = if (y==x) then 1 else 0
    g : Int -> Bool
    g 0 = False
    g _ = True


unzip' : List (a, b) -> (List a, List b)
unzip' = K3.foldr f z
  where
    z : (List a, List b) --baasjuht
    z = ([], []) 
    f : (a, b) -> (List a, List b) -> (List a, List b) --list mida tahame lahti teha, acc, tulemus
    f (a, b) (as, bs) = (a::as, b::bs) -- võtame () ja lisame acc-i

--foldr
removeAll1 : Int -> List Int -> List Int
removeAll1 n xs = K3.foldr f [] xs
    where
    f : Int -> List Int -> List Int
    f x acc = if (x==n) then acc else x::acc

--filter ||
removeAll2 : Int -> List Int -> List Int
removeAll2 n xs = filter' (/=n) xs --/= == not equal7

--sellega vist [ 1 | x <- xs, x == 0]
removeAll3 : Int -> List Int -> List Int
removeAll3 n xs = [ x | x <- xs, x /= n]

-- any' : (a -> Bool) -> List a -> Bool
-- any' p xs = K3.foldr (||) False (K3.map p xs)
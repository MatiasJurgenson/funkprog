import System.Random

-- Ülesanne 1: 
-- Leia järgnevate substitutsioonide tulemused.

-- a) (λf. (λg. g x)(λx. f x)(λy. x y))[x→y] =  (λf. (λg. g y)(λx. f x)(λz. y z))
--                -               -       

-- b) (λf. (λg. g x)(λx. f x)(λy. x y))[x→f] =  (λz. (λg. g f)(λx. z x)(λy. f y))
--                -               - 

-- c) (λf. (λg. g x)(λx. f x)(λy. x y))[x→(λy. x y)]= (λf. (λg. g (λy. x y))(λx. f x)(λy. (λy. x y) y))
--                -               - 

-- Ülesanne 2:
-- Funkstsioon yl1 arvutab True siis ja ainult siis, kui 
-- listis leidub paar (a,b), kus a ja b kaugus pole suurem kui 1.0.

yl1 : List (Double, Int) -> Bool
yl1 = foldr f False
    where f : (Double, Int) -> Bool -> Bool
          f (a,b) acc = abs (a - cast b) <= 1.0 || acc

-- Näiteks:
-- yl1 [] == False
-- yl1 [(1.1, 2)] == True               -- 2 - 1.1 == 0.9 <= 1.0
-- yl1 [(1.1, 3),(2.2, 2)] == True      -- 2.2 - 2 == 0.2 <= 1.0
-- yl1 [(1.1, 3),(3.0, 0)] == False


-- Ülesanne 3:

data Puu a = Leht0 | Leht1 a | Haru (Puu a) a (Puu a) 

-- Funkstsioon yl2 saab argumendiks puu, mille elemendid
-- on paarid (i,x), ja väärtuse y. Tagastada tuleb listi kõik
-- esimesed komponendid i, mis on paaris väärtusega y (ehk x==y).

yl2 : Eq a => Puu (Int, a) -> a -> List Int
yl2 Leht0 y = []
yl2 (Leht1 (i, x)) y = if (x==y) then [i] else []
yl2 (Haru l (i, x) r) y = (yl2 l y) ++ (if (x==y) then [i] else []) ++ (yl2 r y)


-- Näiteks:
-- yl2 (Haru Leht0 (1, 'a') (Leht1 (2, 'b'))) 'a' == [1]
-- yl2 (Haru Leht0 (1, 'a') (Leht1 (2, 'b'))) 'b' == [2]
-- yl2 (Haru Leht0 (1, 'a') (Leht1 (2, 'b'))) 'c' == []
-- yl2 (Haru Leht0 (1, 'a') (Leht1 (1, 'a'))) 'a' == [1,1]


-- Ülesanne 4:

interface Veider a where
    f : a -> Integer
    g : Char -> a

-- Implementeeri liidese Veider instantsid nii, et 
-- kõik järgnevad avaldised oleks tõesed:

-- a) g 'x' == 10
-- b) f True + f 1 == g 'x'

Veider Integer where
    f a = 5
    g a = 10

Veider Bool where
    f a = 5
    g a = True 

-- Ülesanne 5:

t2ring : IO Int32
t2ring = randomRIO (1,6)

-- Protseduur yl4 küsib kasutajalt ühe rea teksti ja trükib 
-- selle välja selliselt, et iga sisestatud tähe kohta trükitakse
-- juhuslikult see täht kas ühekordselt või kahekordselt.

-- Vihje: kas teate, et on olemas unpack ja putChar
yl4 : IO () 
yl4 = do 
    putStrLn "Palun sisesta rida teksti"
    rida <- getLine
    -- foldr (\x, acc => t2ring >>= (\r => if (r > 3) then putChar x else putChar x >> putchar x) >> acc) (pure ()) (unpack rida)
    --putChar '\n'
    tryki (unpack rida)
    where 
        tryki : List Char -> IO ()
        tryki [] = pure ()
        tryki (x::xs) = do
            r <- t2ring
            if (r > 3) then do
                putChar x
                tryki xs
                else do 
                    putChar x
                    putChar x
                    tryki xs

-- Main> :exec yl4
-- Kalmer
-- KKalmmeerr

-- Main> :exec yl4
-- Tere hommikust!
-- TTere  hommikuust!

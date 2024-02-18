import Data.List
import System.Random

-- 1. substitutsioon

-- Tehke järgnevad substitutsioonid:
-- a. (𝜆𝑓.𝑓𝑦(𝜆𝑥.𝑥))[𝑦→𝜆𝑥𝑦.𝑓𝑦] == (𝜆z.z(𝜆𝑥𝑦.𝑓𝑦)(𝜆𝑥.𝑥))
-- b. (𝜆𝑥.𝑓(𝑥𝑥))(𝜆𝑥.𝑓(𝑥𝑥))[𝑓→𝜆𝑥𝑦.𝑦] == (𝜆z.(𝜆𝑥𝑦.𝑦)(zz))(𝜆z.(𝜆𝑥𝑦.𝑦)(zz))
-- c. (𝜆𝑥𝑔𝑦. 𝑥𝑔𝑦)[𝑔→𝑥𝑔𝑦] == (𝜆𝑥𝑔𝑦. 𝑥𝑔𝑦)    

-- 2. foldr

-- Ülesanne 2:
-- Kirjuta funkstsioon yl2, mis otsib argumentlistis paari, kus paari esimene 
-- komponent on True ja teine 0. Kui selline paar leidub, tagastatakse Just 
-- konstruktori all suurim sellise elemendi indeks -- mitmes element listis on 
-- sellisel kujul. Kui sellist paari ei leidu, tuleb tagastada Nothing.

yl2 : List (Bool, Int) -> Maybe Nat
yl2 xs = foldr f Nothing xs
    where f : (Bool, Int) -> Maybe Nat -> Maybe Nat
          f (True,0) acc = acc
          f (_, _) acc = Just (S 1)
        

-- Näiteks:
-- yl2 [] == Nothing
-- yl2 [(True, 0)] == Just 0
-- yl2 [(False, 0)] == Nothing
-- yl2 [(True, 1)] == Nothing
-- yl2 [(False, 0),(False, 1),(True, 1),(True, 0),(True, 0)] == Just 4


-- 3. liidesed

-- Kirjuta järgneva liidese instantsid nii, et võrdused kehtiksid!

interface Veider x where
    ff : x -> List x

-- Võrdused:
-- ff 2 == [2]
-- ff 3 == [1,2]
-- ff True == [True]
-- ff False == [True,True]

Veider Integer where
    ff 3 = [1,2]
    ff x = [x]

Veider Bool where
    ff False = [True, True]
    ff x = [x]


-- 4. Puud

-- Jõuluvana armastab väga puid ja seetõttu hoiab ta ka laste kohta 
-- andmeid puudes. Ta teab, kes on olnud üleannetu ja kes hea!
-- 
-- a) Laste nimede puust on vaja tekitada nimekiri. 
--   (Et seda siis kaks korda üle kontrollida!)
--
-- b) Jõuluvanal on vaja sorteerida puust välja kõik head lapsed.
--  Kirjuta funktsioon naughty, mis jätab puu struktuuri samaks aga 
--  eemaldab heade laste sissekanded.
 

data Tree a = LeafJust a | LeafNothing | Branch (Tree a) (Tree a)

Eq a => Eq (Tree a) where
    (LeafJust x) == (LeafJust y) = x==y
    LeafNothing  == LeafNothing  = True
    (Branch x z) == (Branch y w) = x==y && z==w
    _            == _            = False

data Descr = Naughty | Nice 

Eq Descr where
    Naughty == Naughty = True
    Nice    == Nice    = True
    _       == _       = False

-- toList (Branch (Branch (LeafJust "x") LeafNothing)  (Branch LeafNothing   (LeafJust "y"))) == ["x", "y"]
-- toList (Branch (Branch (LeafJust "x") (LeafJust "a")) (Branch (LeafJust "b")   (LeafJust "y"))) == ["x","a","b","y"]

-- naughty (Branch LeafNothing (LeafJust ("Tiiu",Nice))) == Branch LeafNothing LeafNothing 
-- naughty (Branch LeafNothing (LeafJust ("Mari",Naughty))) == Branch LeafNothing (LeafJust "Mari") 
-- naughty (Branch (LeafJust ("Mari",Naughty)) (LeafJust ("Tiiu",Nice))) == Branch (LeafJust "Mari") LeafNothing


naughty : Tree (String,Descr) -> Tree String
naughty LeafNothing = LeafNothing
--kui hea siis asendab muidu jätab alles
naughty (LeafJust (x, y)) = if (y == Nice) then LeafNothing else (LeafJust x)
-- teeb läbi kõikide harudega
naughty (Branch l r) = Branch (naughty l) (naughty r) 

toList : Tree String -> List String
toList LeafNothing = []
--kui string, siis lisab
toList (LeafJust x) = [x]
-- teeb läbi kõikide harudega
toList (Branch l r) = (toList l) ++ (toList r)  

-- 5. Juhuarvud

-- Protseduur yl5 n m genereerib n juhuarvu nullist m-ni ja 
-- trükib välja genereeritud arvude summa.

yl5 : Int -> Int32 -> IO ()
yl5 n m = do
    -- genereerib n arvu 0-st m-ini
    xs <- sequence [randomRIO (the Int32 0, m) | x <- [1..n]]
    -- liidab kokku ja väljastab
    putStrLn $ "summa: " ++ show (sum xs)

-- Main> :exec yl5 1 30 
-- summa: 4
-- Main> :exec yl5 1 30 
-- summa: 16
-- Main> :exec yl5 10000 30 
-- summa: 151188
-- Main> :exec yl5 10000 30 
-- summa: 150341
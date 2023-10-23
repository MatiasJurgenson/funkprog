module K7

import Data.List
import System.Random

t2ring : IO ()
t2ring = do
    r <- randomRIO (the Int32 1, 6)
    printLn r

dialoog : IO ()
dialoog = do
    putStrLn "Mis on sinu nimi?"
    nimi <- getLine
    putStrLn $ "Tere, " ++ nimi ++ "!"

prindiArvud : List Int32 -> IO ()
prindiArvud [] = pure ()
prindiArvud (x::xs) = do
    printLn x
    prindiArvud xs 


readMaybe : IO (Maybe Int32)
readMaybe = do
  input <- getLine
  if all isDigit (unpack input) --saab string ja vaatab kas on arcud
    then pure (Just (cast input)) --kui on arvud
    else pure Nothing


loeArv : IO Int32
loeArv = do
    putStrLn "Sisesta arv"
    arv <- readMaybe
    case arv of 
        Nothing => do 
            putStrLn "Ei tunne sellist arvu"
            loeArv
        Just a => pure a

summa2 : IO ()
summa2 = do
    putStr "Esimene arv. "
    n1 <- loeArv
    putStr "Teine arv. "
    n2 <- loeArv
    putStr "Arvude summa: "
    printLn (n1+n2)


summaN1 : IO ()
summaN1 = do
    putStr "Mitu arvu soovid sisestada? "
    n <- loeArv
    loeJaLiida n 0
    where
        loeJaLiida : Int32 -> Int32 -> IO ()
        loeJaLiida 0 s = putStrLn $ "Arvude summa: " ++ cast s
        loeJaLiida n s = do
            x <- loeArv
            loeJaLiida (n-1) (s+x)

 
summaN2 : IO ()
summaN2 = do
    putStr "Mitu arvu soovid sisestada? "
    n <- loeArv
    --xs <- sequence (map (\x => loeArv) [1..n])
    --xs <- sequence [loeArv | x <- [1..n]]
    xs <- traverse (const loeArv) [1..n]
    putStrLn $ "Arvude summa: " ++ show (sum xs)

m2ng : IO ()
m2ng = do
    r <- randomRIO (the Int32 0, 10)
    putStrLn "Arva ära täisarv vahemikus nullist sajani!"
    n <- loeArv
    pakkumine n r 1
    where
        pakkumine : Int32 -> Int32 -> Int32 -> IO ()
        pakkumine n r acc = if (n==r)
            then do
                putStrLn $ "Ära arvasid! Oligi " ++ cast r ++ ". Pakkusid " ++ cast acc ++ " korda."
                else if (n < r) 
                    then do
                    putStrLn "Ei! Minu number on suurem"
                    n <- loeArv
                    pakkumine n r (acc+ 1)
                    else do 
                        putStrLn "Ei! Minu number on väiksem"
                        n <- loeArv
                        pakkumine n r (acc+ 1)
            
            
    
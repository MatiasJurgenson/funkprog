module K4

data Email = E String String
 
varmo     : Email
kalmer    : Email
karoliine : Email
matias    : Email
varmo     = E "varmo.vene"       "ut.ee"
kalmer    = E "kalmer.apinis"    "ut.ee"
karoliine = E "karoliine.holter" "ut.ee"
matias    = E "matias.jurgenson" "ut.ee"

--show kalmer == "kalmer.apinis@ut.ee"
Show Email where
  show (E nimi domeen) = nimi ++ "@" ++ domeen


--record on ainult ühe konstruktoriga andmetüüp, millele genereeritakse automaatselt funktsioonid, mis selle väljasid projetseerivad. 
record Kiri where
  constructor MkKiri
  saatja   : Email
  saajad   : List Email
  pealkiri : String
  sisu     : String

testkiri' : Kiri
testkiri' = MkKiri {
    saatja = matias,
    saajad = [E "heisi.kurig" "ut.ee"],
    pealkiri = "test",
    sisu = "siin on sisu"
}

testkiri : Kiri
testkiri = MkKiri matias [E "heisi.kurig" "ut.ee"] "pealkiri" "sisu"

pealkiriSisu : Kiri -> String
pealkiriSisu (MkKiri _ _ pealkiri sisu) = pealkiri ++ ": " ++ sisu
--pealkiriSisu kiri = pealkiri kiri ++ ": " ++ sisu kiri
--pealkiriSisu kiri =  kiri.pealkiri ++ ": " ++ kiri.sisu


data Tree a = Leaf | Branch (Tree a) a (Tree a)

--selleks et võrrelda võrrelda puid peab juba olemas olema liige
Eq a => Eq (Tree a) where
    Leaf == Leaf = True
    (Branch x z w) == (Branch y v s) = x==y && z==v && w==s
    _ == _ = False


height : Tree a -> Int
height Leaf = 0
height (Branch l _ r) = 1 + max (height l) (height r)


fold : (a -> b -> a -> a) -> a -> Tree b -> a
fold f a Leaf = a
fold f a (Branch l y r) = f (fold f a l) y (fold f a r) 


size : Tree a -> Nat
--size Leaf = 0
--size (Branch l y r) = size l + 1 + size r
size = fold (\l,_,r => l + 1 + r) 0


heightFold : Tree a -> Int
heightFold = fold(\l,_,r => 1 + max l r ) 0

memberOf : Eq a => a -> Tree a -> Bool
memberOf x = fold(\l,y,r => (x==y) || l || r) False


balanced' : Tree a -> (Bool,Int)
balanced' = fold(\(lb,lh),x,(rb,rh) => (abs (lh - rh) <= 1 && lb && rb, 1 + max lh rh )) (True, 0)

balanced : Tree a -> Bool
balanced Leaf = True
balanced (Branch l x r) = abs ((height l) - (height r)) <= 1 && balanced l && balanced r
--balanced tree = fst (balanced' tree)


gen : Int -> a -> Tree a
gen 0 _ = Leaf
gen y x = Branch (gen (y-1) x) x (gen (y-1) x)


tree2list : Tree a -> List a
tree2list Leaf = []
tree2list (Branch l x r) = tree2list l ++ x :: tree2list r 

--tree2list = fold(\l,x,r => l ++ x :: r) []
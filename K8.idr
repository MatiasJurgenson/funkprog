module K8

-- n = λf x. f**n x
-- succ = λn. λf x. n f (f x)
-- add = λm n. λf x. m f (n f x)
-- mul = λm n. λf x. m (n f) x
-- exp =  λm n. λf x. n m f x

-- 1 = λfx. f x
-- f**2 = f (f x)

-- add 1 1 => (λm n. λf x. m f (n f x)) 1 1 => λf x. 1 f (1 f x) => λf x. f (1 f x) => λf x. f (f x)
-- add 0 0 => 
-- mul 2 0 => (λm n. λf x. m (n f) x) 2 0 => λf x 2 (0 f) x => λf x. ((λf x. f**2 x) (0 f) x) => λ f x. 0 f (0 f x) => λf x. (λ f x. x) f ((λf x. x) f x) => λf x. (λf x. x) f x => λf x. x => x 
-- mul 2 3 =>
-- exp 2 2 =>
-- exp 2 0 => (λm n. λf x. n m f x) 2 0 => λf x. 0 2 f x => λf x. f x => 1



import Data.SortedSet
 
data Lam  = Var String          -- muutuja
          | App Lam   Lam       -- rakendus
          | Abs String Lam      -- abstraktsioon
 
showLam : Nat -> Lam -> String
showLam _ (Var x)   = x
showLam d (App f e) =
    showParens (d>1) (showLam 1 f++" "++showLam 2 e)
showLam d (Abs x e) =
    showParens (d>0) ("\\ "++x++". "++showLam 0 e)
 
Show Lam where
    show = showLam 0
 
Eq Lam where
    (Var x)   == (Var y)   = x==y
    (App x y) == (App z w) = x==z&&y==w
    (Abs x y) == (Abs z w) = x==z&&y==w
    _         == _         = False
 
 
freeVars : Lam -> SortedSet String
freeVars (Var x)   = singleton x
freeVars (App x y) = freeVars x `union` freeVars y
freeVars (Abs x y) = delete x (freeVars y)
 
subst : Lam -> String -> Lam -> Lam
subst (Var x) v r = if x==v then r else Var x
subst (App x y) v r = App (subst x v r) (subst y v r)
subst (Abs x y) v r =
    if v==x then Abs x y
    else if contains x (freeVars r) then subst (Abs x' (subst y x (Var x'))) v r
    else Abs x (subst y v r)
            where x' : String
                  x' = x++"'"

infixl 3 @@
(@@) : Lam -> Lam -> Lam
x @@ y = App x y

-- n = λf x. f**n x
-- succ = λn. λf x. n f (f x)
-- add = λm n. λf x. m f (n f x)
-- mul = λm n. λf x. m (n f) x
-- exp =  λm n. λf x. n m f x
 
true : Lam
true = Abs "x" (Abs "y" (Var "x"))
 
false : Lam
false = Abs "x" (Abs "y" (Var "y"))
 
cond : Lam
cond = Abs "t" (Abs "x" (Abs "y" (Var "t" @@ Var "x" @@ Var "y")))
 
 
num : Nat -> Lam
num n = Abs "f" (Abs "x" (app_f n)) where
    app_f : Nat -> Lam
    app_f 0 = Var "x"
    app_f (S k) = (Var "f") @@ (app_f k)
 
-- (\ x. x x)(\ x. x x)
inf : Lam
inf = Abs "x" (Var "x" @@ Var "x") @@ Abs "x" (Var "x" @@ Var "x")
 
succ : Lam
succ = Abs "n" (Abs "f" (Abs "x" (Var "n" @@ Var "f" @@ (Var "f" @@ Var "x"))))
 
add : Lam
add = Abs "m" (Abs "n" (Abs "f" (Abs "x"
            (Var "m" @@ Var "f" @@ (Var "n" @@ Var "f" @@ Var "x")))))
 
mul : Lam
mul = Abs "m" (Abs "n" (Abs "f" (Abs "x"
            (Var "m" @@ (Var "n" @@ Var "f") @@ Var "x"))))

-- \m n. \ f x. n m f x
expr : Lam
expr = Abs "m" (Abs "n" (Abs "f" (Abs "x"
    (Var "n" @@ Var "m" @@ Var "f" @@ Var "x"))))  

-- näiteks:
-- (show $ redA (cond @@ true @@ num 2 @@ num 3)) == "\\ f. \\ x. f (f x)"
-- (show $ redA (add @@ num 2 @@ num 3)) == "\\ f. \\ x. f (f (f (f (f x))))"
-- show $ redA (cond @@ true @@ num 2 @@ inf)  -- ei termineeru

--(show $ redN (cond @@ true @@ num 2 @@ num 3)) == "\\ f. \\ x. f (f x)"
--(show $ redN (add @@ num 2 @@ num 3)) == "\\ f. \\ x. f (f (f (f (f x))))"
--(show $ redN (cond @@ true @@ num 2 @@ inf))  == "\\ f. \\ x. f (f x)"

--aplikatiivjärjekord
redA : Lam -> Lam
redA (App e1 e2) = 
    case redA e1 of 
    Abs y b => redA (subst b y (redA e2))
    a => App a (redA e2)
redA (Abs x y) = Abs x (redA y)
redA t = t


--normaaljärjekord
redNx : Lam -> Lam   
redNx (App x y) =
    case redNx x of
      Abs z t => redNx (subst t z y)
      nx      => App nx (redNx y)
redNx (Abs x y) = Abs x (redNx y)
redNx t = t

redNwhnf : Lam -> Lam   
redNwhnf (App x y) =
    case redNx x of
      Abs z t => redNx (subst t z y)
      nx      => App nx y
redNwhnf (Abs x y) = Abs x y
redNwhnf t = t

redN : Lam -> Lam   
redN (App x y) =
    case redNwhnf x of
      Abs z t => redN (subst t z y)
      nx      => App nx (redN y)
redN (Abs x y) = Abs x (redN y)
redN t = t


--näiteks:
--(show (redA1 (num 3))) == "Nothing"
--(show (redA1 (cond @@ false))) == "Just \\ x. \\ y. (\\ x. \\ y. y) x y"
--(show (redA1 (succ @@ num 0))) == "Just \\ f. \\ x. (\\ f. \\ x. x) f (f x)"
--(show (redA1 (add @@ (succ @@ (num 0)) @@ num 0))) == "Just (\\ m. \\ n. \\ f. \\ x. m f (n f x)) (\\ f. \\ x. (\\ f. \\ x. x) f (f x)) (\\ f. \\ x. x)"

redA1 : Lam -> Maybe Lam
redA1 (App e1 e2) =
    case redA1 e1 of
        Just e1' => Just (App e1' e2)
        Nothing =>
            case redA1 e2 of
                Just e2' => Just (App e1 e2')
                Nothing =>
                    case e1 of
                        Abs y b => Just (subst b y e2)
                        na => Nothing
redA1 (Abs x y) = 
    case redA1 y of
        Nothing => Nothing
        Just y' => Just (Abs x y')
redA1 t = Nothing
 
-- testimiseks trükime välja kõi sammud.
printSteps : (Lam -> Maybe Lam) -> Lam -> IO ()
printSteps f l =
    case f l of
        Nothing => printLn l
        Just l' => do printLn l
                      printSteps f l'


redN1 : Lam -> Maybe Lam
redN1 (App e1 e2) =
    case redN1 e1 of
        Just e1' => Just (App e1' e2)
        Nothing =>
            case redN1 e2 of
                Just e2' => Just (App e1 e2')
                Nothing =>
                    case e1 of
                        Abs y b => Just (subst b y e2)
                        na => Nothing
redN1 (Abs x y) = 
    case redN1 y of
        Nothing => Nothing
        Just y' => Just (Abs x y')
redN1 t = Nothing
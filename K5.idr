module K5


--FV(λf. (λg. g x) (λx. f x)) -- (x)
--              -
--FV((λx. (λg. g x)) x) --(x)
--                   -
--FV(λg. (λf. f x) (λx. g x)) -- (x)
--              -


import Data.List
-- elem
import Data.SortedSet
-- empty, singleton, insert, delete, contains, union
 
data Lam = Var String | App Lam Lam | Abs String Lam
 
showLam : Nat -> Lam -> String
showLam _ (Var x)   = x
showLam d (App f e) = showParens (d>1) (showLam 1 f++" "++showLam 2 e)
showLam d (Abs x e) = showParens (d>0) ("\\ "++x++". "++showLam 0 e)
 
-- See on liides -- liideseid vaatame järgmises praksis.
Show Lam where
    show = showLam 0
 
-- t1 := \f. (\g. g x) (\x. f x)
t1 : Lam
t1 = Abs "f" (App (Abs "g" (App (Var "g") (Var "x"))) (Abs "x" (App (Var "f") (Var "x"))))
 
-- (\x. (\g. g x)) x
t2 : Lam
t2 = App (Abs "x" (Abs "g" (App (Var "g") (Var "x")))) (Var "x")
 
-- t3 := \g. (\f. f x) (\x. g x)
t3 : Lam
t3 = Abs "g" (App (Abs "f" (App (Var "f") (Var "x"))) (Abs "x" (App (Var "g") (Var "x"))))


fv : Lam -> SortedSet String
fv (Var x) = singleton x -- muutuja hulgas
fv (App e1 e2) = fv e1 `union` fv e2
fv (Abs x e) = delete x (fv e)
 
-- testimiseks on selgem kasutada liste
fvList : Lam -> List String
fvList = SortedSet.toList . fv


--(λf.(λg.gx)(λx.fx))[x→y] ==> (λf.(λg.gy)(λx.fx)) --vabad x-id vahetuvad
--
--((λx.(λg.gx))x)[x→(λx.x)] ==> ((λx.(λg.gx))(λx.x))
--
--(λg.(λf.fx)(λx.gx))[x→f] ==> (λg.(λz.zf)(λx.gx)) -- ei saanud kohe teha (kuna juba oli f), seega nimetame f-i ümber z-ks

subst : Lam -> String -> Lam -> Lam
subst (Var y) x e =
    if (x==y) then e else (Var y)

subst (App e1 e2) x e = 
    App (subst e1 x e) (subst e2 x e) --paneme App ette et uleksid õiged ajsad

subst (Abs y e1) x e = 
    case (x==y) of
        True => (Abs y e1)
        False =>
            case not (contains y (fv e)) of
                True => Abs y (subst e1 x e)
                False => 
                    let z = newv y in
                    subst (Abs z (subst e1 y (Var z))) x e

    where  
        newv : String -> String
        newv xs = xs++"'"


--:exec printLn (subst t1 "x" (Var "y"))

--λf.(λg.gx)(λx.fx)=α(λx.(λg.gx))x --ei ole sest App =/= Abs
--λf.(λg.gx)(λx.fx)=αλg.(λf.fx)(λx.gx) --on võrdsed


lamEq : List (String,String) -> Lam -> Lam -> Bool
lamEq v (Var x) (Var y) = elem (x, y) v || x==y
lamEq v (App e1 e2) (App e3 e4) = lamEq v e1 e3 && lamEq v e2 e4
lamEq v (Abs x e1) (Abs y e2) = 
    --let v' = (x,y) :: [(u,v) | (u,v)<-v,x/=u,y/=v] in -- <- == kuulub
    let v' = (x,y) :: filter (\(u,v) => x/=u && y/=v) v in
    lamEq v' e1 e2
lamEq v _ _ = False

-- See on liides -- liideseid vaatame järgmises praksis.
Eq Lam where
    x == y = lamEq [(x,x)| x <- fvList x ++ fvList y] x y
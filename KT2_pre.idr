%default total
 
-- 1) leia kõik reedeksid

-- b-reedeks = (λb. c) a
-- n-reedeks = λy. (λx.x) y
 
-- a) (λf. f((λx.x) 3)) (λx.x)
--           --------
--    ------------------------     
 
 
-- b) (λf. (λy. (λx.x) y) x)
--              ---------
--         --------------
--         -----------------


-- c) (λa. (λb. c) a) ((λx.x) c)
--         ----------  --------
--     --------------
--     ------------------------
 
-- 2) beeta-redutseeri normaalkujule normaal- ja aplikatiivjärjekorras

-- kui (λf. f) (λx.b) siis f -> (λx.b)
-- kui (λf. b) (λx.b) siis b
 
-- a) (λf. (λg. g f)) ((λx.x) a) (λx.b)  -- (λg. g f )[f → ((λx.x) a)]
-- N: (λf. (λg. g f)) ((λx.x) a) (λx.b)  -- g((λx.x) a)[g → (λx.b)]
--    --> (λg. g ((λx.x) a))  (λx.b)     -- b[x → ((λx.x)a)]
--    --> (λx.b) ((λx.x) a)              
--    --> b
-- A: (λf. (λg. g f)) ((λx.x) a) (λx.b)  -- x[x → a]
--    --> (λf. (λg. g f)) a (λx.b)       -- (λg. g f )[f → a]
--    --> (λg. g a) (λx.b)               -- ga[g → (λx.b)]
--    --> (λx.b) a                       -- b[x → a]
--    --> b
 
-- b) (λx. (λx.x)) ((λx. x) x)
-- N: (λx. (λx.x)) ((λx. x) x)
--    --> (λx. (λy.y)) ((λx. x) x)  -- (λy.y)[x → ((λx.x)x)]
--    --> (λy.y)
--    --> (λx. x)
-- A: (λx. (λx.x)) ((λx. x) x)      -- x[x → x]
--    --> (λx. (λx.x)) x
--    --> (λx. (λy.y)) x            -- (λy.y)[x → x]
--    --> (λy.y)
--    --> (λx. x)

-- c) (λf. f f f) ((λx.x) (λx.b))
-- N: (λf. f f f) ((λx.x) (λx.b))                          -- f f f [f → ((λx.x) (λx.b))]
--    --> ((λx.x) (λx.b)) ((λx.x) (λx.b)) ((λx.x) (λx.b))  -- x[x → (λx.b)]
--    --> (λx.b) ((λx.x) (λx.b)) ((λx.x) (λx.b))           -- b[x → ((λx.x) (λx.b))]
--    --> b ((λx.x) (λx.b))                                -- x[x → (λx.b)]
--    --> b (λx.b)                                         
-- A: (λf. f f f) ((λx.x) (λx.b))                          -- x[x → (λx.b)]
--    --> (λf. f f f) (λx.b)                               -- f f f [f → (λx.b)]
--    --> (λx.b) (λx.b) (λx.b)                             -- b[x → (λx.b)]
--    --> b (λx.b) 

-- 3) tüübi tuletamine
-- "Joonista" tüübituletuspuu, kirjuta välja kõik kitsendused ja
-- lahenda kogu avaldise tüüp ɣ2.
 
-- Γ ⊢ xᵝ ⇒ {α = β}                        -- var
-- Γ ⊢ (λxᵅ.eᵝ)ˠ ⇒ {γ = α → β} ∪ E         -- abs
-- Γ ⊢ (eᵅ eᵝ)ˠ ⇒ {α = β → γ} ∪ E1 ∪ E2    -- app 

-- Lihtsustuseks:
--  * ei pea kirjutama xᵅ ∈ Γ
--  * kitsendusi ei pea kirjutama puu sisse  (mis oli slaididel roheline)
-- 
-- a) ⊢ (λxᵅ¹. ((λyᵅ². yᵅ³)ˠ¹ xᵅ⁴)ᵝ¹)ˠ²
 
-- -------------
-- xᵅ¹,yᵅ² ⊢ yᵅ³
-----------------------    ----------  
-- xᵅ¹ ⊢ (λyᵅ². yᵅ³)ˠ¹     xᵅ¹ ⊢ xᵅ⁴
-- ----------------------------------
-- xᵅ¹ ⊢ ((λyᵅ². yᵅ³)ˠ¹ xᵅ⁴)ᵝ¹
-- -------------------------------
-- (λxᵅ¹. ((λyᵅ². yᵅ³)ˠ¹ xᵅ⁴)ᵝ¹)ˠ²
 
-- ɑ2=ɑ3, ɣ1=ɑ2→ɑ3, ɑ1=ɑ4, ɣ1=ɑ4→β1, ɣ2=ɑ1→β1
 
-- Lahendus: ɣ2 = ɑ→ɑ
 
 
-- b) ⊢ (λxᵅ¹. (xᵅ² (λyᵅ³. yᵅ⁴)ˠ¹)ᵝ¹)ˠ²

--              ---------------
--              xᵅ¹, yᵅ³ ⊢ yᵅ⁴
-- ----------   ------------------
-- xᵅ¹ ⊢ xᵅ²    xᵅ¹ ⊢ (λyᵅ³.yᵅ⁴)ˠ¹
-- -------------------------------
-- xᵅ¹ ⊢ (xᵅ²(λyᵅ³.yᵅ⁴)ˠ¹)ᵝ¹ 
-- ------------------------------
-- ⊢ (λxᵅ¹.(xᵅ²(λyᵅ³.yᵅ⁴)ˠ¹)ᵝ¹)ˠ²

-- α3 = α4, α1 = α2, γ1 = α3 → α4, α2 = γ1 → β1, γ2 = α1 → β1

-- lahendus: γ2 = ((α → α) → β) → β


-- c) ⊢ (λxᵅ¹. ((λyᵅ². (λzᵅ³. yᵅ⁴)ˠ¹)ˠ³ xᵅ⁵)ᵝ¹)ˠ²

-- -------------------
-- xᵅ¹, yᵅ², zᵅ³ ⊢ yᵅ⁴
-- -----------------------
-- xᵅ¹, yᵅ² ⊢ (λzᵅ³.yᵅ⁴)ˠ¹ 
-- ---------------------------  ----------
-- xᵅ¹ ⊢ (λyᵅ².(λzᵅ³.yᵅ⁴)ˠ¹)ˠ³  xᵅ¹ ⊢ xᵅ⁵
-- --------------------------------------
-- xᵅ¹ ⊢ ((λyᵅ².(λzᵅ³.yᵅ⁴)ˠ¹)ˠ³ xᵅ⁵)ᵝ¹
-- ----------------------------------------
-- ⊢ (λxα1.((λyᵅ².(λzᵅ³.yᵅ⁴)ˠ¹)ˠ³ xᵅ⁵)ᵝ¹)ˠ²

-- α2 = α4. γ1 = α3 → α4, γ3 = α2 → γ1, α1 = α5, γ3 = α5 → β1, γ2 = α1 → β1

-- lahendus: γ2 = α2 → (α3 → α2)


-- d) ⊢ (λxᵅ¹. ((λyᵅ². (λzᵅ³. zᵅ⁴)ˠ¹)ˠ³ xᵅ⁵)ᵝ¹)ˠ²

-- --------------------
-- xᵅ¹, yᵅ², zᵅ³ ⊢ zᵅ⁴
-- -----------------------
-- xᵅ¹, yᵅ² ⊢ (λzᵅ³.zᵅ⁴)ˠ¹
-- ---------------------------  ----------
-- xᵅ¹ ⊢ (λyᵅ².(λzᵅ³.zᵅ⁴)ˠ¹)ˠ³  xᵅ¹ ⊢ xᵅ⁵
-- ----------------------------------
-- xᵅ¹ ⊢ ((λyᵅ².(λzᵅ³.zᵅ⁴)ˠ¹)ˠ³ xᵅ⁵)ᵝ¹
-- --------------------------------------- 
-- ⊢ (λxᵅ¹.((λyᵅ².(λzᵅ³.zᵅ⁴)ˠ¹)ˠ³ xᵅ⁵)ᵝ¹)ˠ²

-- α3 = α4, γ1 = α3 → α4, γ3 = α2 → γ1, α1 = α5, γ3 = α5 → β1, γ2 = α1 → β1

-- lahendus: γ2 = α2 → (α4 → α4)

 
-- 4) sõltuvate tüüpidega programmeerimine
 
data Vect : Nat -> Type -> Type where
    Nil  : Vect 0 a
    (::) : a -> Vect n a -> Vect (1+n) a
 
topelt : Nat -> Nat
topelt 0 = 0
topelt (S k) = S (S (topelt k))
 
-- ex1 -- pane elemendid vaheldumisi  (NB! Kalmeril siin plugin juksib.)
sega : Vect n a -> Vect n a -> Vect (topelt n) a
sega [] [] = []
sega (x::xs) (y::ys) = x :: y :: (sega xs ys)
 
-- Main> sega [1,2,3] [30,20,10]
-- [1, 30, 2, 20, 3, 10]
 
concat : Vect n a -> Vect m a -> Vect (n+m) a
concat [] ys = ys
concat (x :: y) ys = x :: concat y ys
 
-- ex2 -- lamenda tabel
flatten : Vect n (Vect m a) -> Vect (n*m) a
flatten [] = []
flatten (xs :: ys) = 
    let zs = flatten ys in
    concat xs zs
 
-- Main> flatten [[1,2,3],[30,20,10]]
-- [1, 2, 3, 30, 20, 10]
 
-- ex3 -- viimane element
last : Vect (S n) a -> a
last (x :: []) = x
last (x :: (y :: ys)) = last (y :: ys) 
 
-- Main> last [1,2,3]
-- 3
 
-- ex4 -- korda n korda
repeat : (n:Nat) -> a -> Vect n a
repeat 0 x = []
repeat (S n) x = x :: repeat n x
 
-- Main> repeat 3 'a'
-- ['a', 'a', 'a']
 
-- ex5 -- lisa kõigile üks ette
appendAll : (n:Nat) -> Vect n a -> Vect n (Vect m a) -> Vect n (Vect (S m) a)
appendAll 0 [] [] = []
appendAll (S n) (x :: xs) (y :: ys) = (x :: y) :: appendAll n xs ys
 
-- Main> appendAll 3 [1,2,3] [[30],[20],[10]]
-- [[1, 30], [2, 20], [3, 10]]
 
-- ex6 -- transponeeri
transpose : (n:Nat) -> (m:Nat) -> Vect n (Vect m a) -> Vect m (Vect n a)
transpose 0 m [] = repeat m []
transpose (S k) m (x :: y) = appendAll m x (transpose k m y)
 
-- Main> transpose 3 2 [[1,2],[3,4],[5,6]]
-- [[1, 3, 5], [2, 4, 6]]
 
 
 
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
 
--ex7 -- lausearvutus
test1 : (a \/ b) /\ (a -> b)
        --------------------
    ->          b
test1 (ConI (DisjIl x) y) = y x
test1 (ConI (DisjIr x) y) = x
 
--ex8 -- lausearvutus
test2 : (a \/ b \/ c) /\ (b -> c)
        -------------------------
    ->         (a \/ c)
test2 (ConI (DisjIl (DisjIl x)) y) = DisjIl x
test2 (ConI (DisjIl (DisjIr x)) y) = DisjIr (y x)
test2 (ConI (DisjIr x) y) = DisjIr x
 
 
-- tuleb kasuks test3-s
mult0 : (k:Nat) -> 0 = k*0
mult0 0 = Refl
mult0 (S k) = mult0 k
 
-- NB! Nat ei ole tegelikult piiratud ressurss.
add : (1 _ : Nat) -> (1 _: Nat) -> Nat
add x 0 = x
add 0 (S k) = S k
add (S j) (S k) = 2+j+k
 
mul : (1 _ : Nat) -> (1 _: Nat) -> Nat
mul 0 0 = 0
mul (S k) 0 = 0
mul 0 (S k) = 0
mul (S j) (S k) = (S j)*(S k)
 
--ex9 -- mul on korrutamine
test3 : (a:Nat) -> (b:Nat)
        ------------------
    ->     mul a b = a*b
test3 0 0 = Refl
test3 0 (S k) = Refl
test3 (S k) 0 = mult0 k
test3 (S k) (S n) = Refl
 
--ex9 -- liitmisel S paremal
plus_n_Sm : (n:Nat)  ->  (m:Nat)
            --------------------
         -> n + (S m) = S (n+m)
plus_n_Sm 0 0 = Refl
plus_n_Sm 0 (S k) = Refl
plus_n_Sm (S k) n = rewrite plus_n_Sm k n in Refl
 
 
--ex10 -- topelt n arvutab n+n
topeltOk :    (n:Nat)
            --------------
        -> topelt n = n+n
topeltOk 0 = Refl
topeltOk (S n) = rewrite topeltOk n in rewrite plus_n_Sm n n in Refl
-- S (S (topelt n)) = S (plus n (S n))
-- S (topelt n) = S (plus n (S n))
-- topelt n = plus n (S n)

 
--ex11 -- foldr (::) [] on identsusfunktsioon
foldr_id : (xs:List a) -> foldr (::) [] xs = xs
foldr_id [] = Refl
foldr_id (x :: xs) = rewrite foldr_id xs in Refl
--foldr (::) [] xs = xs
-- x :: xs = x :: xs


foldl_rev : (xs:List Nat) -> map (plus 0) xs = xs
foldl_rev [] = Refl
foldl_rev (x :: xs) = 
    -- x :: map (plus 0) xs = x :: xs
    rewrite foldl_rev xs in  
    -- x :: xs = x :: xs
    Refl
 
-- 6) lineaarsed tüübid
 
namespace Lin
    public export
    data List : Type -> Type where
        Nil  : Lin.List a
        (::) : (1 _ : a) -> (1 _ : Lin.List a) -> Lin.List a
 
--ex12 -- rakendab funktsioonid järjest
seqL : (1 _: Lin.List ((1 _ : a) -> a)) -> (1 _: a) -> a
seqL [] x = x
seqL (f :: fs) x = seqL fs (f x)

 
-- Main> seqL [add 1, add 2] 0
-- 3
-- Main> seqL [add 3, mul 0, add 4] 0
-- 4
 
--ex13 -- foldr, kus akumulaator on lineaarne
foldLf : ((1 _: a) -> b -> a) -> Prelude.List b -> (1 _: a) -> a
foldLf f [] y = y
foldLf f (x :: xs) y = foldLf f xs (f y x)
 
-- Main> foldLf (\ x, y => add x y) [1,3] 0
-- 4
-- Main> foldLf (\ x, y => add x y) [2,3] 1
-- 6
 
--ex14 -- foldr, kus akumulaator ja list on lineaarsed
foldLl : ((1 _ : a) -> (1 _ : b) -> a) -> (1 _ : Lin.List b) -> a -> a
foldLl f [] y = y
foldLl f (x :: xs) y = f (foldLl f xs y) x
 
-- Main> foldLl (\ x, y => mul x y) [2,0] 1
-- 0
-- Main> foldLl (\ x, y => mul x y) [2,5] 1
-- 10
 
append : (1 _ : Lin.List a) -> (1 _ : Lin.List a) -> Lin.List a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys
 
--ex15 -- lineaarse listi lamendamine
concatL : (1 _ : Lin.List (Lin.List a)) -> Lin.List a
concatL [] = []
concatL ([] :: xs) = concatL xs
concatL (ys :: xs) = append ys (concatL xs) -- paneb kokku ja läheb edasi
 
-- Main> concatL [[],[],[]]
-- []
-- Main> concatL [[1,2,3],[],[4,5]]
-- [1, 2, 3, 4, 5]
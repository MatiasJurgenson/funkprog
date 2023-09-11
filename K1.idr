module K1

sumInt : Int -> Int
sumInt 0 = 0
sumInt n = sumInt (n-1) + n

fib : Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

--esimesed kaks int-i on väärtused ja viimane on tagastatav
modulo : Int -> Int -> Int
modulo x y = f x
    where 
        f : Int -> Int
        --f n = if (n<y) then n else f (n-y) --pole soovitatud
        f n with (n<y)
            f n | True = n
            f n | False = f (n-y)

syt : Int -> Int -> Int
syt x 0 = x
syt x y = syt y (x `mod` y) --12 mod 8 ülejääk on 4

hanoi : Int -> Int
hanoi 1 = 1
hanoi n = 2 * hanoi (n - 1) + 1

ack : Int -> Int -> Int
ack 0 n = n + 1
ack m 0 = ack (m-1) 1
ack m n = ack (m-1) (ack m (n-1)) -- saab ka ack m n = ack (m-1) $ ack m (n-1) -- peale $ on kõik argument

aste : Int -> Int -> Int
aste x 0 = 1
aste x n = x * aste x (n-1)

qaste : Int -> Int -> Int
qaste x 0 = 1 
qaste x n = case mod n 2 == 0 of --töötab ka `mod`
    True => y * y
    False => x * y * y
    where 
        y : Int
        y = qaste x (div n 2)

ndiv : Int -> Int -> Int
ndiv x y = f x 0
    where -- defineerime f (funktsiooni)
        f : Int -> Int -> Int
        f n z with (n<y) -- if n<y then z else ...
            f n z | True = z
            f n z | False = f (n-y) (z+1)


korda : Int -> (Int -> Int) -> Int -> Int
korda 0 f x = x
korda n f x = f (korda (n - 1) f x)
 
inc : Int -> Int
inc x = x + 1

add : Int -> Int -> Int
add x y = korda x inc y

mul : Int -> Int -> Int
mul x y = korda x (add y) 0 --add argument on alati y (iga kord liidab y)

add5 : Int -> Int
add5 n = let k = 5 in
    n + k
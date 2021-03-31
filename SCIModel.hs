module SCIModel (T1, T2(..), mod1, mod2, m1, m2, s1, s2) where
import SCITypes (SCIStruct(..), SCIModel(..))
import SCIHelper (UnOp, BinOp, UnRel)

-- Define two SCI-models and assignment functions for tests

type T1 = Integer
n1 :: UnOp T1
n1 x = 3 - x

a1 :: BinOp T1
a1 = min

o1 :: BinOp T1
o1 = max

i1 :: BinOp T1
i1 x = o1 (n1 x)

e1 :: BinOp T1
e1 x y = a1 (i1 x y) (i1 y x)

d1 :: BinOp T1
d1 x y = if x == y then 3 else 0

r1 :: UnRel T1
r1 x = x > 1

u1 = [0, 1, 2, 3]

m1 = SCIStruct n1 a1 o1 i1 e1 d1
mod1 = SCIModel u1 m1 r1

s1 :: String -> T1
s1 "x" = 0
s1 "y" = 1
s1 "z" = 2
s1 _ = 3

data T2 = False1 | False2 | False3 | True1 deriving (Eq, Ord, Show)

n2 :: UnOp T2
n2 True1 = False1
n2 _ = True1

a2 :: BinOp T2
a2 False1 _ = False1
a2 _ False1 = False1
a2 False2 _ = False2
a2 _ False2 = False2
a2 False3 _ = False3
a2 _ False3 = False3
a2 _ _ = True1

o2 :: BinOp T2
o2 x y = n2 (a2 (n2 x) (n2 y))

i2 :: BinOp T2
i2 x = o2 (n2 x)

e2 :: BinOp T2
e2 x y = a2 (i2 x y) (i2 y x)

d2 :: BinOp T2
d2 x y = if x == y then True1 else False1

u2 = [ False1, False2, False3, True1 ]

r2 :: UnRel T2
r2 x = x == True1

m2 = SCIStruct n2 a2 o2 i2 e2 d2
mod2 = SCIModel u2 m2 r2

s2 :: String -> T2
s2 "x" = False1
s2 "y" = False2
s2 "z" = False3
s2 _ = True1

-- Define an invalid model

data T3 = F1 | F2 | F3 | Tr1 | Tr2 deriving (Eq, Ord, Show)

n3 :: UnOp T3
n3 Tr1 = F1
-- n3 Tr2 = Tr2
n3 _ = Tr1

a3 :: BinOp T3
a3 F1 _ = F1
a3 _ F1 = F1
a3 F2 _ = F2
a3 _ F2 = F2
a3 F3 _ = F3
a3 _ F3 = F3
a3 _ _ = Tr1

o3 :: BinOp T3
o3 x y = n3 (a3 (n3 x) (n3 y))

i3 :: BinOp T3
i3 x = o3 (n3 x)

e3 :: BinOp T3
e3 x y = a3 (i3 x y) (i3 y x)

d3 :: BinOp T3
d3 x y = if x == y then Tr1 else F1

u3 = [ F1, F2, F3, Tr1, Tr2 ]

r3 :: UnRel T3
r3 x = x == Tr1 || x == Tr2

m3 = SCIStruct n3 a3 o3 i3 e3 d3
mod3 = SCIModel u3 m3 r3

s3 :: String -> T3
s3 "x" = F1
s3 "y" = F2
s3 "z" = F3
s3 _ = Tr1

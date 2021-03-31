module SCIHelper (allSq, getRight, UnOp, BinOp, UnRel, BinRel) where

appendUnique :: (Eq t) => t -> [t] -> [t]
appendUnique x y = if x `elem` y then y else y ++ [x]

allAll :: (a -> b -> Bool) -> [a] -> [b] -> Bool
allAll f xs ys = and [ f x y | x <- xs, y <- ys ]

allSq :: (a -> a -> Bool) -> [a] -> Bool
allSq f xs = allAll f xs xs

getRight :: Either a b -> b
getRight (Right v) = v

type UnOp t = t -> t
type BinOp t = t -> t -> t
type UnRel t = t -> Bool
type BinRel t = t -> t -> Bool

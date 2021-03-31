module SCITest (mod3, mod4, putCompare, putTruths, putSizes, putSubs, putCheckModel, putRSTree, putRSProof, putRSDecision, putRSResult, putRSSizes, putRSLengths) where
import SCITypes (SCIFormula(..), SCIModel(..), SCIStruct(..),
                sciLength, sciDepth, sciTruth, sciSub, sciEval, sciCheckModel)
import SCIModel(T1,T2,m1,m2,mod1,mod2,s1,s2)
import RSProof (RSSystem(..), RSTree(..), rsIsProof, rsProof, rsTreeSize, rsTreeDepth)
import SCIRS (SCINode(..), FormulaLists(..))
import SCIHelper(UnOp, BinOp, UnRel)

-- Define invalid models

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

type T4 = T3
n4 :: UnOp T4
n4 Tr1 = F1
n4 Tr2 = F2
n4 _ = Tr1

a4 = a3

o4 Tr1 F1 = F2
o4 x y = o3 x y

i4 = i3
e4 = e3
d4 = d3
u4 = u3
r4 = r3

m4 = SCIStruct n4 a4 o4 i4 e4 d4
mod4 = SCIModel u4 m4 r4

s4 = s3



-- Output test results

putCompare :: SCIFormula -> SCIFormula -> IO ()
putCompare f1 f2 =
    putStrLn $ show f1 ++ " " ++ show (compare f1 f2) ++ " " ++ show f2

putTruths :: SCIFormula -> IO ()
putTruths f =
    putStrLn $ show f ++ ": " ++ show (sciEval m1 s1 f) ++ " (" ++ show (sciTruth mod1 s1 f) ++ "), " ++ show (sciEval m2 s2 f) ++ " (" ++ show (sciTruth mod2 s2 f) ++ ")"

putSizes :: SCIFormula -> IO ()
putSizes f =
    putStrLn $ show f ++ ": depth = " ++ show (sciDepth f) ++ ", length = " ++ show (sciLength f)

putSubs :: SCIFormula -> IO ()
putSubs f =
    putStrLn $ show f ++ ": " ++ show (sciSub f)

putCheckModel :: (Eq t) => SCIModel t -> String -> IO ()
putCheckModel mod name =
    putStrLn $ "Checking " ++ name ++ ": " ++ show (sciCheckModel mod)

-- RS trees

instance RSSystem Int where
--  rsIsLeaf = odd
  rsSuccessors x = if odd x then [] else [ x `div` 2 ]
  rsIsAxiomatic x = x == 1
  rsIsProven = rsIsAxiomatic
  rsIsRefuted x = odd x && x > 1

putRSSubFunc :: (t -> String) -> String -> RSTree t -> IO ()
putRSSubFunc f s (RSLeaf x) =
    putStrLn $ s ++ f x
putRSSubFunc f s (RSUnary x l) =
    putStrLn (s ++ f x) >> putRSSubFunc f (s ++ "  ") l
putRSSubFunc f s (RSBinary x l r) =
    putStrLn (s ++ f x) >> putRSSubFunc f (s ++ "  ") l >> putRSSubFunc f (s ++ "  ") r

putRSSubtree :: (Show t) => String -> RSTree t -> IO ()
putRSSubtree = putRSSubFunc show

putRSTree :: (Show t) => RSTree t  -> IO ()
putRSTree = putRSSubtree ""

putRSSubLengths :: String -> RSTree SCINode -> IO ()
putRSSubLengths = putRSSubFunc sciShowSizes

putRSDecision :: (Show t, RSSystem t) => RSTree t -> IO ()
putRSDecision n = if rsIsProof n then putRSProof n
                                 else putRSRefutedBranch n

putRSRefutedBranch :: (Show t, RSSystem t) => RSTree t -> IO ()
putRSRefutedBranch (RSLeaf x) = putStrLn $ "F " ++ show x
putRSRefutedBranch (RSUnary x l) = do
    putStrLn $ "F " ++ show x
    putRSRefutedBranch l
putRSRefutedBranch (RSBinary x l r) = do
    putStrLn $ "F " ++ show x
    if rsIsProof l then putRSRefutedBranch r
                   else putRSRefutedBranch l

putRSResult :: (RSSystem t) => RSTree t -> IO ()
putRSResult n = if rsIsProof n then putStrLn "proven"
                               else putStrLn "unproven"

putRSSizes :: (RSSystem t) => RSTree t -> IO ()
putRSSizes n = putStrLn $ "Depth = " ++ show (rsTreeDepth n) ++ ", size = " ++ show (rsTreeSize n)

sciShowSizes :: SCINode -> String
sciShowSizes node = "(" ++ sciShowListSizes p ++ ", " ++ sciShowListSizes n ++ ")"
    where p = newF (pos node) ++ idF (pos node) ++ oldF (pos node)
          n = newF (neg node) ++ idF (neg node) ++ oldF (neg node)

sciShowListSizes :: [SCIFormula] -> String
sciShowListSizes l = show (length l) ++ ":" ++ show (sum ll) ++ ":" ++ show (maximum ll)
    where ll = 0: map sciLength l

putRSLengths :: RSTree SCINode -> IO ()
putRSLengths = putRSSubLengths ""

putRSSubproof :: (Show t, RSSystem t) => String -> RSTree t -> IO ()
putRSSubproof s n@(RSLeaf x) =
    putTF s n x
--    if rsIsProof n then putStr "T " else putStr "F "
--    putStrLn $ s ++ show x
putRSSubproof s n@(RSUnary x l) = do
--    if rsIsProof n then putStr "T " else putStr "F "
--    putStrLn $ s ++ show x
    putTF s n x
    putRSSubproof (s ++ "  ") l
putRSSubproof s n@(RSBinary x l r) = do
--    if rsIsProof n then putStr "T " else putStr "F "
--    putStrLn $ s ++ show x
    putTF s n x
    putRSSubproof (s ++ "  ") l
    putRSSubproof (s ++ "  ") r

putTF :: (Show t, RSSystem t) => String -> RSTree t -> t -> IO ()
putTF s n x = do
    if rsIsProof n then putStr "T " else putStr "F "
    putStrLn $ s ++ show x

putRSProof :: (Show t, RSSystem t) => RSTree t -> IO ()
putRSProof = putRSSubproof ""

module LTProof (LTSystem(..), LTTree(..), ltProof, ltIsProof,
                ltTreeSize, ltTreeDepth,
                showLTTree, showLTDecision, showLTResult) where

class (Eq node) => LTSystem node where
    ltIsLeaf :: node -> Bool
    ltSuccessors :: node -> [node]
    ltIsAxiomatic :: node -> Bool
    ltIsProven :: node -> Bool

    ltIsLeaf = null . ltSuccessors

data LTTree node =
    LTLeaf node
    | LTNonLeaf node [LTTree node]
    deriving (Eq)

ltProof :: (LTSystem node) => node -> LTTree node
ltProof node = makeLTProof node $ ltSuccessors node

makeLTProof :: (LTSystem node) => node -> [node] -> LTTree node
makeLTProof n [] = LTLeaf n
makeLTProof n s = LTNonLeaf n $ map ltProof s

ltIsProof :: (LTSystem node) => LTTree node -> Bool
ltIsProof (LTLeaf x) = ltIsAxiomatic x
ltIsProof (LTNonLeaf _ l) = all ltIsProof l

-- tree statistics

ltTreeDepth :: LTTree t -> Int
ltTreeDepth (LTLeaf _) = 1
ltTreeDepth (LTNonLeaf _ l) = 1 + maximum (map ltTreeDepth l)

ltTreeSize :: LTTree t -> Int
ltTreeSize (LTLeaf _) = 1
ltTreeSize (LTNonLeaf _ l) = 1 + sum (map ltTreeSize l)

-- show a proof tree

showLTSubFunc :: (t -> String) -> String -> LTTree t -> String
showLTSubFunc f s (LTLeaf x) = s ++ f x
showLTSubFunc f s (LTNonLeaf x l) =
    s ++ f x ++ concatMap (showLTSubFunc f (s ++ "  ")) l

showLTTree :: (Show t) => LTTree t  -> String
showLTTree = showLTSubFunc show "\n"

showLTDecision :: (Show t, LTSystem t) => LTTree t -> String
showLTDecision n = if ltIsProof n then showLTTree n
                                 else showLTRefutedBranch n

showLTRefutedBranch :: (Show t, LTSystem t) => LTTree t -> String
showLTRefutedBranch (LTLeaf x) = "F " ++ show x
showLTRefutedBranch (LTNonLeaf n l) =
    "F " ++ show n ++ "\n" ++
    showLTRefutedBranch (head $ filter (not . ltIsProof) l)

showLTResult :: (LTSystem t) => LTTree t -> String
showLTResult n = if ltIsProof n then "proven"
                               else "unproven"

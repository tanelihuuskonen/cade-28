module RSProof (RSSystem(..), RSTree(..), rsProof, rsIsProof, rsTreeDepth, rsTreeSize) where

class (Eq node) => RSSystem node where
    rsIsLeaf :: node -> Bool
    rsSuccessors :: node -> [node]
    rsIsAxiomatic :: node -> Bool
    rsIsProven :: node -> Bool
    rsIsRefuted :: node -> Bool
    rsIsFinal :: node -> Bool

--    rsIsLeaf x = rsSuccessors x == []
    rsIsLeaf = null . rsSuccessors
    rsIsFinal x = rsIsProven x || rsIsRefuted x

data RSTree node =
    RSLeaf node
    | RSUnary node (RSTree node)
    | RSBinary node (RSTree node) (RSTree node)
    deriving (Eq, Show)

rsTreeSize :: RSTree node -> Int
rsTreeSize (RSLeaf _) = 1
rsTreeSize (RSUnary _ s) = 1 + rsTreeSize s
rsTreeSize (RSBinary _ l r) = 1 + rsTreeSize l + rsTreeSize r

rsTreeDepth :: RSTree node -> Int
rsTreeDepth (RSLeaf _) = 1
rsTreeDepth (RSUnary _ s) = 1 + rsTreeDepth s
rsTreeDepth (RSBinary _ l r) = 1 + max (rsTreeDepth l) (rsTreeDepth r)

rsProof :: (RSSystem node) => node -> RSTree node
rsProof node = makeRSProof node (rsSuccessors node) (rsIsFinal node)

makeRSProof :: (RSSystem node) => node -> [node] -> Bool -> RSTree node
makeRSProof n [] _ = RSLeaf n
makeRSProof n _ True = RSLeaf n
makeRSProof n [s1] _ = RSUnary n (rsProof s1)
makeRSProof n [s1, s2] _ = RSBinary n (rsProof s1) (rsProof s2)
-- makeRSProof _ _ _ = 

rsIsProof :: (RSSystem node) => RSTree node -> Bool
rsIsProof (RSLeaf x) = rsIsProven x
rsIsProof (RSUnary _ l) = rsIsProof l
rsIsProof (RSBinary _ l r) = rsIsProof l && rsIsProof r

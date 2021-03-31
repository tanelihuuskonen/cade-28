module SCILTurf (SCILabFml(..), LTNode(..), ltIsProvable, startNode) where
import SCITypes (SCIFormula(..), sciNII)
import Data.List(union)
--import qualified Data.List.Ordered as O(union, member)
import LTProof (ltIsProof, ltProof, LTSystem(..), LTTree(..))

data SCILabFml =
    LFml {
        fml :: SCIFormula,
        pos :: Bool,
        label :: Int}
    | LEq {
        eqPos :: Bool,
        t, u :: Int}
    | LNEq {
        neqPos :: Bool,
        v, w :: Int}
    deriving (Eq)

data LTNode =
    LTNormalNode {
        newF, oldF :: [SCILabFml],
        freshLabel :: Int}
    | LTIdentityNode {
        newF, oldF :: [SCILabFml],
        expl :: Char} -- !!
    | LTEqContradictionNode {
        eqF :: SCILabFml,
        newF, oldF :: [SCILabFml]}
    | LTTruthContradictionNode {
        cTLF, cFLF :: SCILabFml,
        newF, oldF :: [SCILabFml]}
    | LTExhaustedNode {
        oldF :: [SCILabFml]}
    deriving (Eq)

showSLF :: SCILabFml -> String
showSLF (LFml f p l) = showPI p l ++ ":" ++ show f
showSLF (LEq p m n) = showPI p m ++ " == " ++ showPI p n
showSLF (LNEq p m n) = showPI p m ++ " /= " ++ showPI p n

showPI :: Bool -> Int -> String
showPI True n = "+" ++ show n
showPI False n = "-" ++ show n

instance Show SCILabFml where show = showSLF

showLTN :: LTNode -> String
showLTN LTNormalNode{newF=n, oldF=o, freshLabel=f}
    = "N(" ++ show f ++ "): n = " ++ show n ++", o = " ++ show o
showLTN LTIdentityNode{newF=n, oldF=o, expl = e}  -- !!
    = "Id(" ++ [e] ++ "): n = " ++ show n ++", o = " ++ show o -- !!
showLTN LTEqContradictionNode{eqF=e, newF=n, oldF=o}
    = "IC(" ++ show e ++ "): n = " ++ show n ++", o = " ++ show o
showLTN LTTruthContradictionNode{cTLF = ct, cFLF = cf, newF = n, oldF = o}
    = "TC: " ++ show ct ++ " # " ++ show cf ++ ", n = " ++ show n ++ ", o = " ++ show o
showLTN LTExhaustedNode{oldF = o}
    = "X: " ++ show o

shortLTN :: LTNode -> String
shortLTN LTNormalNode{freshLabel = f} = "N(" ++ show f ++ ")"
shortLTN LTIdentityNode{expl = e} = "I(" ++ [e] ++ ")"
shortLTN LTEqContradictionNode{} = "EC"
shortLTN LTTruthContradictionNode{} = "TC"
shortLTN LTExhaustedNode{} = "X"

instance Show LTNode where show = showLTN
-- instance Show LTNode where show = shortLTN

instance LTSystem LTNode where
    ltSuccessors = SCILTurf.ltSuccessors
    ltIsAxiomatic = SCILTurf.ltIsAxiomatic
    ltIsProven = SCILTurf.ltIsAxiomatic

showLTT :: (Show t) => LTTree t -> String
showLTT = showIndentedLTT "" ""
showIndentedLTT :: (Show t) => String -> String -> LTTree t -> String
showIndentedLTT p s (LTLeaf l) = p ++ s ++ show l
showIndentedLTT p s (LTNonLeaf n ts)
    = p ++ s ++ show n ++ concatMap (showIndentedLTT "\n" $ "  " ++ s) ts
instance (Show t) => Show (LTTree t) where show = showLTT

ltNormal :: SCIFormula -> Bool -> Int -> [[SCILabFml]]
ltNormal (Variable _) _ _ = [[]]
ltNormal (Not f) p n = [[LFml f (not p) n]]
ltNormal (Imply f g) True n
    = [[LFml f False n, LFml g False (n+1)],
        [LFml f False n, LFml g True (n+1)],
        [LFml f True n, LFml g True (n+1)]]
ltNormal (Imply f g) False n = [[LFml f True n, LFml g False n]]
ltNormal (Ident f g) True n =
    [[LFml f True n, LFml g True n],
     [LFml f False n, LFml g False n]]
ltNormal (Ident f g) False n =
    [[LFml f True n, LFml g True (n+1), LNEq True n (n+1)],
     [LFml f True n, LFml g False n],
     [LFml f False n, LFml g True n],
     [LFml f False n, LFml g False (n+1), LNEq False n (n+1)]]

ltIsProvable :: SCIFormula -> Bool
ltIsProvable = ltIsProof . ltProof . startNode

-- sciNII expresses everything in terms of Not, Imply, Ident
-- the start formula is negated and assigned label 1
startNode :: SCIFormula -> LTNode
startNode f = LTNormalNode [LFml (sciNII f) False 1] [] 2

ltIsAxiomatic :: LTNode -> Bool
ltIsAxiomatic LTEqContradictionNode{} = True
ltIsAxiomatic LTTruthContradictionNode{} = True
ltIsAxiomatic _ = False

ltIsRefuted (LTExhaustedNode _) = True
ltIsRefuted _ = False

ltSuccessors :: LTNode -> [LTNode]
ltSuccessors (LTIdentityNode [] o _) = [LTExhaustedNode o]
ltSuccessors (LTIdentityNode (n:ns) o _) = [idSucc n ns (n:o)]
ltSuccessors (LTNormalNode [] o _) = [LTIdentityNode o [] 'n'] -- old normal becomes new id
ltSuccessors (LTNormalNode (n@(LFml f pos _):ns) o fr)
    | isTruthContradiction n $ ns ++ o = [makeTruthContradictionNode n (n:ns) o]
    | elemFmlPos f pos o = SCILTurf.ltSuccessors $ LTNormalNode ns (o `union` [n]) fr
    | otherwise = applyRule (LTNormalNode ns (o `union` [n]) (fr + 2)) $ ltNormal f pos fr
ltSuccessors (LTNormalNode (n:ns) o fr)
    | isEqContradiction n $ ns ++ o = [makeEqContradictionNode n (n:ns) o]
    | otherwise = [LTNormalNode ns (o `union` [n]) fr]
ltSuccessors _ = []

isEqContradiction :: SCILabFml -> [SCILabFml] -> Bool
isEqContradiction (LNEq p m n) fs
    | m == n = True
    | otherwise = (LEq p m n) `elem` fs
isEqContradiction (LEq p m n) fs = (LNEq p m n) `elem` fs
isEqContradiction _ _ = False

isTruthContradiction :: SCILabFml -> [SCILabFml] -> Bool
isTruthContradiction (LFml f pos _) l = elemFmlPos f (not pos) l
isTruthContradiction _ _ = False

elemFmlPos :: SCIFormula -> Bool -> [SCILabFml] -> Bool
elemFmlPos f pos = any $ hasFmlPos f pos

hasFmlPos :: SCIFormula -> Bool -> SCILabFml -> Bool
hasFmlPos fml pos (LFml f p _) = fml == f && pos == p
hasFmlPos _ _ _ = False

makeTruthContradictionNode :: SCILabFml -> [SCILabFml] -> [SCILabFml] -> LTNode
makeTruthContradictionNode lf@(LFml fml pos _) l1 l2
    | pos = LTTruthContradictionNode lf nlf l1 l2
    | otherwise = LTTruthContradictionNode nlf lf l1 l2 where
        nlf = findLab fml (not pos) $ l1 ++ l2
        findLab f p (lg:lgs)
            | hasFmlPos f p lg = lg
            | otherwise = findLab f p lgs

makeEqContradictionNode :: SCILabFml -> [SCILabFml] -> [SCILabFml] -> LTNode
makeEqContradictionNode f@(LEq _ _ _) = LTEqContradictionNode f
makeEqContradictionNode (LNEq p u v) = LTEqContradictionNode (LEq p u v)

applyRule :: LTNode -> [[SCILabFml]] -> [LTNode]
applyRule base = map (addToNode base)

addToNode :: LTNode -> [SCILabFml] -> LTNode
addToNode (LTNormalNode n o fr) l = LTNormalNode (n `union` l) o fr

idSucc :: SCILabFml -> [SCILabFml] -> [SCILabFml] -> LTNode
idSucc f n o
    | isEqContradiction f $ n ++ o = makeEqContradictionNode f n o
    | isTruthContradiction f $ n ++ o = makeTruthContradictionNode f n o
    | canDoNot f $ n ++ o = doNot f (n `union` o)
    | canDoImply f $ n ++ o = doImply f (n `union` o)
    | canDoIdent f $ n ++ o = doIdent f (n `union` o)
    | canDoF f $ n ++ o = doF f (n `union` o)
    | canDoTran f $ n ++ o = doTran f (n `union` o)
    | null n = LTExhaustedNode (f:o)
    | otherwise = idSucc g ns (f:o) where
        g = head n
        ns = tail n

ordUnion :: (Ord t) => [t] -> [t] -> [t]
ordUnion x [] = x
ordUnion [] y = y
ordUnion (x:xs) (y:ys)
    | x < y = x : ordUnion xs (y:ys)
    | x > y = y : ordUnion (x:xs) ys
    | otherwise = x : ordUnion xs ys

elemFml :: SCIFormula -> [SCILabFml] -> Bool
elemFml f = any $ hasFml f

hasFml :: SCIFormula -> SCILabFml -> Bool
hasFml fml (LFml f _ _) = fml == f

doNot :: SCILabFml -> [SCILabFml] -> LTNode
doNot lf@(LFml (Not f) p l) lfs = LTIdentityNode (lf:(nlf:lfs)) [] '~'
    where
    nlf = head $ doNots f p l lfs
-- doNot _ _ = LTExhaustedNode []

doImply :: SCILabFml -> [SCILabFml] -> LTNode
doImply lf@(LFml (Imply f g) p l) lfs = LTIdentityNode (lf:(nlf:lfs)) [] '>'
     where
     nlf = head $ doImplies f g p l lfs

doIdent :: SCILabFml -> [SCILabFml] -> LTNode
doIdent lf@(LFml (Ident f g) p l) lfs = LTIdentityNode (lf:(nlf:lfs)) [] '='
     where
     nlf = head $ doIdents f g p l lfs

doF :: SCILabFml -> [SCILabFml] -> LTNode
doF lf lfs = LTIdentityNode (lf:(nlf:lfs)) [] 'F'
    where
    nlf = head $ doFs lf lfs

doTran :: SCILabFml -> [SCILabFml] -> LTNode
doTran lf lfs = LTIdentityNode (lf:(nlf:lfs)) [] 'T'
    where
    nlf = head $ doTrans lf lfs

notNull :: [t] -> Bool
notNull = not . null

canDoNot :: SCILabFml -> [SCILabFml] -> Bool
canDoNot (LFml (Not f) p l) lfs = notNull $ doNots f p l lfs
canDoNot _ _ = False

canDoImply :: SCILabFml -> [SCILabFml] -> Bool
canDoImply (LFml (Imply f g) p l) lfs = notNull $ doImplies f g p l lfs
canDoImply _ _ = False

canDoIdent :: SCILabFml -> [SCILabFml] -> Bool
canDoIdent (LFml (Ident f g) p l) lfs = notNull $ doIdents f g p l lfs
canDoIdent _ _ = False

canDoF :: SCILabFml -> [SCILabFml] -> Bool
canDoF lf@(LFml _ _ _) lfs = notNull $ doFs lf lfs
canDoF _ _ = False

canDoTran :: SCILabFml -> [SCILabFml] -> Bool
canDoTran lf@(LEq _ _ _) lfs = notNull $ doTrans lf lfs
canDoTran _ _ = False

doNots :: SCIFormula -> Bool -> Int -> [SCILabFml] -> [SCILabFml]
doNots f p l lfs = [makeEq p l wl |
                    u@(LFml uf up ul) <- lfs,
                    uf == f,
                    v@(LFml vf vp vl) <- lfs,
                    vf /= f,
                    up == vp,
                    matchEq up ul vl lfs,
                    w@(LFml wf wp wl) <- lfs,
                    wf == Not vf,
                    wl /= l,
                    wp == p,
                    makeEq p l wl `notElem` lfs]

matchEq :: Bool -> Int -> Int -> [SCILabFml] -> Bool
matchEq b m n l
    | m == n = True
    | otherwise = makeEq b m n `elem` l

makeEq :: Bool -> Int -> Int -> SCILabFml
makeEq b m n
    | m < n = LEq b m n
    | otherwise = LEq b n m

doImplies :: SCIFormula -> SCIFormula -> Bool -> Int -> [SCILabFml] -> [SCILabFml]
doImplies f g p l lfs = [makeEq p l yl |
                        u@(LFml uf up ul) <- lfs,
                        uf == f,
                        v@(LFml vf vp vl) <- lfs,
                        up == vp,
                        ul == vl,
                        w@(LFml wg wp wl) <- lfs,
                        wg == g,
                        x@(LFml xg xp xl) <- lfs,
                        xp == wp,
                        xl == wl,
                        vf /= f || xg /= g,
                        y@(LFml yh yp yl) <- lfs,
                        yh == Imply vf xg,
                        yl /= l,
                        yp == p,
                        makeEq p l yl `notElem` lfs]

doIdents :: SCIFormula -> SCIFormula -> Bool -> Int -> [SCILabFml] -> [SCILabFml]
doIdents f g p l lfs = [makeEq p l yl |
                        u@(LFml uf up ul) <- lfs,
                        uf == f,
                        v@(LFml vf vp vl) <- lfs,
                        up == vp,
                        ul == vl,
                        w@(LFml wg wp wl) <- lfs,
                        wg == g,
                        x@(LFml xg xp xl) <- lfs,
                        xp == wp,
                        xl == wl,
                        vf /= f || xg /= g,
                        y@(LFml yh yp yl) <- lfs,
                        yh == Ident vf xg,
                        yl /= l,
                        yp == p,
                        makeEq p l yl `notElem` lfs]


doFs :: SCILabFml -> [SCILabFml] -> [SCILabFml]
doFs lf@(LFml f p l) lfs = [ makeEq p l ul |
                        u@(LFml uf up ul) <- lfs,
                        uf == f,
                        up == p,
                        ul /= l,
                        makeEq p l ul `notElem` lfs]

doTrans :: SCILabFml -> [SCILabFml] -> [SCILabFml]
doTrans lf@(LEq p m n) lfs
    = filter ((flip notElem) (lf:lfs)) t where
    t = [makeEq p m um | (LEq _ um un) <- pfs,
                        un == n, makeEq p m um `notElem` pfs]
        ++ [makeEq p m un | (LEq _ um un) <- pfs,
                        um == n, makeEq p m un `notElem` pfs]
        ++ [makeEq p um n | (LEq _ um un) <- pfs,
                        un == m, makeEq p um n `notElem` pfs]
        ++ [makeEq p un n | (LEq _ um un) <- pfs,
                        um == m, makeEq p un n `notElem` pfs]
    pfs = [f | f@(LEq up _ _) <- lfs, up == p]

elemFmlPosLab :: SCIFormula -> Bool -> Int -> [SCILabFml] -> Bool
elemFmlPosLab f pos lab = any $ hasFmlPosLab f pos lab

hasFmlPosLab :: SCIFormula -> Bool -> Int -> SCILabFml -> Bool
hasFmlPosLab fml pos lab (LFml f p l) = fml == f && pos == p && lab == l

--

x :: SCIFormula
x = Variable "x"

y :: SCIFormula
y = Variable "y"

xy :: SCIFormula
xy = Ident x y

nxy :: SCIFormula
nxy = Ident (Not x) (Not y)

xynxy :: SCIFormula
xynxy = Imply xy nxy

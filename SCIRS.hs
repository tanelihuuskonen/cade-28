module SCIRS (SCINode(..), sciIsProvable, FormulaLists(..), startNode) where
import Data.List(nub, union)
import SCITypes (SCIFormula(..), SCIModel(..), SCIAssignment(..), sciShorten,
        sciSub, sciNII)
import RSProof (rsIsProof, rsProof, RSSystem(..))
import SCIHelper (UnOp)
import qualified Data.Map.Strict as M

data FormulaLists = FL { newF, idF, oldF :: [SCIFormula] }
    deriving (Eq, Show)

data SCINode =
    SCINormalNode {
        subs :: [SCIFormula],
        pos, neg :: FormulaLists }
    | SCIIdentityNode {
        subs :: [SCIFormula],
        pos, neg :: FormulaLists }
    | SCIAxNegationNode {
        ax :: SCIFormula,
        pos, neg :: FormulaLists }
    | SCIAxIdentityNode {
        ax :: SCIFormula,
        pos, neg :: FormulaLists }
    | SCIAxNINode {
        ax :: SCIFormula,
        pos, neg :: FormulaLists }
    | SCIExhaustedNode {
        pos, neg :: FormulaLists }
    deriving (Eq, Show)

instance RSSystem SCINode where
    rsSuccessors = sciRSSuccessors
    rsIsAxiomatic = sciIsAxiomatic
    rsIsProven = sciIsAxiomatic
    rsIsRefuted = sciIsRefuted

emptyFL = FL [] [] []
flNew f = FL [f] [] []
flId f = FL [] [f] []
flOld f = FL [] [] [f]

type SCIRule = SCIFormula -> [SCINode]

sciPosRule :: SCIRule
sciPosRule v@(Variable _) = [SCINormalNode [] (flOld v) emptyFL]
sciPosRule (Not f) = jointNew [] [f]
sciPosRule (Imply f g) = jointNew [g] [f]
sciPosRule eqn@(Ident f g)
    | f == g = [SCIAxIdentityNode eqn (flId eqn) emptyFL]
    | otherwise = [SCINormalNode [] (flId eqn) emptyFL]

sciNegRule v@(Variable _) = [SCINormalNode [] emptyFL (flOld v)]
sciNegRule (Not f) = jointNew [f] []
sciNegRule (Imply f g) = splitNew [f, Not g]
sciNegRule eqn@(Ident f g)
    | f == g = [SCINormalNode [] emptyFL emptyFL]
    | otherwise = [SCINormalNode [] emptyFL (FL [e] [eqn] [])]
    where e = sciNII $ Equiv f g

jointNew :: [SCIFormula] -> [SCIFormula] -> [SCINode]
jointNew p n = [SCINormalNode [] (FL p [] []) (FL n [] [])]

splitNew :: [SCIFormula] -> [SCINode]
splitNew = map sn where
    sn (Not f) = SCINormalNode [] emptyFL (flNew f)
    sn f = SCINormalNode [] (flNew f) emptyFL

sciIsProvable :: SCIFormula -> Bool
sciIsProvable = rsIsProof . rsProof . startNode

startNode :: SCIFormula -> SCINode
startNode f = SCINormalNode (sciSub g) (flNew g) emptyFL
    where g = sciNII f

sciIsAxiomatic :: SCINode -> Bool
sciIsAxiomatic SCIAxNegationNode{} = True
sciIsAxiomatic SCIAxIdentityNode{} = True
sciIsAxiomatic SCIAxNINode{} = True
sciIsAxiomatic _ = False

sciIsRefuted SCIExhaustedNode{} = True
sciIsRefuted _ = False

axIN :: SCIFormula -> FormulaLists -> FormulaLists -> Bool
axIN (Variable _) _ _ = False
axIN (Not _) _ _ = False
axIN (Imply _ _) _ _ = False
axIN (Ident f g) p n = (elemFL f p && elemFL g n) || (elemFL f n && elemFL g p)
-- axIN _ _ _ = True

sciRSSuccessors :: SCINode -> [SCINode]
sciRSSuccessors SCIAxNegationNode{} = []
sciRSSuccessors SCIAxIdentityNode{} = []
sciRSSuccessors SCIAxNINode{} = []
sciRSSuccessors SCIExhaustedNode{} = []
sciRSSuccessors (SCINormalNode s p@(FL (f:fs) i o) n)
    | elemFL f n = [SCIAxNegationNode f p n]
    | otherwise = applyRule (sciPosRule f) (SCINormalNode s (FL fs i o) n)
sciRSSuccessors (SCINormalNode s p n@(FL (f:fs) i o))
    | elemFL f p = [SCIAxNegationNode f p n]
    | axIN f p n = [SCIAxNINode (Not f) p n]
    | otherwise = applyRule (sciNegRule f) (SCINormalNode s p (FL fs i o))
sciRSSuccessors (SCINormalNode s p@(FL [] pi _) n@(FL [] ni no))
    | containsAx pi = [SCIAxIdentityNode (getAx pi) p n]
    | null ni = [SCIExhaustedNode p n]
    | otherwise = [SCIIdentityNode s p $ FL (ni `union` ids) [] no]
    where
        ax = getAx pi
        ids = map idd s
        idd f = Ident f f
sciRSSuccessors (SCIIdentityNode s p@(FL [] pi _) n@(FL (f@(Ident g h):fs) ni no))
    | axIN f p n = [SCIAxNINode (Not f) p n]
    | f `elem` pi = [SCIAxNegationNode f p n]
    | canTran f fs ni = [SCIIdentityNode s p $ doTran f fs ni no]
    | canIdNeg s f fs ni = [SCIIdentityNode s p $ doIdNeg s f fs ni no]
    | canIdImp s f fs ni = [SCIIdentityNode s p $ doIdImp s f fs ni no]
    | canIdId s f fs ni = [SCIIdentityNode s p $ doIdId s f fs ni no]
    | otherwise = [SCIIdentityNode s p $ FL fs nif no]
    where
        nif = ni `union` [f]
sciRSSuccessors (SCIIdentityNode _ p n) = [SCIExhaustedNode p n]

notNull :: [t] -> Bool
notNull = not . null

canTran :: SCIFormula -> [SCIFormula] -> [SCIFormula] -> Bool
canTran f fs ni = notNull $ findTran f fs ni

findTran :: SCIFormula -> [SCIFormula] -> [SCIFormula] -> [SCIFormula]
findTran f@(Ident g h) fs ni = [Ident g v |
    Ident u v <- fs ++ ni,
    h == u,
    v /= h,
    Ident g h `notElem` fs,
    Ident g h `notElem` ni]

doTran :: SCIFormula -> [SCIFormula] -> [SCIFormula] -> [SCIFormula] -> FormulaLists
doTran f fs ni no = FL (h:(f:fs)) ni no
    where h = head $ findTran f fs ni

canIdNeg :: [SCIFormula] -> SCIFormula -> [SCIFormula] -> [SCIFormula] -> Bool
canIdNeg s f@(Ident g h) fs ni
    = Not g `elem` s && Not h `elem` s && idn `notElem` (fs ++ ni)
    where idn = Ident (Not g) (Not h)

doIdNeg :: [SCIFormula] -> SCIFormula -> [SCIFormula] -> [SCIFormula] -> [SCIFormula] -> FormulaLists
doIdNeg s f@(Ident g h) fs = FL (idn:(f:fs))
    where idn = Ident (Not g) (Not h)

canIdImp :: [SCIFormula] -> SCIFormula -> [SCIFormula] -> [SCIFormula] -> Bool
canIdImp s f fs ni = notNull $ findIdImp s f fs ni

findIdImp :: [SCIFormula] -> SCIFormula -> [SCIFormula] -> [SCIFormula] -> [SCIFormula]
findIdImp s f@(Ident g h) fs ni = [Ident (Imply g u) (Imply h v) |
    Ident u v <- fs ++ ni,
    Imply g u `elem` s,
    Imply h v `elem` s,
    Ident (Imply g u) (Imply h v) `notElem` (fs ++ ni)]

doIdImp :: [SCIFormula] -> SCIFormula -> [SCIFormula] -> [SCIFormula] -> [SCIFormula] -> FormulaLists
doIdImp s f fs ni no = FL (h:(f:fs)) ni no
    where h = head $ findIdImp s f fs ni

canIdId :: [SCIFormula] -> SCIFormula -> [SCIFormula] -> [SCIFormula] -> Bool
canIdId s f fs ni = notNull $ findIdId s f fs ni

findIdId :: [SCIFormula] -> SCIFormula -> [SCIFormula] -> [SCIFormula] -> [SCIFormula]
findIdId s f@(Ident g h) fs ni = [Ident (Ident g u) (Ident h v) |
    Ident u v <- fs ++ ni,
    Ident g u `elem` s,
    Ident h v `elem` s,
    Ident (Ident g u) (Ident h v) `notElem` (fs ++ ni)]

doIdId :: [SCIFormula] -> SCIFormula -> [SCIFormula] -> [SCIFormula] -> [SCIFormula] -> FormulaLists
doIdId s f fs ni no = FL (h:(f:fs)) ni no
    where h = head $ findIdId s f fs ni

applyRule :: [SCINode] -> SCINode -> [SCINode]
applyRule ns base = map (unionNode base) ns

unionNode :: SCINode -> SCINode -> SCINode
unionNode (SCINormalNode s bp bn) (SCINormalNode _ p n)
    = SCINormalNode s (unionFL bp p) (unionFL bn n)
unionNode (SCINormalNode _ bp bn) (SCIAxIdentityNode a p n)
    = SCIAxIdentityNode a (unionFL bp p) (unionFL bn n)
unionNode (SCINormalNode _ bp bn) (SCIAxNegationNode a p n)
    = SCIAxNegationNode a (unionFL bp p) (unionFL bn n)
unionNode (SCINormalNode _ bp bn) (SCIAxNINode a p n)
    = SCIAxNINode a (unionFL bp p) (unionFL bn n)

elemFL :: SCIFormula -> FormulaLists -> Bool
elemFL f (FL n i o) = elem f n || elem f i || elem f o

unionFL :: FormulaLists -> FormulaLists -> FormulaLists
unionFL (FL n1 i1 o1) (FL n2 i2 o2)
    = FL (n1 `union` n2) (i1 `union` i2) (o1 `union` o2)

containsAx :: [SCIFormula] -> Bool
containsAx = any isAx

isAx :: SCIFormula -> Bool
isAx (Ident f g) = f == g
isAx _ = False

getAx :: [SCIFormula] -> SCIFormula
getAx = head . filter isAx

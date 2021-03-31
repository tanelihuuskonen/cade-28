module SCITypes (
    SCIError(..),
    SCIFormula(..),
    trapError,
    ThrowsError,
    SCIStruct(..),
    SCIModel(..),
    SCIAssignment,
    sciDepth,
    sciLength,
    sciSub,
    sciSubst,
    sciNII,
    sciLesser,
    sciShorten,
    sciEval,
    sciCheckModel,
    sciTruth) where
import Control.Monad.Except (catchError)
import Text.ParserCombinators.Parsec (ParseError)
import Data.List (union)
import SCIHelper (allSq, UnOp, BinOp, UnRel, BinRel)


data SCIError =
        SCIParsingError       ParseError
        | OtherError            String

showError :: SCIError -> String
showError (SCIParsingError err) = "Parsing error: " ++ show err
showError (OtherError msg) = "Error: " ++ msg

instance Show SCIError where show = showError

data SCIFormula =
          Variable      String
        | Not           SCIFormula
        | And           SCIFormula SCIFormula
        | Or            SCIFormula SCIFormula
        | Imply         SCIFormula SCIFormula
        | Equiv         SCIFormula SCIFormula
        | Ident         SCIFormula SCIFormula
        deriving (Eq, Ord)

type     ThrowsError = Either SCIError

trapError action = catchError action (return . Variable . const "(error)")

showSCI :: SCIFormula -> String
showSCI (Variable v) = v
showSCI (Not f) = "not " ++ showSCI f
showSCI (And f1 f2) = showSCIBin f1 "and" f2
showSCI (Or f1 f2) = showSCIBin f1 "or" f2
showSCI (Imply f1 f2) = showSCIBin f1 "->" f2
showSCI (Equiv f1 f2) = showSCIBin f1 "<->" f2
showSCI (Ident f1 f2) = showSCIBin f1 "=" f2

showSCIBin f1 op f2 = "(" ++ showSCI f1 ++ " " ++ op ++ " " ++ showSCI f2 ++ ")"

instance Show SCIFormula where show = showSCI

type SCIAssignment t = String -> t

data SCIStruct t = SCIStruct {
    sciNot :: UnOp t,
    sciAnd :: BinOp t,
    sciOr :: BinOp t,
    sciImply :: BinOp t,
    sciEquiv :: BinOp t,
    sciIdent :: BinOp t
}

data SCIModel t = SCIModel {
    dom :: [t],
    struct :: SCIStruct t,
    truth :: UnRel t
}

sciEval :: SCIStruct t -> SCIAssignment t -> SCIFormula -> t
sciEval _ s (Variable v) = s v
sciEval str s (Not f) = sciNot str (sciEval str s f)
sciEval str s (And f g) = sciAnd str (sciEval str s f) (sciEval str s g)
sciEval str s (Or f g) = sciOr str (sciEval str s f) (sciEval str s g)
sciEval str s (Imply f g) = sciImply str (sciEval str s f) (sciEval str s g)
sciEval str s (Equiv f g) = sciEquiv str (sciEval str s f) (sciEval str s g)
sciEval str s (Ident f g) = sciIdent str (sciEval str s f) (sciEval str s g)

sciTruth :: SCIModel t -> SCIAssignment t -> SCIFormula -> Bool
sciTruth m a f = truth m $ sciEval (struct m) a f

type UnCk t = UnOp t -> UnRel t -> UnRel t
type BinCk t = BinOp t -> UnRel t -> BinRel t

ckUnList :: UnCk t -> UnOp t -> UnRel t -> [t] -> Bool
ckUnList ck op rel = all (ck op rel)

ckBinList :: BinCk t -> BinOp t -> UnRel t -> [t] -> Bool
ckBinList ck op rel = allSq (ck op rel)

ckNot :: UnCk t
ckNot n r x = not (r x) == r (n x)

ckModelNot :: SCIModel t -> Bool
ckModelNot m = ckUnList ckNot (sciNot $ struct m) (truth m) (dom m)

ckModelBin :: BinCk t -> (SCIStruct t -> BinOp t) -> SCIModel t -> Bool
ckModelBin ck op m = ckBinList ck (op $ struct m) (truth m) (dom m)

-- check that truth-functional binop in model obeys given Boolean binop
ckTF :: BinOp Bool -> BinCk t
ckTF f op r x y = f (r x) (r y) == r (op x y)

ckAnd, ckOr, ckImply, ckEquiv :: BinCk t
ckAnd = ckTF (&&)
ckOr = ckTF (||)
-- implication is expressed by (||) . not
ckImply = ckTF $ (||) . not
ckEquiv = ckTF (==)

-- identity is not truth-functional
ckIdent :: (Eq t) => BinCk t
ckIdent d r x y = (x == y) == r (d x y)

ckModelAnd :: SCIModel t -> Bool
ckModelAnd = ckModelBin ckAnd sciAnd

ckModelOr :: SCIModel t -> Bool
ckModelOr = ckModelBin ckOr sciOr

ckModelImply :: SCIModel t -> Bool
ckModelImply = ckModelBin ckImply sciImply

ckModelEquiv :: SCIModel t -> Bool
ckModelEquiv = ckModelBin ckEquiv sciEquiv

ckModelIdent :: (Eq t) => SCIModel t -> Bool
ckModelIdent = ckModelBin ckIdent sciIdent

sciCheckModel :: (Eq t) => SCIModel t -> Bool
sciCheckModel m = ckModelNot m && ckModelAnd m && ckModelOr m && ckModelImply m && ckModelEquiv m && ckModelIdent m

sciDepth :: SCIFormula -> Integer
sciDepth (Variable _) = 0
sciDepth (Not f) = 1 + sciDepth f
sciDepth (And f g) = 1 + max (sciDepth f) (sciDepth g)
sciDepth (Or f g) = 1 + max (sciDepth f) (sciDepth g)
sciDepth (Imply f g) = 1 + max (sciDepth f) (sciDepth g)
sciDepth (Equiv f g) = 1 + max (sciDepth f) (sciDepth g)
sciDepth (Ident f g) = 1 + max (sciDepth f) (sciDepth g)

sciLength :: SCIFormula -> Integer
sciLength (Variable _) = 1
sciLength (Not f) = 1 + sciLength f
sciLength (And f g) = 1 + sciLength f + sciLength g
sciLength (Or f g) = 1 + sciLength f + sciLength g
sciLength (Imply f g) = 1 + sciLength f + sciLength g
sciLength (Equiv f g) = 1 + sciLength f + sciLength g
sciLength (Ident f g) = 1 + sciLength f + sciLength g

properSubSCI :: SCIFormula -> [SCIFormula]
sciSub :: SCIFormula -> [SCIFormula]

properSubSCI (Variable _) = []
properSubSCI (Not f) = sciSub f
properSubSCI (And f g) = sciSub f `union` sciSub g
properSubSCI (Or f g) = sciSub f `union` sciSub g
properSubSCI (Imply f g) = sciSub f `union` sciSub g
properSubSCI (Equiv f g) = sciSub f `union` sciSub g
properSubSCI (Ident f g) = sciSub f `union` sciSub g

sciSub f = properSubSCI f ++ [f]

sciSubst :: SCIFormula -> SCIFormula -> SCIFormula -> SCIFormula
sciSubst old new f | old == f = new
sciSubst _ _ v@(Variable _) = v
sciSubst old new (Not f) = Not $ sciSubst old new f
sciSubst old new (And f g) = And (sciSubst old new f) (sciSubst old new g)
sciSubst old new (Or f g) = Or (sciSubst old new f) (sciSubst old new g)
sciSubst old new (Imply f g) = Imply (sciSubst old new f) (sciSubst old new g)
sciSubst old new (Equiv f g) = Equiv (sciSubst old new f) (sciSubst old new g)
sciSubst old new (Ident f g) = Ident (sciSubst old new f) (sciSubst old new g)

sciNII :: SCIFormula -> SCIFormula
sciNII v@(Variable _) = v
sciNII (Not f) = Not $ sciNII f
sciNII (Imply f g) = Imply (sciNII f) (sciNII g)
sciNII (Ident f g) = Ident (sciNII f) (sciNII g)
sciNII (And f g) = Not $ Imply (sciNII f) (Not $ sciNII g)
sciNII (Or f g) = Imply (Not $ sciNII f) (sciNII g)
sciNII (Equiv f g) = sciNII $ And (Imply f g) (Imply g f)

sciLesser :: SCIFormula -> SCIFormula -> Bool
sciLesser f g
    | sciLength f < sciLength g = True
    | sciLength f > sciLength g = False
    | otherwise = f < g

applyOrderedBy :: (t -> t -> u) -> BinRel t -> (t -> t -> u)
applyOrderedBy op rel x y = if rel x y then op x y else op y x

sciShorten :: SCIFormula -> SCIFormula -> SCIFormula -> SCIFormula
sciShorten = applyOrderedBy sciSubst (flip sciLesser)
sciShorten2 f g
    | sciLesser f g = sciSubst g f
    | otherwise = sciSubst f g

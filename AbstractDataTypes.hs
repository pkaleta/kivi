module AbstractDataTypes where


import Common
import ParserTypes
import Data.List
import Data.Map as Map


type Tag = Int
type Arity = Int
type NameConstrMapping = Map Name (Tag, Int)
data AExpr = AConstr Name Tag


primitiveADTs :: [ProgramElement Name]
primitiveADTs = [(DataType "Bool" [("True", 0, 0), ("False", 1, 0)]),
                 (DataType "List" [("Nil", 2, 0), ("Cons", 3, 2)])]


initialTag :: Tag
initialTag = 4


undefinedTag :: Tag
undefinedTag = -1


tag :: PatTypeScPair -> PatTypeScPair
tag (adts, scs) = (adts', scs')
    where
        ((mapping, tag), adts') = mapAccumL tagADT (Map.empty, initialTag) adts
        scs' = [tagSc mapping sc | sc <- scs]


tagADT :: (NameConstrMapping, Tag) -> PatProgramElement -> ((NameConstrMapping, Tag), PatProgramElement)
tagADT (mapping, curTag) (PatDataType dtName cs) =
    ((mapping', curTag'), PatDataType dtName cs')
    where
        ((mapping', curTag'), cs') = mapAccumL collect (mapping, curTag) cs

        collect (mapping, curTag) (name, undefinedTag, arity) =
            ((Map.insert name (curTag, arity) mapping, curTag+1), (name, curTag, arity))


tagSc :: NameConstrMapping -> PatProgramElement -> PatProgramElement
tagSc mapping (PatScDefn name eqs) = PatScDefn name [tagEq mapping eq | eq <- eqs]


tagEq :: NameConstrMapping -> Equation -> Equation
tagEq mapping (patterns, expr) = (patterns', expr')
    where
        patterns' = tagPatterns mapping patterns
        expr' = tagExpr mapping expr


tagPatterns :: NameConstrMapping -> [Pattern] -> [Pattern]
tagPatterns mapping patterns = [tagPattern mapping pattern | pattern <- patterns]


tagPattern :: NameConstrMapping -> Pattern -> Pattern
tagPattern mapping (PConstrName name patterns) =
    PConstr (getPatternTag mapping name) (tagPatterns mapping patterns)
tagPattern mapping pattern = pattern


tagExpr :: NameConstrMapping -> Expr Pattern -> Expr Pattern
tagExpr mapping (EConstrName name) =
    EConstr (getPatternTag mapping name) (getPatternArity mapping name)
tagExpr mapping (EAp e1 e2) = EAp (tagExpr mapping e1) (tagExpr mapping e2)
tagExpr mapping (ELet isRec defns expr) = ELet isRec defns' expr'
    where
        defns' = [(tagPattern mapping pattern, tagExpr mapping rhs) | (pattern, rhs) <- defns]
        expr' = tagExpr mapping expr
tagExpr mapping (ECase expr alts) = ECase expr' alts'
    where
        expr' = tagExpr mapping expr
        alts' = [(tagPattern mapping pattern, tagExpr mapping rhs) | (pattern, rhs) <- alts]
tagExpr mapping (ELam patterns expr) = ELam patterns' expr'
    where
        expr' = tagExpr mapping expr
        patterns' = tagPatterns mapping patterns
tagExpr mapping expr = expr


getPatternTag :: NameConstrMapping -> Name -> Tag
getPatternTag = getPatternConstr fst


getPatternArity :: NameConstrMapping -> Name -> Arity
getPatternArity = getPatternConstr snd


getPatternConstr :: ((Tag, Arity) -> Int) -> NameConstrMapping -> Name -> Int
getPatternConstr f mapping name =
    case Map.lookup name mapping of
        Nothing -> error $ "Could not find constructor: " ++ name
        Just constr -> f constr


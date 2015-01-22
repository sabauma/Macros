{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE PatternGuards   #-}
{-# LANGUAGE ViewPatterns    #-}
module Example where

import Control.Arrow (first)
import Control.Applicative hiding (Const (..))
import Control.Monad.State
import Data.List
import Data.Maybe
import Data.Function
import GHC.Exts

type MarkSet = [String]

type Symbol = String

instance IsList Exp where
  type Item Exp    = Exp
  fromList         = EList
  toList (EList x) = x
  toList _         = error "toList: not list"

data Ident
  = Ident
  { symbolicName :: Symbol
  , bindingName  :: Symbol
  , marksOf      :: MarkSet
  } deriving (Show)

instance Eq Ident where
  i == j = bindingName i == bindingName j && marksOf i == marksOf j

data Const = I Int | B Bool

instance Show Const where
  show (B True) = "#t"
  show (B _   ) = "#f"
  show (I i)    = show i

data Exp
  = EConst Const
  | EList  [Exp]
  | EId Ident
  | EWrapped [(Ident, Symbol)] MarkSet Exp

updateMarks :: MarkSet -> Ident -> Ident
updateMarks ms i = i { marksOf = marksOf i `disjointUnion` ms }

updateBinding :: Symbol -> Ident -> Ident
updateBinding s i = i { bindingName = s }

expose :: Exp -> Exp
expose (EWrapped u m (EWrapped u' m' e')) = expose $ EWrapped u'' m'' e'
  where u'' = u ++ map (first $ updateMarks m) u'
        m'' = m `disjointUnion` m'
expose (EWrapped u m (EList xs))          = EList (map (EWrapped u m) xs)
expose (EWrapped u m (EId i   ))          = case lookup i' u of
                                                 Nothing -> EId i'
                                                 Just s  -> EId $ updateBinding s i'
  where i' = updateMarks m i
expose (EWrapped u m e)                   = expose e
expose x                                  = x

exposeTo :: Int -> Exp -> Exp
exposeTo 0 e = e
exposeTo n e =
  case expose e of
       EList xs -> EList $ map (exposeTo (n - 1)) xs
       e'       -> exposeTo (n - 1) e'

instance Show Exp where
  show (EConst c) = show c
  show (EList xs) = "(" ++ unwords (map show xs) ++ ")"
  show (EId i   ) = symbolicName i
  -- show (EId i   ) = "«" ++ symbolicName i ++ "," ++ bindingName i ++ "," ++ show (marksOf i) ++ "»"

data ParsedExp
  = PSymbolicData Exp
  | PVariable Ident
  | PApplication Exp [Exp]
  | PMacroApplication Ident [Exp]
  | PFunction Ident Exp
  | PPatFunction Ident Exp
  | PSyntaxData Exp
  | PSyntaxBinding Ident Exp Exp
  | PRecSyntaxBinding Ident Exp Exp
  deriving (Show)

data ExpandedExp
  = ExVariable Symbol
  | ExApp ExpandedExp [ExpandedExp]
  | ExSymbolicData Exp
  | ExFunction Symbol ExpandedExp

instance Show ExpandedExp where
  show (ExVariable v)   = v
  show (ExApp e es  )   = "(" ++ show e ++ " " ++ unwords (map show es) ++ ")"
  show (ExFunction s e) = "(λ (" ++ s ++ ") " ++ show e ++ ")"

var :: Symbol -> Ident
var s = Ident s s []

var' :: Symbol -> Exp
var' = EId . var

or2 :: Exp -> Exp
or2 (expose -> EList [x, y]) = [body, x]
  where body = [ var' "lambda"
               , [var' "t"]
               , [var' "if", var' "t", var' "t", y]]

example, example2, example3 :: Exp
example  = [var' "a", var' "b"]
example2 = [var' "or2", var' "a", var' "b"]

example3 = [body, var' "t"]
  where body = [ var' "lambda"
               , [var' "if"]
               , [var' "or2", var' "if", var' "t"] ]

type Env = [(Symbol, VarType)]

data VarType
  = Transformer (Exp -> Exp)
  | Variable
  | PatVariable
  | Special

instance Eq VarType where
  Variable    == Variable    = True
  PatVariable == PatVariable = True
  Special     == Special     = True
  _           == _           = False

rinit' :: Env
rinit' = map (, Special) ["quote", "lambda", "plambda", "let-syntax", "syntax"]

rinit :: Env
rinit = rinit' ++ [("or2", Transformer or2)]

resolve :: Ident -> Symbol
resolve = bindingName

isTrans :: VarType -> Bool
isTrans (Transformer _) = True
isTrans _               = False

parse :: Env -> Exp -> ParsedExp
parse env e =
  case exposeTo 3 e of
       EConst _              -> PSymbolicData e
       EId i
         | lup i == Variable -> PVariable i
       EList (x : xs)
         | not (isSym x)     -> PApplication x xs
       EList (EId i : xs)
         | lup i == Variable -> PApplication (EId i) xs
         | isTrans $ lup i   -> PMacroApplication i xs
       EList [EId i, xs]
         | is i "quote"      -> PSymbolicData xs
       EList [EId b, EList [EId i], xs]
         | is b "lambda"     -> PFunction i xs
         | is b "plambda"    -> PPatFunction i xs
       EList [EId i, EId j]
         | is i "syntax" && lup j /= PatVariable -> PSyntaxData (EId j)
         | is i "syntax" && lup j == PatVariable -> PVariable j
       EList [EId r, EList [EId i, e1], e2]
         | is r "let-syntax" -> PSyntaxBinding i e1 e2
  where
    lup i = fromMaybe Variable $ lookup (resolve i) env
    isSym (EId _) = True
    isSym _       = False
    is i s = resolve i == s && fromJust (lookup s env) == Special

fresh :: State Int Symbol
fresh = do
  st <- get
  put (st + 1)
  return $ "fresh_" ++ show st

strip :: Exp -> Exp
strip (EList xs)       = EList (map strip xs)
strip (EWrapped u m e) = strip e
strip (EId i   )       = var' $ symbolicName i
strip c                = c

mark :: Exp -> [Symbol] -> Exp
mark e m = EWrapped [] m e

setEq :: (Ord a, Eq a) => [a] -> [a] -> Bool
setEq xs ys = sort xs == sort ys

subst :: Exp -> Ident -> Symbol -> Exp
subst e i s = EWrapped [(i, s)] [] e

disjointUnion :: (Eq s) => [s] -> [s] -> [s]
disjointUnion xs ys = (xs \\ ys) `union` (ys \\ xs)

fullExpand :: Exp -> ExpandedExp
fullExpand e = evalState (expand rinit e) 0

expand :: Env -> Exp -> State Int ExpandedExp
expand env e =
  case parse env e of
       PVariable i        -> return $ ExVariable (resolve i)
       PApplication e1 e2 -> ExApp <$> expand env e1 <*> mapM (expand env) e2
       PSymbolicData e    -> return $ ExSymbolicData (strip e)
       PSyntaxData e      -> return $ ExSymbolicData e
       PFunction i e      -> do
         s <- fresh
         let env' = (s, Variable) : env
             e'   = subst e i s
         ExFunction s <$> expand env' e'
       PPatFunction i e   -> do
         s <- fresh
         let env' = (s, PatVariable) : env
             e'   = subst e i s
         ExFunction s <$> expand env' e'
       PMacroApplication i e
         | Transformer t <- lup i -> do
           m <- fresh
           let e' = mark (t (mark (EList e) [m])) [m]
           expand env e'
  where
    lup i = fromMaybe Variable $ lookup (resolve i) env


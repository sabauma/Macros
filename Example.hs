{-# LANGUAGE TupleSections #-}

module Example where

import Debug.Trace
import Control.Applicative hiding (Const (..))
import Control.Monad.State
import Data.List
import Data.Maybe

type MarkSet = [String]

type Symbol = String

data Ident
  = Ident
  { symbolicName :: Symbol
  , bindingName  :: Symbol
  , marksOf      :: MarkSet
  } deriving (Eq, Ord, Show)

data Const = I Int | B Bool

instance Show Const where
  show (B b) = show b
  show (I i) = show i

data Exp
  = EConst Const
  | EList  [Exp]
  | EId Ident

instance Show Exp where
  show (EConst c) = show c
  show (EList xs) = "(" ++ intercalate " " (map show xs) ++ ")"
  show (EId i   ) = symbolicName i

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
  show (ExApp e es  )   = "(" ++ show e ++ " " ++ intercalate " " (map show es) ++ ")"
  show (ExFunction s e) = "(λ (" ++ s ++ ") " ++ show e ++ ")"

var' = EId . var

or2 :: Exp -> Exp
or2 (EList [x, y]) = EList [body, x]
  where body = EList [ var' "lambda"
                     , EList $ [var' "t"]
                     , EList $ [var' "if", var' "t", var' "t", y]]

example  = EList [var' "a", var' "b"]

example2 = EList [body, var' "t"]
  where body = EList [ var' "lambda"
                     , EList [var' "if"]
                     , EList [var' "or2", var' "if", var' "t"] ]

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
resolve i = bindingName i

isTrans :: VarType -> Bool
isTrans (Transformer _) = True
isTrans _               = False

parse :: Env -> Exp -> ParsedExp
parse env e =
  case e of
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
    lup i = maybe Variable id $ lookup (resolve i) env
    isSym (EId _) = True
    isSym _       = False
    is i s = resolve i == s && fromJust (lookup s env) == Special

fresh :: State Int Symbol
fresh = do
  st <- get
  put (st + 1)
  return $ "fresh_" ++ show st

strip :: Exp -> Exp
strip (EList xs) = EList (map strip xs)
strip c          = c

mark :: Exp -> Symbol -> Exp
mark e m = go e
  where
    go (EList xs) = EList $ map go xs
    go (EId   i ) = EId $ i { marksOf = marksOf i `disjointUnion` [m] }
    go c          = c

var :: Symbol -> Ident
var s = Ident s s []

subst :: Exp -> Ident -> Symbol -> Exp
subst e i s = go e
  where
    go (EId j)
      |  sort (marksOf j) == sort (marksOf i)
      && resolve i        == resolve j = EId $ var s
    go (EList xs) = EList $ map go xs
    go c          = c

disjointUnion :: (Eq s) => [s] -> [s] -> [s]
disjointUnion xs ys = (xs \\ ys) `union` (ys \\ xs)

fullExpand :: Exp -> ExpandedExp
fullExpand e = evalState (expand rinit e) 0

expand :: Env -> Exp -> State Int ExpandedExp
expand env e =
  case parse env e of
       PVariable i        -> return $ ExVariable (resolve i)
       PApplication e1 e2 -> ExApp <$> (expand env e1) <*> (mapM (expand env) e2)
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
           let e' = mark (t (mark (EList e) m)) m
           expand env e'
  where
    lup i = maybe Variable id $ lookup (resolve i) env


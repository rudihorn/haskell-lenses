{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             MultiParamTypeClasses, FlexibleInstances, PolyKinds,
             FlexibleContexts, UndecidableInstances, ConstraintKinds,
             ScopedTypeVariables, TypeInType, TypeOperators, StandaloneDeriving,
             TypeApplications, OverloadedStrings #-}

module DynamicPredicate where

import Data.Type.Set
import GHC.TypeLits
import Data.Text.Format
import Data.Text.Lazy.Builder
import Data.Text.Buildable(Buildable)

import Common

import qualified Predicate as P
import qualified QueryPrecedence as QP

data Value where
  Bool :: Bool -> Value
  Int :: Int -> Value
  String :: String -> Value
  deriving (Eq, Ord)

-- data Predicate (r :: Env) where
--  Constant :: Value -> Predicate '[]
--  Var :: (KnownSymbol s, Recoverable t Types.Type) => Proxy '(s,t) -> Predicate '[ '(s, t)]
--  InfixAppl :: Operator -> Predicate r1 -> Predicate r2 -> Predicate ()

type Phrase = P.Phrase String Value
type DPhrase = Phrase

instance Recoverable b Bool => Recoverable ('P.Bool b) Value where
  recover Proxy = Bool (recover (Proxy :: Proxy b))

instance KnownNat i => Recoverable ('P.Int i) Value where
  recover Proxy = Int (fromIntegral $ natVal (Proxy :: Proxy i))

instance KnownSymbol s => Recoverable ('P.String s) Value where
  recover Proxy = String (symbolVal (Proxy :: Proxy s))



-- Phrase

instance Recoverable v Value => Recoverable ('P.Constant v) Phrase where
  recover Proxy = P.Constant (recover (Proxy :: Proxy v))

instance KnownSymbol v => Recoverable ('P.Var v) Phrase where
  recover Proxy = P.Var (symbolVal (Proxy :: Proxy v))

instance (Recoverable p1 Phrase, Recoverable p2 Phrase, Recoverable op P.Operator) => Recoverable ('P.InfixAppl op p1 p2) Phrase where
  recover Proxy = P.InfixAppl (recover @op Proxy) (recover @p1 Proxy) (recover @p2 Proxy)

instance (Recoverable p Phrase, Recoverable op P.UnaryOperator) => Recoverable ('P.UnaryAppl op p) Phrase where
  recover Proxy = P.UnaryAppl (recover @op Proxy) (recover @p Proxy)

instance (Recoverable cond (Maybe Phrase), Recoverable cases [(Phrase, Phrase)], Recoverable pother Phrase)
  => Recoverable ('P.Case cond cases pother) Phrase where
  recover Proxy = P.Case (recover @cond @(Maybe Phrase) Proxy) (recover @cases @[(Phrase, Phrase)] Proxy) (recover @pother @Phrase Proxy)

simplify :: Phrase -> Phrase
simplify (P.InfixAppl (P.LogicalAnd) (P.Constant (Bool True)) p2) = p2
simplify (P.InfixAppl (P.LogicalAnd) (P.Constant (Bool False)) _) = P.Constant (Bool False)
simplify (P.InfixAppl (P.LogicalAnd) p1 (P.Constant (Bool True))) = p1
simplify (P.InfixAppl (P.LogicalAnd) _ (P.Constant (Bool False))) = P.Constant (Bool False)
simplify p = p

conjunction :: [P.Phrase id Value] -> P.Phrase id Value
conjunction (P.Constant (Bool True) : y : xs) = conjunction $ y : xs
conjunction (y : P.Constant (Bool True) : xs) = conjunction $ y : xs
conjunction (x : y : xs) = P.InfixAppl P.LogicalAnd x $ conjunction $ y : xs
conjunction [x] = x
conjunction [] = P.Constant (Bool True)

disjunction :: [P.Phrase id Value] -> P.Phrase id Value
disjunction (P.Constant (Bool False) : y : xs) = disjunction $ y : xs
disjunction (x : P.Constant (Bool False) : xs) = disjunction $ x :xs
disjunction (x : y : xs) = P.InfixAppl P.LogicalOr x $ disjunction $ y : xs
disjunction [x] = x
disjunction [] = P.Constant (Bool True)

not :: P.Phrase id Value -> P.Phrase id Value
not p = P.UnaryAppl P.Negate p

print_value :: Value -> IO Builder
print_value (Bool False) = return $ build "false" ()
print_value (Bool True) = return $ build "true" ()
print_value (Int i) = return $ build "{}" (Only i)
print_value (String s) = return $ build "{}" (Only s)

print_op :: P.Operator -> String
print_op P.Plus = "+"
print_op P.LogicalAnd = "AND"
print_op P.LogicalOr = "OR"
print_op P.Equal = "="
print_op P.LessThan = "<"
print_op P.GreaterThan = ">"

print_unary_op :: P.UnaryOperator -> String
print_unary_op P.Negate = "NOT"
print_unary_op P.UnaryMinus = "-"

print_query_eq :: Phrase -> QP.Op -> QP.Op -> IO Builder
print_query_eq p pr npr | compare npr pr == LT = build "({})" <$> Only <$> print_query p npr
                        | otherwise = print_query p npr

print_query_gr :: Phrase -> QP.Op -> QP.Op -> IO Builder
print_query_gr p pr npr
    | compare npr pr == GT = print_query p npr
    | otherwise = build "({})" <$> Only <$> print_query p npr

build_sep :: (Buildable sep, Buildable a) => sep -> [a] -> Builder
build_sep _ [] = build "" ()
build_sep _ [x] = build "{}" (Only x)
build_sep sep (x : xs) = build "{}{}{}" (x, sep, build_sep sep xs)

build_sep_str :: Buildable a => String -> [a] -> Builder
build_sep_str sep xs = build_sep sep xs

print_query :: Phrase -> QP.Op -> IO Builder
print_query (P.Constant val) _ = print_value val
print_query (P.Var v) _ = return $ build "{}" v where
print_query (P.InfixAppl op a b) pr =
  let npr = QP.of_op op in
  do left <- print_query_eq a pr npr
     right <- print_query_eq b pr npr
     return $ build "{} {} {}" (left, print_op op, right)
print_query (P.UnaryAppl op a) pr =
  let npr = QP.of_unary_op op in
  do arg <- print_query_gr a pr npr
     return $ build "{} {}" (print_unary_op op, arg)
print_query (P.In _ []) _ =
  return $ build "FALSE" ()
print_query (P.In cs vals) _ =
  do vals <- mapM (build_vals) vals
     return $ build "({}) IN ({})" (build_sep_str ", " cs, build_sep_str ", " $ vals) where
  build_vals vs =
    do vals <- mapM print_value vs
       return $ build "({})" $ Only $ build_sep_str ", " $ vals
print_query (P.Case inp cases other) _ =
  do inp <- build_inp inp
     cases <- mapM build_case cases
     other <- print_query other QP.first
     return $ build "CASE {}{} ELSE {} END" (inp, build_sep_str " " $ cases, other) where
  build_inp Nothing = return $ build "" ()
  build_inp (Just x) = build "({}) " <$> Only <$> print_query x QP.first
  build_case (key, val) =
     do cond <- print_query key QP.first
        act <- print_query val QP.first
        return $ build "WHEN {} THEN {}" (cond, act)

print :: Phrase -> IO Builder
print p = print_query p QP.first


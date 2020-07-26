
module Lens.Predicate.Precedence where

import qualified Lens.Predicate.Base as P

data Op = Or | And | Cmp | Not | Add | Sub | Mult | Divide deriving (Eq, Ord)

first :: Op
first = Or

of_op :: P.Operator -> Op
of_op P.LogicalAnd = And
of_op P.LogicalOr = Or
of_op P.Plus = Add
-- of_op P.Minus = Sub
of_op P.Equal = Cmp
of_op P.GreaterThan= Cmp
of_op P.LessThan = Cmp
-- of_op P.Multiply = Mult
-- of_op P.Divide = Divide

of_unary_op :: P.UnaryOperator -> Op
of_unary_op _ = Not

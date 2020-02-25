module Delta where

import Data.Set (Set, (\\), union)
import qualified Data.Set as Set

type Delta a = (Set a, Set a)

fromSet :: Set a -> Delta a
fromSet s = (s, Set.empty)

fromList :: Ord a => [a] -> Delta a
fromList l = (Set.fromList l, Set.empty)

neg :: Delta a -> Delta a
neg (p,n) = (n, p)

positive :: Delta a -> Set a
positive (p,_) = p

negative :: Delta a -> Set a
negative (_,n) = n

merge :: Ord a => Delta a -> Delta a -> Delta a
(p1, n1) `merge` (p2, n2) = (p, n) where
  p = (p1 \\ n2) `union` (p2 \\ n1)
  n = (n1 \\ p2) `union` (n2 \\ p1)

(#+) :: Ord a => Delta a -> Delta a -> Delta a
(#+) = merge

(#-) :: Ord a => Delta a -> Delta a -> Delta a
m #- n = m #+ (neg n)

delta_union :: Ord a => Delta a -> Set a
delta_union (p1, n1) = p1 `union` n1

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}

module Main where

import Control.Arrow ((&&&),(|||))
import Control.Monad
import Control.Concurrent.MVar
import Control.DeepSeq
import Data.Bifunctor
import Numeric.Natural
import System.Random.MWC

main :: IO ()
main = do
  let n = 5000
  ns <- newMVar [1..n]
  rs <- randomListMVar n
  evalSort mingleSort rs

type K = Int

ordK :: K -> K -> Bool
ordK = (<=)
-- ordK = (>=)

data List list = Nil | Cons K list deriving (Show,Eq,Functor)

-- least fixed point of f
newtype Mu f = In_ { in_ :: f (Mu f) }

instance (forall a. Show a => Show (f a)) => Show (Mu f) where
  show (In_ x) = "⌈" ++ show x ++ "⌉"

type Algebra f a = f a -> a

initialAlgebra :: Functor f => Algebra f (Mu f)
initialAlgebra = In_

-- catamorphism
-- consuming data structure
-- the running time of a fold is always linear in the size of input
fold :: (Functor f) => Algebra f a -> Mu f -> a
fold f = f . fmap (fold f) . in_

toList :: Mu List -> [K]
toList = fold $ \case
  Nil       -> []
  Cons x xs -> x : xs

-- greatest fixed point of f
newtype Nu f = Out { out :: f (Nu f) }

type Coalgebra f a = a -> f a

finalCoalgebra :: Functor f => Coalgebra f (Nu f)
finalCoalgebra = out

-- anamorphism
-- producing data structure
-- the running time of an unfold is linear in the size of the output
unfold :: Functor f => Coalgebra f a -> a -> Nu f
unfold f = Out . fmap (unfold f) . f

fromList :: [K] -> Nu List
fromList = unfold $ \case
  []     -> Nil
  (x:xs) -> Cons x xs

downcast :: Functor f => Nu f -> Mu f
downcast = In_ . fmap downcast . out

upcast1, upcast2:: Functor f => Mu f -> Nu f
upcast1 = fold $ unfold $ fmap out
upcast2 = unfold $ fold $ fmap In_

-- consuming, or folding over, an input list
-- in order to produce, or unfold into, an ordered list.
type Sort = Mu List -> Nu List

testSort :: Sort -> [K] -> [K]
testSort sort = toList . downcast . sort . downcast . fromList

randomList :: Int -> IO [K]
randomList n = do
  let range = (0,1000)
  gen <- createSystemRandom
  replicateM n $ uniformR range gen

randomListMVar :: Int -> IO (MVar [K])
randomListMVar n = do
  rs <- randomList n
  newMVar rs

evalSort :: Sort -> MVar [K] -> IO ()
evalSort sort mvar = do
  rs <- readMVar mvar
  deepseq (testSort sort rs) $ return ()

bubbleSort :: Sort
bubbleSort = unfold bubble
  where
    bubble = fold bub

-- bub :: Algebra List (List (Mu List))
bub :: List (List (Mu List)) -> List (Mu List)
bub Nil                              = Nil
bub (Cons a Nil)                     = Cons a $ In_ Nil
bub (Cons a (Cons b ml)) | ordK a b  = Cons a $ In_ $ Cons b ml
                         | otherwise = Cons b $ In_ $ Cons a ml

naiveInsertSort :: Sort
naiveInsertSort = fold naiveInsert
  where
    naiveInsert = unfold naiveIns

-- naiveIns :: Coalgebra List (List (Nu List))
naiveIns :: List (Nu List) -> List (List (Nu List))
naiveIns Nil                                    = Nil
naiveIns (Cons a (Out Nil))                     = Cons a Nil
naiveIns (Cons a (Out (Cons b nl))) | ordK a b  = Cons a (Cons b nl)
                                    | otherwise = Cons b (Cons a nl)

swap :: List (List x) -> List (List x)
swap Nil                             = Nil
swap (Cons a Nil)                    = Cons a Nil
swap (Cons a (Cons b x)) | ordK a b  = Cons a $ Cons b x
                         | otherwise = Cons b $ Cons a x

bubbleSort' :: Sort
bubbleSort' = unfold $ fold $ fmap In_ . swap

naiveInsertSort' :: Sort
naiveInsertSort' = fold $ unfold $ swap . fmap out

-- paramorphism
-- given more information about the intermediate state of the list during the traversal
-- (Mu f, a) の Mu f は再帰のその時点における値全体
para, para' :: Functor f => (f (Mu f, a) -> a) -> Mu f -> a
para  f = f . fmap (id &&& para f) . in_
para' f = snd . fold ((In_ . fmap fst) &&& f)

toList' :: Mu List -> [K]
toList' = para $ \case
  Nil             -> []
  Cons x (ml, xs) -> x : xs

-- apomorphism
-- provide a stopping condition on production,
-- which in turn improves the efficiency of the algorithm
apo, apo' :: Functor f => (a -> f (Either (Nu f) a)) -> a -> Nu f
apo  f = Out . fmap (id ||| apo f) . f
apo' f = unfold ((fmap Left . out) ||| f) . Right -- not efficient

fromList' :: [K] -> Nu List
fromList'= apo $ \case
  []     -> Nil
  (x:xs) -> Cons x $ Right xs

-- run in linear time on a list that is already sorted
insertSort :: Sort
insertSort = fold insert
  where
    insert = apo ins

ins :: List (Nu List) -> List (Either (Nu List) (List (Nu List)))
ins Nil                                    = Nil
ins (Cons a (Out Nil))                     = Cons a $ Left  $ Out Nil
ins (Cons a (Out (Cons b nl))) | ordK a b  = Cons a $ Left  $ Out $ Cons b nl -- 肝
                               | otherwise = Cons b $ Right $ Cons a nl

selectSort :: Sort
selectSort = unfold select
  where
    select = para sel

-- 先頭から2つマッチして順序が不変ならば後続は元々のリスト
--   ((Mu List, List (Mu List))のfst)が使われる
-- 内側で入れ替えが発生していてもそれが最小値でない限り外側で無効化される
-- 結果的に最小値と先頭の入れ替えのみが発生したことになる
-- 選択ソート
sel :: List (Mu List, List (Mu List)) -> List (Mu List)
sel Nil                                = Nil
sel (Cons a (x, Nil))                  = Cons a x
sel (Cons a (x, Cons b y)) | ordK a b  = Cons a x
                           | otherwise = Cons b $ In_ $ Cons a y

swop :: List (x, List x) -> List (Either x (List x))
swop Nil                                = Nil
swop (Cons a (x, Nil))                  = Cons a $ Left x
swop (Cons a (x, Cons b y)) | ordK a b  = Cons a $ Left x
                            | otherwise = Cons b $ Right $ Cons a y

insertSort' :: Sort
insertSort' = fold $ apo $ swop . fmap (id &&& out)

selectSort' :: Sort
selectSort' = unfold $ para $ fmap (id ||| In_) . swop

data Tree tree = Empty | Node tree K tree deriving (Show,Eq,Functor)

-- all the values in the left subtree of a node are less than or equal to the value at the node, and all values in the right subtree are greater
type SearchTree = Tree

-- unfold of a fold approach
pivot :: List (SearchTree (Mu List)) -> SearchTree (Mu List)
pivot Nil                               = Empty
pivot (Cons a Empty)                    = Node (In_ Nil)        a (In_ Nil)
pivot (Cons a (Node l b r)) | ordK a b  = Node (In_ $ Cons a l) b r
                            | otherwise = Node l                b (In_ $ Cons a r)

sprout :: List (x, SearchTree x) -> SearchTree (Either x (List x))
sprout Nil                                  = Empty
sprout (Cons a (x, Empty))                  = Node (Left x)           a (Left x)
sprout (Cons a (x, Node l b r)) | ordK a b  = Node (Right (Cons a l)) b (Left r)
                                | otherwise = Node (Left l)           b (Right (Cons a r))

-- coalgebra dual to pivot
-- efficient insertion into a tree is necessarily an apomorphism;
--   because of the search tree property,
--   the recursion need only go down one of the branches,
--   which is not possible with an unfold
treeIns :: List (Nu SearchTree)
        -> SearchTree (Either (Nu SearchTree) (List (Nu SearchTree)))
treeIns Nil                         = Empty
treeIns (Cons a (Out Empty))        = Node (Left $ Out Empty) a (Left $ Out Empty)
treeIns (Cons a (Out (Node l b r))) | ordK a b  = Node (Right $ Cons a l) b (Left r)
                                    | otherwise = Node (Left l) b (Right $ Cons a r)

grow, grow' :: Mu List -> Nu SearchTree
grow  = unfold $ para $ fmap (id ||| In_) . sprout
grow' = fold $ apo $ sprout . fmap (id &&& out)

-- ternary version of append
-- had we implemented this naively as a plain unfold,
--   the right list would also have to be traversed and thus induce unnecessary copying
glue :: SearchTree (Nu List) -> List (Either (Nu List) (SearchTree (Nu List)))
glue Empty                       = Nil
glue (Node (Out Nil) a r)        = Cons a $ Left r
glue (Node (Out (Cons b l)) a r) = Cons b $ Right $ Node l a r

wither :: SearchTree (x, List x) -> List (Either x (SearchTree x))
wither Empty                         = Nil
wither (Node (l, Nil)      a (r, _)) = Cons a $ Left r
wither (Node (_, Cons b l) a (r, _)) = Cons b $ Right $ Node l a r

-- algebra that is dual to glue
shear :: SearchTree (Nu SearchTree, List (Nu SearchTree)) -> List (Nu SearchTree)
shear Empty                         = Nil
shear (Node (l, Nil) a (r, _))      = Cons a r
shear (Node (_, Cons b l) a (r, _)) = Cons b $ Out $ Node l a r

flatten, flatten' :: Mu SearchTree -> Nu List
flatten  = fold $ apo $ wither . fmap (id &&& out)
flatten' = unfold $ para $ fmap (id ||| In_) . wither

quickSort :: Sort
quickSort = flatten . downcast . grow

treeSort :: Sort
treeSort = flatten' . downcast . grow'

-- e the element of a tree node in a heap is 
-- less than or equal to all the elements of the subtrees
type Heap = Tree

-- always add to the left and then swap left with right
-- (Braun tree)
-- node’s right subtree has, at most, one element less than its left
pile :: List (x, Heap x) -> Heap (Either x (List x))
pile Nil                                  = Empty
pile (Cons a (x, Empty))                  = Node (Left x)           a (Left x)
pile (Cons a (x, Node l b r)) | ordK a b  = Node (Right $ Cons b r) a (Left l)
                              | otherwise = Node (Right $ Cons a r) b (Left l)

heapIns :: List (Nu Heap) -> Heap (Either (Nu Heap) (List (Nu Heap)))
heapIns Nil                         = Empty
heapIns (Cons a (Out Empty))        = Node (Left $ Out Empty) a (Left $ Out Empty)
heapIns (Cons a (Out (Node l b r))) | ordK a b  = Node (Right $ Cons b r) a (Left l)
                                    | otherwise = Node (Right $ Cons a r) b (Left l)

divvy :: List (Heap (Mu List)) -> Heap (Mu List)
divvy Nil                               = Empty
divvy (Cons a Empty)                    = Node (In_ Nil)        a (In_ Nil)
divvy (Cons a (Node l b r)) | ordK a b  = Node (In_ $ Cons b r) a l
                            | otherwise = Node (In_ $ Cons a r) b l

sift :: Heap (x, List x) -> List (Either x (Heap x))
sift Empty                                              = Nil
sift (Node (l, Nil)       a (r, _))                     = Cons a $ Left r
sift (Node (l, _)         a (r, Nil))                   = Cons a $ Left l
sift (Node (l, Cons b l') a (r, Cons c r')) | ordK b c  = Cons a $ Right $ Node l' b r
                                            | otherwise = Cons a $ Right $ Node l  c r'

meld :: Heap (Mu Heap, List (Mu Heap)) -> List (Mu Heap)
meld Empty                                              = Nil
meld (Node (l, Nil)         a (r, _))                   = Cons a r
meld (Node (l, _)           a (r, Nil))                 = Cons a l
meld (Node (l, Cons b l') a (r, Cons c r')) | ordK b c  = Cons a $ In_ $ Node l' b r
                                            | otherwise = Cons a $ In_ $ Node l  c r'

-- apo (blend . fmap (id &&& out)) is a ternary version of merge,
--   just as apo glue was a ternary append
blend :: Heap (Nu List, List (Nu List)) -> List (Either (Nu List) (Heap (Nu List)))
blend = sift

heapSort :: Sort
heapSort = unfold deleteMin . downcast . fold heapInsert
  where
    deleteMin  = para meld
    heapInsert = apo heapIns

mingleSort :: Sort
mingleSort = fold (apo $ blend . fmap (id &&& out)) . downcast . unfold (fold divvy)

data Bush bush = Leaf K | Fork bush bush deriving (Show,Eq,Functor)

data NonEmpty nonEmpty = Single K | Push K nonEmpty deriving (Show,Eq,Functor)

data TernaryTree tt = TEmpty | TNode K tt tt tt deriving (Show,Eq,Functor)

data ABTree a b = ABEmpty | ABNode K a b deriving (Show,Eq,Functor)

data TABTree a b = TABEmpty | TABNode K a a a b deriving (Show,Eq,Functor)

instance Bifunctor ABTree where
  bimap f g ABEmpty        = ABEmpty
  bimap f g (ABNode k a b) = ABNode k (f a) (g b)

instance Bifunctor TABTree where
  bimap f g TABEmpty               = TABEmpty
  bimap f g (TABNode k a1 a2 a3 b) = TABNode k (f a1) (f a2) (f a3) (g b)

fix :: (a -> a) -> a
fix f = f $ fix f

fix2 :: (a -> a) -> (a -> b -> b) -> b
fix2 f g = fix $ g $ fix f

type Mu2 f g = Mu (g (Mu f))
type Nu2 f g = Nu (g (Nu f))

h :: Natural -> Natural
h n | n <= 0    = 1
    | otherwise = 3 * h (pred n) + 1

type MuShellTree' = Mu2 TernaryTree TABTree

te :: Mu TernaryTree
te = In_ TEmpty

tn :: K -> Mu TernaryTree -> Mu TernaryTree -> Mu TernaryTree -> Mu TernaryTree
tn k a b c = In_ $ TNode k a b c

tabe :: Mu (TABTree a)
tabe = In_ TABEmpty

tabn :: K -> a -> a -> a -> Mu (TABTree a) -> Mu (TABTree a)
tabn k a b c d = In_ $ TABNode k a b c d

testST0' = tabn 0 te te te tabe
testST1' = tabn 0 (tn 1 te te te) te te tabe
testST4' = tabn 0 (tn 1 te te te) (tn 2 te te te) (tn 3 te te te) (tabn 4 te te te tabe)
testST5' = tabn 0 (tn 1 (tn 5 te te te) te te)
                  (tn 2 te te te) (tn 3 te te te) (tabn 4 te te te tabe)
testST8' = tabn 0 (tn   1 (tn 5 te te te) te te)
                  (tn   2 (tn 6 te te te) te te) 
                  (tn   3 (tn 7 te te te) te te)
                  (tabn 4 (tn 8 te te te) te te tabe)

type MonoidalAlgebra f m = f m m -> m
type ComonoidalCoalgebra f m = m -> f m m

tt2List :: Algebra TernaryTree [K]
tt2List TEmpty          = []
tt2List (TNode k a b c) = k : (a <> b <> c)

list2TT :: Coalgebra TernaryTree [K]
list2TT [] = TEmpty
list2TT (a:b:c:ls) = TNode a [b] [c] ls

tabt2List :: MonoidalAlgebra TABTree [K]
tabt2List TABEmpty            = []
tabt2List (TABNode k a b c d) = k : (a <> b <> c <> d)

something :: (Functor f, Bifunctor g)
          => Algebra f a -> MonoidalAlgebra g a -> Mu2 f g -> a
something f g = g . bimap (fold f) (something f g) . in_

cosomething :: (Functor f, Bifunctor g)
            => Coalgebra f a -> ComonoidalCoalgebra g a -> a -> Nu2 f g
cosomething f g = Out . bimap (unfold f) (cosomething f g) . g

infixr 0 :~>
type f :~> g = forall a. f a -> g a

class HFunctor hf where
  hfmap :: (g :~> h) -> (hf g :~> hf h)

type HAlgebra hf f = hf f :~> f

newtype HMu hf a = In_H { in_H :: hf (HMu hf) a }

hcata :: HFunctor hf => HAlgebra hf f -> HMu hf :~> f
hcata f = f . hfmap (hcata f) . in_H

type HCoalgebra hf f = f :~> hf f

newtype HNu hf a = OutH { outH :: hf (HNu hf) a }

hana :: HFunctor hf => HCoalgebra hf f -> f :~> HNu hf
hana f = OutH . hfmap (hana f) . f

data TFTree f a = TFEmpty | TFNode K a a a (f a) deriving (Functor)

instance HFunctor TFTree where
  hfmap f TFEmpty            = TFEmpty
  hfmap f (TFNode k a b c d) = TFNode k a b c $ f d

type MuShellTree = HMu TFTree (Mu TernaryTree)

tfe :: HMu TFTree a
tfe = In_H TFEmpty

tfn :: K -> a -> a -> a -> HMu TFTree a -> HMu TFTree a
tfn k a b c d = In_H $ TFNode k a b c d

testMTS0, testMTS1, testMTS4, testMTS5, testMTS8 :: MuShellTree
testMTS0 = tfn 0 te te te tfe
testMTS1 = tfn 0 (tn 1 te te te) te te tfe
testMTS4 = tfn 0 (tn 1 te te te) (tn 2 te te te) (tn 3 te te te) (tfn 4 te te te tfe)
testMTS5 = tfn 0 (tn 1 (tn 5 te te te) te te)
                 (tn 2 te te te) (tn 3 te te te) (tfn 4 te te te tfe)
testMTS8 = tfn 0 (tn  1 (tn 5 te te te) te te)
                 (tn  2 (tn 6 te te te) te te)
                 (tn  3 (tn 7 te te te) te te)
                 (tfn 4 (tn 8 te te te) te te tfe)

nanika :: HAlgebra TFTree TernaryTree
nanika TFEmpty            = TEmpty
nanika (TFNode k a b c d) = TNode k a b c

mkShellTree :: Mu List -> HNu TFTree (Nu TernaryTree)
mkShellTree = para f
  where
  f :: List (Mu List, HNu TFTree (Nu TernaryTree)) -> HNu TFTree (Nu TernaryTree)
  f Nil = OutH TFEmpty
  f (Cons k (x, OutH TFEmpty)) = OutH $ TFNode k (Out TEmpty) (Out TEmpty) (Out TEmpty)
                                                 (OutH TFEmpty)

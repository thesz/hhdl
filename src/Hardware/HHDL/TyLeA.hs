-- |TyLeA.hs
--
-- Type level decimal arithmetic.
--
-- Decimal numbers represented either by standalone digits (Dx)
-- or by lists of standalone digits (D1 :. D2 :. D8), (D2 :. D4).
--
-- Author: Serguey Zefirov, 2011
--
-- I place it into public domain.

{-# LANGUAGE TypeFamilies, TemplateHaskell, TypeOperators, UndecidableInstances #-}

module Hardware.HHDL.TyLeA(
	-- how to convert from types to runtime values.
	  Nat(fromNat)
	-- numbers construction.
	-- numbers are either single digits or digits, separated by ":." operator.
	, D0, D1, D2, D3, D4
	, D5, D6, D7, D8, D9
	, (:*)(..)
	-- functions.
	, Max, Plus
	, Mul, Div2, Log2
	-- shortcuts.
	, tySizePure
	, tySize	-- use it as SomeSizedType $(tySize 1024) (equal to D1 :* D0 :* D2 :* D4)
) where

import Control.Monad
import Language.Haskell.TH

data D0 = D0
data D1 = D1
data D2 = D2
data D3 = D3
data D4 = D4
data D5 = D5
data D6 = D6
data D7 = D7
data D8 = D8
data D9 = D9

infixl 5 :*
data ds :* d = ds :* d deriving Show

-------------------------------------------------------------------------------
-- Maximum.

data Equal = Equal deriving Show
data Less = Less deriving Show
data Greater = Greater deriving Show

class Mat a where mat :: a
instance Mat Equal where mat = Equal
instance Mat Less where mat = Less
instance Mat Greater where mat = Greater

type family Max a b
type instance Max a b = SelectMax (Compare a b Equal) a b

type family SelectMax what a b
type instance SelectMax Equal a b = a
type instance SelectMax Less a b = b
type instance SelectMax Greater a b = a

type family Compare a b prevCond
$(liftM concat $ forM [(a,b) | a <- [0..9], b <- [0..9]] $ \(a,b) -> do
	let compareName = mkName "Compare"
	let digit n = ConT $ mkName $ "D"++show n
	let prevCond = VarT $ mkName "prevCond"
	let less = ConT $ mkName "Less"
	let greater = ConT $ mkName "Greater"
	let da = digit a
	let db = digit b
	let compareDigits = TySynInstD compareName [da, db,prevCond] $ case compare a b of
		EQ -> prevCond
		LT -> less
		GT -> greater
	let va = VarT $ mkName "a"
	let vb = VarT $ mkName "b"
	let vc = VarT $ mkName "c"
	let number h l = AppT (AppT (ConT $ mkName ":*") h) l
	let compareNumberRight = TySynInstD compareName [da, number vb db, prevCond] less
	let compareNumberLeft  = TySynInstD compareName [number va da, db, prevCond] greater
	let compareNumbers = TySynInstD compareName [number va da, number vb db, prevCond] $ case compare a b of
		EQ -> ConT compareName `AppT` va `AppT` vb `AppT` prevCond
		LT -> ConT compareName `AppT` va `AppT` vb `AppT` less
		GT -> ConT compareName `AppT` va `AppT` vb `AppT` greater
	let r = [compareDigits, compareNumberLeft, compareNumberRight, compareNumbers]
--	runIO $ mapM (putStrLn . show . ppr) r
	return r
 )

-------------------------------------------------------------------------------
-- Addition.

type family Sum3 a b c
$(liftM concat $ forM [(a,b,c) | a <- [0..9], b <- [0..9], c <- [0..1]] $ \(a,b,c) -> do
	let sum3Name = mkName "Sum3"
	let sum = a+b+c
	let s = sum `mod` 10
	let propC = sum `div` 10
	let digit n = ConT $ mkName $ "D"++show n
	let number h l = AppT (AppT (ConT $ mkName ":*") h) l
	let ds = digit s
	let digitSumResult
		| propC == 0 = ds
		| otherwise = number (digit propC) (ds)
	let da = digit a
	let db = digit b
	let dc = digit c
	let dPropC = digit propC
	let va = VarT $ mkName "a"
	let vb = VarT $ mkName "b"
	let vc = VarT $ mkName "c"
	let digitSum = TySynInstD sum3Name [da, db, dc] digitSumResult
	let numberSumResult = number (ConT sum3Name `AppT` va `AppT` vb `AppT` dPropC) ds
	let numberSum = TySynInstD sum3Name [number va da, number vb db, dc] numberSumResult
	let add3 a b c = ConT sum3Name `AppT` a `AppT` b `AppT` c
	let partLeftSumResult
		| propC == 0 = number va ds
		| otherwise = number (add3 va (digit 0) (digit 1)) ds
	let partLeft = TySynInstD sum3Name [number va da, db, dc] partLeftSumResult
	let partRightSumResult
		| propC == 0 = number vb ds
		| otherwise = number (add3 (digit 0) vb (digit 1)) ds
	let partRight = TySynInstD sum3Name [da, number vb db, dc] partRightSumResult
	let r = [digitSum, numberSum, partLeft, partRight]
--	runIO $ mapM (putStrLn . show . ppr) r
	return r
 )

type family Plus a b
type instance Plus a b = Sum3 a b D0

-------------------------------------------------------------------------------
-- Multiplication.

type family Mul a b
type instance Mul a b = MulAcc D0 a b

type family Dup a
type instance Dup a = Plus a a

type family MulAcc acc a b
type instance MulAcc acc a D0 = acc
type instance MulAcc acc a D1 = Plus acc a
type instance MulAcc acc a D2 = Plus acc (Dup a)
type instance MulAcc acc a D3 = Plus acc (Plus a (Dup a))
type instance MulAcc acc a D4 = Plus acc (Dup (Dup a))
type instance MulAcc acc a D5 = Plus acc (Plus (Dup (Dup a)) a)
type instance MulAcc acc a D6 = Plus acc (Dup (Plus (Dup a) a))
type instance MulAcc acc a D7 = Plus acc (Plus (Dup (Plus (Dup a) a)) a)
type instance MulAcc acc a D8 = Plus acc (Dup (Dup (Dup a)))
type instance MulAcc acc a D9 = Plus acc (Plus (Dup (Dup (Dup a))) a)
type instance MulAcc acc a (bs :* b) = MulAcc (Mul a bs :* D0) a b


-------------------------------------------------------------------------------
-- Division by 2.

type family Div2 a
type instance Div2 D0 = D0
type instance Div2 D1 = D0
type instance Div2 D2 = D1
type instance Div2 D3 = D1
type instance Div2 D4 = D2
type instance Div2 D5 = D2
type instance Div2 D6 = D3
type instance Div2 D7 = D3
type instance Div2 D8 = D4
type instance Div2 D9 = D4
type instance Div2 (D0 :* a) = Div2 a
type instance Div2 (D1 :* a) = Plus (Div2 a) D5
type instance Div2 (D2 :* a) = D1 :* Div2 a
type instance Div2 (D3 :* a) = D1 :* Plus (Div2 a) D5
type instance Div2 (D4 :* a) = D2 :* Div2 a
type instance Div2 (D5 :* a) = D2 :* Plus (Div2 a) D5
type instance Div2 (D6 :* a) = D3 :* Div2 a
type instance Div2 (D7 :* a) = D3 :* Plus (Div2 a) D5
type instance Div2 (D8 :* a) = D4 :* Div2 a
type instance Div2 (D9 :* a) = D4 :* Plus (Div2 a) D5
type instance Div2 (as :* D0 :* a) = Div2 (as :* D0) :* Div2 a
type instance Div2 (as :* D1 :* a) = Div2 (as :* D0) :* Plus (Div2 a) D5
type instance Div2 (as :* D2 :* a) = Div2 (as :* D2) :* Div2 a
type instance Div2 (as :* D3 :* a) = Div2 (as :* D2) :* Plus (Div2 a) D5
type instance Div2 (as :* D4 :* a) = Div2 (as :* D4) :* Div2 a
type instance Div2 (as :* D5 :* a) = Div2 (as :* D4) :* Plus (Div2 a) D5
type instance Div2 (as :* D6 :* a) = Div2 (as :* D6) :* Div2 a
type instance Div2 (as :* D7 :* a) = Div2 (as :* D6) :* Plus (Div2 a) D5
type instance Div2 (as :* D8 :* a) = Div2 (as :* D8) :* Div2 a
type instance Div2 (as :* D9 :* a) = Div2 (as :* D8) :* Plus (Div2 a) D5

-------------------------------------------------------------------------------
-- Base 2 logarithm.

type family Log2 a
type instance Log2 D0 = D0
type instance Log2 D1 = D0
type instance Log2 D2 = D1
type instance Log2 D3 = D2
type instance Log2 D4 = D2
type instance Log2 D5 = D3
type instance Log2 D6 = D3
type instance Log2 D7 = D3
type instance Log2 D8 = D3
type instance Log2 D9 = D4
type instance Log2 (as :* a) = Inc (Log2 (Div2 (Inc (as :* a))))

type family Inc a
type instance Inc a = Plus a D1

-------------------------------------------------------------------------------
-- Conversion to runtime values.

class Nat a where
	fromNat :: a -> Int
	natMult :: a -> Int
	natMult = const 0

instance Nat D0 where { fromNat = const 0; natMult = const 1}
instance Nat D1 where { fromNat = const 1; natMult = const 1}
instance Nat D2 where { fromNat = const 2; natMult = const 1}
instance Nat D3 where { fromNat = const 3; natMult = const 1}
instance Nat D4 where { fromNat = const 4; natMult = const 1}
instance Nat D5 where { fromNat = const 5; natMult = const 1}
instance Nat D6 where { fromNat = const 6; natMult = const 1}
instance Nat D7 where { fromNat = const 7; natMult = const 1}
instance Nat D8 where { fromNat = const 8; natMult = const 1}
instance Nat D9 where { fromNat = const 9; natMult = const 1}

instance (Nat ds, Nat d) => Nat (ds :* d) where
	fromNat ~(ds :* d) = fromNat d + fromNat ds * 10
	natMult = const 1

tySizePure :: Int -> Type
tySizePure n = f $ show n
	where
		f [c] = digit c
		f (c:cs) = AppT (AppT (ConT $ mkName ":*") $ digit c) $ f cs
		digit c = ConT $ mkName $ ['D',c]

tySize :: Int -> Q Type
tySize = return . tySizePure

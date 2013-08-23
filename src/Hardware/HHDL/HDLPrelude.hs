{-# LANGUAGE RankNTypes, GADTs, TypeFamilies, TypeOperators, TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, NoImplicitPrelude #-}


module Hardware.HHDL.HDLPrelude where

import Prelude
	( putStrLn, ($), (.), IO, (++), String, repeat, zipWith, head
	, fst, snd, length, map, Show(..), reverse, Int, Integer, flip, filter
	, unwords, unlines, replicate, const, undefined, error, Ordering(..)
	, concat, concatMap, tail, iterate, Bool, Char, id)

import qualified Prelude
import Data.Word

-------------------------------------------------------------------------------
-- Replacement for Prelude classes.

infixl 6 +, -
infixl 7 *
class Arith op where
	type ArithResult op
	(+), (-), (*) :: op -> op -> ArithResult op

class IntegerConstant a where
	fromInteger :: Integer -> a

class ToInteger a where
	toInteger :: a -> Integer

convertThroughInteger :: (IntegerConstant res, ToInteger arg) => arg -> res
convertThroughInteger = fromInteger . toInteger

infix 4 ==, /=
class Eq a where
	type EqResult a
	(==), (/=) :: a -> a -> EqResult a

infixr 3 &&
infixr 2 ||
class Boolean b where
	not :: b -> b
	(&&), (||) :: b -> b -> b

infix 4 <, >, <=, >=
class Boolean b => Compare a b where
	(>), (<), (>=), (<=) :: a -> a -> b


-------------------------------------------------------------------------------
-- Required instances.

instance IntegerConstant Int where
	fromInteger = Prelude.fromInteger

instance ToInteger Int where
	toInteger = Prelude.toInteger

instance IntegerConstant Integer where
	fromInteger = Prelude.fromInteger

instance ToInteger Integer where
	toInteger = Prelude.toInteger

instance Boolean Bool where
	not = Prelude.not
	(&&) = (Prelude.&&)
	(||) = (Prelude.||)

instance Arith Int where
	type ArithResult Int = Int
	(+) = (Prelude.+)
	(-) = (Prelude.-)
	(*) = (Prelude.*)

instance Arith Integer where
	type ArithResult Integer = Integer
	(+) = (Prelude.+)
	(-) = (Prelude.-)
	(*) = (Prelude.*)

instance Eq Char where
	type EqResult Char = Bool
	(==) = (Prelude.==)
	(/=) = (Prelude./=)

instance Eq Int where
	type EqResult Int = Bool
	(==) = (Prelude.==)
	(/=) = (Prelude./=)

instance Compare Int Bool where
	(>) = (Prelude.>)
	(<) = (Prelude.<)
	(>=) = (Prelude.>=)
	(<=) = (Prelude.<=)

instance Arith Word8 where
	type ArithResult Word8 = Word8
	(+) = (Prelude.+)
	(-) = (Prelude.-)
	(*) = (Prelude.*)

instance Eq Word8 where
	type EqResult Word8 = Bool
	(==) = (Prelude.==)
	(/=) = (Prelude./=)

instance Eq Integer where
	type EqResult Integer = Bool
	(==) = (Prelude.==)
	(/=) = (Prelude./=)

instance IntegerConstant Word8 where
	fromInteger = Prelude.fromInteger

instance ToInteger Word8 where
	toInteger = Prelude.toInteger

{-# LANGUAGE RankNTypes, GADTs, TypeFamilies, TypeOperators, TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances #-}


module Hardware.HHDL.HDLPrelude where

import Data.Word

-------------------------------------------------------------------------------
-- Replacement for Prelude classes.

infixl 6 .+, .-
infixl 7 .*
class Arith op where
	type ArithResult op
	(.+), (.-), (.*) :: op -> op -> ArithResult op

infix 4 .==, ./=
class Equal a where
	type EqResult a
	(.==), (./=) :: a -> a -> EqResult a

infixr 3 .&&
infixr 2 .||
class Boolean b where
	boolNot :: b -> b
	(.&&), (.||) :: b -> b -> b

infix 4 .<, .>, .<=, .>=
class Boolean b => Compare a b where
	(.>), (.<), (.>=), (.<=) :: a -> a -> b


-------------------------------------------------------------------------------
-- Required instances.

instance Boolean Bool where
	boolNot = not
	(.&&) = (&&)
	(.||) = (||)

instance Arith Int where
	type ArithResult Int = Int
	(.+) = (+)
	(.-) = (-)
	(.*) = (*)

instance Arith Integer where
	type ArithResult Integer = Integer
	(.+) = (+)
	(.-) = (-)
	(.*) = (*)

instance Equal Char where
	type EqResult Char = Bool
	(.==) = (==)
	(./=) = (/=)

instance Equal Int where
	type EqResult Int = Bool
	(.==) = (==)
	(./=) = (/=)

instance Compare Int Bool where
	(.>) = (>)
	(.<) = (<)
	(.>=) = (>=)
	(.<=) = (<=)

instance Arith Word8 where
	type ArithResult Word8 = Word8
	(.+) = (+)
	(.-) = (-)
	(.*) = (*)

instance Equal Word8 where
	type EqResult Word8 = Bool
	(.==) = (==)
	(./=) = (/=)

instance Equal Integer where
	type EqResult Integer = Bool
	(.==) = (==)
	(./=) = (/=)


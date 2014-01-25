-- |ToWires.hs
--
-- A class that converts between Haskell types and bit vectors (Integer)
-- with instance for some handy types.
--
-- Copyright (C) Serguey Zefirov, 2009

{-# LANGUAGE TypeOperators, TemplateHaskell, TypeFamilies, FlexibleContexts, UndecidableInstances #-}

module Hardware.HHDL.ToWires where

import Data.Bits
import Data.Word

import Hardware.HHDL.TyLeA

class Nat (BusSize a) => ToWires a where
	type BusSize a
	wireSizeType :: a -> BusSize a
	wireSizeType _ = undefined
	wireSize :: a -> Int
	wireSize x = fromNat $ wireSizeType x
	wireMul :: a -> Integer
	wireMul x = Data.Bits.shiftL 1 (wireSize x)
	wireSelSize :: a -> Int
	wireSelSize = const 0
	-- Integer should occupy no more than wireSize bits, higher ones should be 0
	toWires :: a -> Integer
	-- fromWires should work with integers that have non-zero bits
	-- above wireSize index.
	fromWires :: Integer -> a
	-- enumeration size.
	-- valuesCount of (Maybe a) returns 1+valuesCount (x::a)
	-- valuesCount of Either a b returns valuesCount (x::a) + valuesCount (yLLb)
	-- valuesCount of (a,b) returns valuesCoutn (x::a) * valuesCount (y::b)
--	valuesCount :: a -> Integer
--	-- valueIndex.
--	-- get a value and return an index inside enumeration.
--	valueIndex :: a -> Integer
	-- enumerate values.
--	enumerate :: [a]

castWires :: (ToWires a, ToWires b, BusSize a ~ BusSize b) => a -> b
castWires from = to
	where
		to = fromWires $ toWires from

infixr 5 :&:	-- just like (:)
data l :&: r = l :&: r
instance (Nat (Plus (BusSize l) (BusSize r)), ToWires l, ToWires r) => ToWires (l :&: r) where
	type BusSize (l :&: r) = Plus (BusSize l) (BusSize r)
	toWires (a :&: b) = Data.Bits.shiftL (toWires a) (wireSize b) .|. toWires b
	fromWires x = a :&: b
		where
			b = fromWires x
			a = fromWires $ Data.Bits.shiftR x (wireSize b)
--	enumerate = [a :&: b | a <- enumerate, b <- enumerate]
--	valuesCount (a :&: b) = valuesCount a * valuesCount b

infixr 4 :|:	-- allows us to write a :&: b :|: c :&: d which equal to (a :&: b) :|: (c :&: d)
data l :|: r = l :|: r
instance (Nat (Max (BusSize l) (BusSize r)), ToWires l, ToWires r) => ToWires (l :|: r) where
	type BusSize (l :|: r) = Max (BusSize l) (BusSize r)
	toWires (a :|: b) = toWires a .|. toWires b
	fromWires x = a :|: b
		where
			b = fromWires x
			a = fromWires x
--	enumerate = error "no enumeration for :|:"
		-- [a :|: b | a <- enumerate, b <- enumerate]
--	valuesCount (a :|: b) = max (valuesCount a) (valuesCount b)

instance ToWires Int where
	type BusSize Int = $(tySize 32)
	toWires n = fromIntegral n .&. 0xffffffff
	fromWires x = fromIntegral x .&. 0xffffffff
--	valuesCount = const (Data.Bits.shiftL (1::Integer) 32)
--	valueIndex = fromIntegral
--	enumerate = [fromIntegral n | n <- [0..0xffffffff]]

instance ToWires Word32 where
	type BusSize Word32 = $(tySize 32)
	toWires n = fromIntegral n .&. 0xffffffff
	fromWires x = fromIntegral x .&. 0xffffffff
--	valuesCount = const (Data.Bits.shiftL (1::Integer) 32)
--	valueIndex = fromIntegral
--	enumerate = [fromIntegral n | n <- [0..0xffffffff]]

instance ToWires Word16 where
	type BusSize Word16 = $(tySize 16)
	toWires n = fromIntegral n .&. 0xffff
	fromWires x = fromIntegral x .&. 0xffff
--	valuesCount = const (Data.Bits.shiftL (1::Integer) 32)
--	valueIndex = fromIntegral
--	enumerate = [fromIntegral n | n <- [0..0xffffffff]]

instance ToWires Word8 where
	type BusSize Word8 = $(tySize 8)
	toWires n = fromIntegral n .&. 0xff
	fromWires x = fromIntegral x .&. 0xff
--	valuesCount = const (Data.Bits.shiftL (1::Integer) 32)
--	valueIndex = fromIntegral
--	enumerate = [fromIntegral n | n <- [0..0xffffffff]]

instance ToWires () where
	type BusSize () = $(tySize 0)
	toWires _ = 0
	fromWires _ = ()
--	valuesCount = const 1
--	valueIndex = fromIntegral
--	enumerate = [()]



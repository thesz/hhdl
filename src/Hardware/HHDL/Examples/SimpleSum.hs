{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts, DoRec #-}
{-# LANGUAGE DeriveDataTypeable, NoImplicitPrelude, TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Hardware.HHDL.Examples.SimpleSum where

import Data.Word

import Hardware.HHDL

-------------------------------------------------------------------------------
-- Polymorphic sum of inputs.

simpleSum :: (Show a, BitRepr a, BitRepr (ArithResult a), Arith (Wire c a)) => Comb (Wire c a :. Wire c a :. Nil) (Wire c (ArithResult a) :. Nil)
simpleSum = mkComb "simpleSum" $ \(a :. b :. Nil) -> do
	t <- assignWire (a+b)
	return $ t :. Nil


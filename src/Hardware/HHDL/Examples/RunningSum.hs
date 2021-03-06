{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts, DoRec #-}
{-# LANGUAGE DeriveDataTypeable, NoImplicitPrelude, TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Hardware.HHDL.Examples.RunningSum where

import Data.Word

import Hardware.HHDL

import Hardware.HHDL.Examples.Clock
import Hardware.HHDL.Examples.SimpleSum

-------------------------------------------------------------------------------
-- Running polymorphic sum, ie, accumulator.
-- Demonstrates registers.

runningSumRec :: (Show a, ClockAllowed c clks, BitRepr a, Arith a) => Clocked clks (Wire c a :. Nil) (Wire c a :. Nil)
runningSumRec = mkClocked "runningSum" $ \(a :. Nil) -> do
	rec
		sum <- register (fromIntegerLit 0) nextSum
		(nextSum :. Nil) <- instantiate simpleSum (a :. sum :. Nil)
	return $ sum :. Nil

runningSumRecVHDLText = writeHDLText VHDL (runningSumRec :: Clocked (Clk :. Nil) (Wire Clk Word8 :. Nil) (Wire Clk Word8 :. Nil))
	(\s -> putStrLn s >> writeFile "runningSum.vhdl" s)

test = runningSumRecVHDLText

-- |Hardware.HHDL.Examples.Clock
-- Clock description for examples.

{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts, DoRec #-}
{-# LANGUAGE DeriveDataTypeable, NoImplicitPrelude, TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}


module Hardware.HHDL.Examples.Clock where

import Hardware.HHDL

data Clk = Clk deriving Typeable
data Reset = Reset deriving Typeable
instance Clock Clk where
	type ClkReset Clk = Reset
	clockValue = Clk
	clockResetPositive _ = False
	clockFrontEdge _ = True

fixClockedClock :: Clocked (Clk :. Nil) ins outs -> Clocked (Clk :. Nil) ins outs
fixClockedClock clocked = clocked
-- Many extensions. I overload many things from Haskell Prelude in the style
-- of Awesome Prelude. Also you may need a Template Haskell transformations
-- on declarations, which derives classes and type families instances, etc, etc.
{-# LANGUAGE TypeFamilies, TypeOperators, FlexibleContexts, RecursiveDo #-}
{-# LANGUAGE DeriveDataTypeable, NoImplicitPrelude, TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Hardware.HHDL.Examples.RunningSumMaybes where

import Data.Word

-- The main module of the library. It exports everything I deemed useful
-- for hardware description - code generation over ADT, netlist operators, some
-- handy functions from Prelude...
-- Also, it contains making of wires for Either and Maybe and matching functions.
import Hardware.HHDL

-- The description of clocking frequency for our example.
import Hardware.HHDL.Examples.Clock

-------------------------------------------------------------------------------
-- How to pattern match an algebraic type.

-- Clocked is a type of entity. It has three arguments: a list of clocking frequencies allowed
-- in netlist, types of inputs and outputs.
runningSumMaybes :: Clock c => Mealy c (Wire c (Maybe Word8) :. Nil) (Wire c Word8 :. Nil)
runningSumMaybes = mkMealyNamed
	-- names of inputs and outputs.
	(Just ("maybeA" :. Nil, "currentSum" :. Nil))
	-- default value for state.
	(0 :. Nil)
	"runningSumMaybes" $ \(sum :. Nil) (mbA :. Nil) -> do
        -- here we pattern match in the <a href=http://hackage.haskell.org/package/first-class-patterns>"First class patterns"</a> style.
        -- the idea is that for each constructor Cons of algebraic type T we automatically
        -- create two functions:
        --   - mkCons which creates a wire (of type Wire c T) from wires of arguments and
        --   - pCons which matches a wire of type Wire c T with patterns of types of Cons
        --     arguments.
        -- pJust and pNothing were generated in Hardware.HHDL.HHDL from the description of
        -- Maybe type.
        -- pvar is a pattern that matches anything and passes that anything as an argument
        -- to processing function.
	a <- match mbA [
                -- if we have Just x, return it!
		  pJust pvar --> \(x :. Nil) -> return x
                -- default with 0, if Nothing.
		, pNothing --> \Nil -> return (constant 0)
		]
        -- compute the sum.
	nextSum <- assignWire (sum .+ a)
        -- return currently locked sum.
	return (nextSum :. Nil, sum :. Nil)

-- How to obtain VHDL text - we fix polymorphic parameters in Clocked, generate text (with any
-- entities we have to use) and pass it to display and write function.
runningSumMaybesVHDLText = writeHDLText VHDL (runningSumMaybes :: Mealy Clk (Wire Clk (Maybe Word8) :. Nil) (Wire Clk Word8 :. Nil))
	(\s -> putStrLn s >> writeFile "runningSumMaybes.vhdl" s)

-- a shortcut.
test = runningSumMaybesVHDLText

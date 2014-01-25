{-# LANGUAGE RankNTypes, GADTs, TypeFamilies, TypeOperators, TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances #-}
{-# LANGUAGE DoRec #-}
-- {-# LANGUAGE NoMonomorphismRestriction #-}

module Hardware.HHDL.HHDL(
	-- convenience exports.
	  module Data.Typeable
	, module Hardware.HHDL.HDLPrelude
	, module Prelude
	, module Control.Monad.Fix
	, module Hardware.HHDL.BitRepr
	, module Hardware.HHDL.TyLeA
	, module Hardware.HHDL.TH
	-- This module exports.
	, (:.)(..), Nil(Nil)	-- our own HList.
	, Wire			-- abstract type.
	, HDL(..)		-- what kind of HDL you want to generate.
	, WireOp(..)		-- the means to extend operations.
	, toBits		-- a method to get bit vector from a type.
	, WList
	, WiresList		-- a class that defines list of wires.
	, NLM
	, Clock(..), ClockAllowed
	, Clocked		-- the type constructor of clocked circuits.
	, mkClockedNamed	-- for top-level exported entities.
	, mkClocked
	, Comb			-- the type constrictor of combinational (stateless) circuits.
	, mkComb
	, Mealy			-- simple MEaly state machine.
	, mkMealyNamed		-- for top-level exported entities.
	, mkMealy
	, assignWire		-- w <- assignWire (expression)
	, assignFlattened
	, register		-- latched <- register defaultValue wireToLatch
	, instantiate		-- instantiate entity, literally. outputs <- instantiate entity inputs
	, constant		-- convert Haskell value (BitRepr one) into wire.
	, writeHDLText		-- write HDL text of an entity.
	, match			-- match expression against list of patterns.
	, (-->)			-- combine pattern and netlists.
	, pvar, pcst, pwild	-- variable match, constant match, wildcard match.
	, pJust, mkJust, pNothing, mkNothing	-- generated for Maybe.
	, pLeft, mkLeft, pRight, mkRight	-- generated for Maybe.
	) where

import Control.Monad.State
import Control.Monad
import Control.Monad.Fix
import qualified Data.Bits as B
import qualified Data.Bits
import Data.IORef
import Data.List (nub, intersperse, intercalate)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable
import Data.Word
import qualified Language.Haskell.TH as TH
import System.IO.Unsafe
import qualified Text.Printf

import Hardware.HHDL.BitRepr
import Hardware.HHDL.HDLPrelude
import Hardware.HHDL.TH
import Hardware.HHDL.TyLeA

-------------------------------------------------------------------------------
-- Our own HList.

infixr 5 :.

data a :. as = a :. as deriving Show
data Nil = Nil

-------------------------------------------------------------------------------
-- Unique index generation.

{-# NOINLINE uniqueCounterRef #-}
uniqueCounterRef :: IORef Int
uniqueCounterRef = unsafePerformIO (newIORef 0)

createUniqueIndex :: (String -> Int -> a) -> String -> a
createUniqueIndex mk n = unsafePerformIO $ do
	atomicModifyIORef uniqueCounterRef (\x -> (x+1,()))
	i <- readIORef uniqueCounterRef
	return $ mk n i

-------------------------------------------------------------------------------
-- What is wire.

data WireE =
		-- wire identifier. Is wire should be generated without index, does wire have name and what it is and unique index.
		WIdent	Bool (Maybe String) Int
	|	WConst	Integer
	|	WConcat	SizedWireE SizedWireE
	-- for most operations size of result is equal to sizes of arguments.
	-- for multiplication
	|	WBin	BinOp	SizedWireE	SizedWireE
	|	WUn	UnOp	SizedWireE
	|	WSlice	SizedWireE	Int
	deriving (Eq, Ord, Show)

data BinOp =
		Plus
	|	Minus
	|	Mul
	|	ShiftRL
	|	ShiftRA
	|	ShiftL
	|	And
	|	Or
	|	Xor
	deriving (Eq, Ord, Show)

data UnOp =
		Negate
	|	Complement
	|	Extend	ExtOp
	deriving (Eq, Ord, Show)

data ExtOp =
	ExtZero | ExtSign | ExtOne
	deriving (Eq, Ord, Show)

type SizedWireE = (Int, WireE)

data Wire clk ty where
	Wire :: SizedWireE -> Wire clk ty

instance Show (Wire c ty) where
	show (Wire sw) = show sw

data HDL = VHDL | Verilog
	deriving (Prelude.Eq, Prelude.Ord, Show)

exprFlatten :: SizedWireE -> NLM clocks SizedWireE
exprFlatten sizedExpr = return sizedExpr

{- DEL ME!!!
class BitRepr (WireOpType op) => WireOp op where
	type WireOpType op
	-- |Transformation to HDL.
	opToHDL :: BitRepr (WireOpType op) => HDL -> op -> String

	-- |Flattening transformation.
	opFlatten :: op -> NLM clocks op

	opType :: op -> WireOpType op
	opType op = undefined

	opTypeSize :: op -> Int
	opTypeSize op = bitVectorSize (opType op)
-}

opToHDL :: BitRepr ty => HDL -> Wire c ty -> String
opToHDL hdl (Wire expr) = exprHDL expr
	where
		exprHDL (size, e) = case e of
			WIdent	special name ix -> nameString
				where
					nameString = case name of
						Nothing -> "generated_hhdl_name_"++show ix
						Just n
							| special -> n
							| otherwise -> n ++"_"++ix

			WConst	i -> case hdl of
				Verilog -> error "wconst!"
			WConcat	exprs -> case hdl of
				Verilog -> concat ["{", concat $ intercalate ", " $ map exprHDL exprs, "}"]
			WBin	op a b -> unwords [exprHDL a, hdlOp, exprHDL b]
				where
					hdlOp = case (hdl, op) of
						_ -> error "hdlOp!"
			WUn	op e -> case (hdl, op) of
				(Verilog, Complement) -> "~"++exprHDL e
				(VHDL, Complement) -> unwords ["not", exprHDL e]
				(_, Negate) -> "-"++exprHDL e
			WSlice	e@(len,_) from -> case hdl of
				Verilog
					| len < 2 -> concat [exprHDL e, "[",show from,"]"]
					| otherwise -> concat [exprHDL e, "[",show (from+len-1),":", show from,"]"]
				VHDL
					| len < 2 -> concat [exprHDL e, "(",show from,")"]
					| otherwise -> concat [exprHDL e, "[",show (from+len-1)," downto ", show from,"]"]


data SimpleOps c ty where
	OpConst :: (BitRepr ty, Show ty) => ty -> SimpleOps c ty
	OpSimpleBin :: (BitRepr res, BitRepr arg) =>
		Wire c arg -> [(HDL,String)] -> Wire c arg -> SimpleOps c res
	OpSimpleUn :: (BitRepr res, BitRepr arg) => [(HDL,String)] -> Wire c arg -> SimpleOps c res

toBits :: BitRepr ty => ty -> String
toBits x
	| n > 1 = show bits
	| otherwise = show $ head bits
	where
		i = toBitVector x
		n = bitVectorSize x
		bits = reverse $ concatMap show $ take n $ map snd $ tail $
			iterate ((`Prelude.divMod` 2) . fst) (i,0)

constant :: BitRepr ty => ty -> Wire c ty
constant x = Wire (bitVectorSize x, WConst $ toBitVector x)

simpleBinAnyHDL a op b = (fst a, WBin op a b)

instance (BitRepr ty, Arith ty, BitRepr (ArithResult ty)) => Arith (Wire c ty) where
	type ArithResult (Wire c ty) = Wire c (ArithResult ty)
	Wire a .+ Wire b = Wire $ simpleBinAnyHDL a Plus b
	Wire a .- Wire b = Wire $ simpleBinAnyHDL a Minus b
	Wire a .* Wire b = Wire $ simpleBinAnyHDL a Mul b

instance Boolean (Wire c Bool) where
	boolNot (Wire x) = Wire $ WUn Complement x
	Wire a .&& Wire b = Wire $ simpleBinAnyHDL a And b
	Wire a .|| Wire b = Wire $ simpleBinAnyHDL a Or b


type family WList c ts
type instance WList c Nil = Nil
type instance WList c (t :. ts)  = Wire c t :. WList c ts

class WiresList a where
	type WireNamesList a
	mkWireList :: Maybe (WireNamesList a) -> NLM clocks a
	copyWireList :: Maybe (WireNamesList a) -> a -> NLM clocks a
instance WiresList Nil where
	type WireNamesList Nil = Nil
	mkWireList _ = return Nil
	copyWireList _ _ = return Nil
instance (BitRepr a, WiresList as) => WiresList (Wire c a :. as) where
	type WireNamesList (Wire c a :. as) = String :. WireNamesList as
	mkWireList names = do
		let (n,ns) = case names of
			Just (n :. ns) -> (Just n, Just ns)
			Nothing -> (Nothing, Nothing)
		a <- mkWire n
		as <- mkWireList ns
		return (a :. as)
	copyWireList names ~(w :. ws) = do
		let (n,ns) = case names of
			Just (n :. ns) -> (Just n, Just ns)
			Nothing -> (Nothing, Nothing)
		w <- assignWithForcedCopy n w
		ws <- copyWireList ns ws
		return (w :. ws)

class RegisterWiresList a clocks where
	type RegisterDefault a
	registerWiresList :: RegisterDefault a -> a -> NLM clocks a
instance RegisterWiresList Nil clocks where
	type RegisterDefault Nil = Nil
	registerWiresList _ _ = return Nil
instance (Show a, BitRepr a, ClockAllowed c clocks, RegisterWiresList as clocks) => RegisterWiresList (Wire c a :. as) clocks where
	type RegisterDefault (Wire c a :. as) = a :. RegisterDefault as
	registerWiresList ~(a :. as) ~(w :. ws) = do
		w' <- register a w
		ws' <- registerWiresList as ws
		return $ w' :. ws'

data SignalKind = BitSignal | BusSignal Int deriving Show

class HDLSignal a where
	signalNameKind :: a -> (String, SignalKind)

signalName :: HDLSignal a => a -> String
signalName = fst . signalNameKind

signalKind :: HDLSignal a => a -> SignalKind
signalKind = snd . signalNameKind

wireBusSize :: BitRepr a => Wire c a -> Int
wireBusSize wire = bitVectorSize (wireType wire)
	where
		wireType :: BitRepr a => Wire c a -> a
		wireType _ = undefined

wireOpBusSize :: (BitRepr ty) => Wire c ty -> Int
wireOpBusSize op = bitVectorSize (projectType op)
	where
		projectType :: Wire c ty -> ty
		projectType = undefined

instance BitRepr a => HDLSignal (Wire c a) where
	signalNameKind wire = (name,kind)
		where
			kind = if width == 1 then BitSignal else BusSignal width
			width = wireBusSize wire
			name = case wire of
				Wire Nothing i -> "generated_temporary_name_"++show i
				Wire (Just n) i -> concat [n,"_",show i]


class HDLSignals a where
	signalsWires :: a -> [(String,SignalKind)]
instance HDLSignals Nil where
	signalsWires Nil = []
instance (HDLSignal a, HDLSignals as) => HDLSignals (a :. as) where
	signalsWires (w :. ws) = signalNameKind w : signalsWires ws

class HDLOp op where
	opArgs :: WiresList as => op clk ty -> as
	opSize :: BitRepr ty => op clk ty -> Int

class (Typeable c, Typeable (ClkReset c)) => Clock c where
	type ClkReset c
	-- |Provide construction of clock value to carry around.
	clockValue :: c
	-- |Reset sensitivity.
	clockResetPositive :: c -> Bool
	-- |Front sensitivity.
	clockFrontEdge :: c -> Bool

changeDotsToUnderscores :: Typeable t => t -> String
changeDotsToUnderscores = map (\c -> if c == '.' then '_' else c) . show . typeOf

clockName :: Clock c => c -> String
clockName c = changeDotsToUnderscores c

clockResetName :: Clock c => c -> String
clockResetName c = changeDotsToUnderscores $ clockReset c
	where
		clockReset :: Clock c => c -> ClkReset c
		clockReset _ = undefined

class ClockList l where
	clockListValue :: l
	clockListClocks :: l -> [String]
	clockListResets :: l -> [String]
instance ClockList Nil where
	clockListValue = Nil
	clockListClocks = const []
	clockListResets = const []
instance (ClockList t, Clock h) => ClockList (h :. t) where
	clockListValue = clockValue :. clockListValue
	clockListClocks (c :. cs) = nub $ clockName c : clockListClocks cs
	clockListResets (c :. cs) = nub $ clockResetName c : clockListResets cs

class (Clock c, ClockList cs) => ClockAllowed c cs
instance (Clock c, Clock c1, ClockAllowed c cs) => ClockAllowed c (c1 :. cs)
instance (Clock c, ClockList (c :. cs)) => ClockAllowed c (c :. cs)

class (ClockList clockSubset, ClockList clockSet) => ClockSubset clockSubset clockSet
instance ClockList clockSet => ClockSubset Nil clockSet
instance (Clock c, ClockAllowed c clockSet, ClockSubset css clockSet, ClockList clockSet) => ClockSubset (c :. css) clockSet

wireClock :: Clock c => Wire c a -> c
wireClock w = clockValue

-- |Basic netlist operations.
data NetlistOp domain where
 	-- Latching wires. First comes default
	Register :: (ClockAllowed c clocks, BitRepr a, Show a) =>
		a -> Wire c a -> Wire c a -> NetlistOp clocks


	-- Assign dest what
	-- dest <= what;
	Assign :: BitRepr ty => Wire c ty -> Wire c ty -> NetlistOp clocks

	-- Instance ent
	-- entity ent port map (...);
	Instance :: (Instantiable entity, HDLSignals ins, HDLSignals outs
		, EntityIns entity ~ ins, EntityOuts entity ~ outs) => 
		entity -> ins -> outs -> NetlistOp clocks

-- |Netlist type.
data Netlist clocks = Netlist { netlistOperations :: [NetlistOp clocks] }

-- |State of netlist construction monad.
data NLMS domain = NLMS {
	  nlmsNetlist	:: Netlist domain
	, nlmsCounter	:: Int
	}
emptyNLMS :: NLMS clocked
emptyNLMS = NLMS (Netlist []) 0

type NLM clocked a = State (NLMS clocked) a

mkWire :: BitRepr a => Maybe String -> NLM clocked (Wire c a)
mkWire name = do
	n <- liftM nlmsCounter get
	modify $ \nlms -> nlms { nlmsCounter = n+1 }
	return $ Wire name n

tempWire :: BitRepr a => NLM clocked (Wire c a)
tempWire = mkWire Nothing

class (ClockList (EntityClocks entity)
	, HDLSignals (EntityIns entity)
	, HDLSignals (EntityOuts entity)
	, GenHDL entity) => Instantiable entity where
	type EntityClocks entity
	type EntityIns entity
	type EntityOuts entity
	getInputsOuputsClocks :: entity
		-> (EntityIns entity, EntityOuts entity, EntityClocks entity)

data Comb ins outs where
	Comb :: (HDLSignals ins, HDLSignals outs) => 
		String -> Int -> ins -> outs -> Netlist Nil -> Comb ins outs

instance (HDLSignals ins
	, HDLSignals outs
	, GenHDL (Comb ins outs)) => Instantiable (Comb ins outs) where
	type EntityClocks (Comb ins outs) = Nil
	type EntityIns (Comb ins outs) = ins
	type EntityOuts (Comb ins outs) = outs
	getInputsOuputsClocks (Comb _ _ ins outs _) = (ins, outs, Nil)

runNetlistCreation :: (WiresList ins, WiresList outs, HDLSignals ins, HDLSignals outs)
	=> Maybe (WireNamesList ins, WireNamesList outs)
	-> (ins -> outs -> Netlist domain -> a) -> (ins -> NLM domain outs) -> a
runNetlistCreation names q f = mk $ do
	ins <- mkWireList (fmap fst names)
	outs <- f ins
	outs <- copyWireList (fmap snd names) outs
	return (ins,outs)
	where
		mk act = (\((ins,outs),nlms) -> q ins outs (nlmsNetlist nlms)) $
			runState act emptyNLMS

-- |Create a combinational circut with named inputs and outputs from netlist description.
mkCombNamed :: (HDLSignals ins, HDLSignals outs, WiresList ins, WiresList outs)
	=> Maybe (WireNamesList ins, WireNamesList outs) -> String -> (ins -> NLM Nil outs) -> Comb ins outs
mkCombNamed names n f = runNetlistCreation names (createUniqueIndex Comb n) f

-- |Create a combinational circut anonymous inputs and outputs from netlist description.
mkComb :: (HDLSignals ins, HDLSignals outs, WiresList ins, WiresList outs)
	=> String -> (ins -> NLM Nil outs) -> Comb ins outs
mkComb n f = mkCombNamed Nothing n f

-- |Create a combinational circuit from pure function.
-- You can easily shoot your foot here by creating cyclic expressions like
-- 'f a = y where { x = a+y; y = x-a}.
-- Use with care.
mkCombPure :: (HDLSignals ins, HDLSignals outs, WiresList ins, WiresList outs) => String -> (ins -> outs) -> Comb ins outs
mkCombPure n f = mkComb n (\ins -> return (f ins))

data Clocked clks ins outs where
	Clocked :: (HDLSignals ins, HDLSignals outs, ClockList clks) =>
		clks -> String -> Int -> ins -> outs -> Netlist clks -> Clocked clks ins outs

instance (ClockList clks
	, HDLSignals ins
	, HDLSignals outs
	, GenHDL (Clocked clks ins outs)) => Instantiable (Clocked clks ins outs) where
	type EntityClocks (Clocked clks ins outs) = clks
	type EntityIns (Clocked clks ins outs) = ins
	type EntityOuts (Clocked clks ins outs) = outs
	getInputsOuputsClocks (Clocked clks _ _ ins outs _) = (ins, outs, clks)

mkClockedNamed :: (ClockList clks, WiresList ins, WiresList outs, HDLSignals ins, HDLSignals outs)
	=> Maybe (WireNamesList ins, WireNamesList outs) -> String
	-> (ins -> NLM clks outs) -> Clocked clks ins outs
mkClockedNamed names n f = runNetlistCreation names (createUniqueIndex (Clocked clockListValue) n) f

mkClocked :: (ClockList clks, WiresList ins, WiresList outs, HDLSignals ins, HDLSignals outs)
	=> String -> (ins -> NLM clks outs) -> Clocked clks ins outs
mkClocked n f = mkClockedNamed Nothing n f

data Mealy clk ins outs where
	Mealy :: (HDLSignals ins, HDLSignals outs, Clock clk) =>
		clk -> String -> Int -> ins -> outs -> Netlist (clk :. Nil) -> Mealy clk ins outs

instance (Clock clk
	, HDLSignals ins
	, HDLSignals outs
	, GenHDL (Mealy clk ins outs)) => Instantiable (Mealy clk ins outs) where
	type EntityClocks (Mealy clk ins outs) = clk :. Nil
	type EntityIns (Mealy clk ins outs) = ins
	type EntityOuts (Mealy clk ins outs) = outs
	getInputsOuputsClocks (Mealy clk _ _ ins outs _) = (ins, outs, clk :. Nil)

mkMealyNamed :: (Clock clk, WiresList state, HDLSignals state, WiresList ins, WiresList outs, HDLSignals ins, HDLSignals outs, RegisterWiresList state (clk :. Nil))
	=> Maybe (WireNamesList ins, WireNamesList outs)
	-> RegisterDefault state -> String -> (state -> ins -> NLM (clk :. Nil) (state, outs))
	-> Mealy clk ins outs
mkMealyNamed names defs n f = runNetlistCreation names (createUniqueIndex (Mealy clockValue) n) action
	where
		action ins = do
			rec
				state <- registerWiresList defs nextState
				~(nextState, outs) <- f state ins
			return outs
mkMealy:: (Clock clk, WiresList state, HDLSignals state, WiresList ins, WiresList outs, HDLSignals ins, HDLSignals outs, RegisterWiresList state (clk :. Nil))
	=> RegisterDefault state -> String -> (state -> ins -> NLM (clk :. Nil) (state, outs))
	-> Mealy clk ins outs
mkMealy defs n f = mkMealyNamed Nothing defs n f

-------------------------------------------------------------------------------
-- BitRepr instances.

instance BitRepr Int where
	type BitVectorSize Int = $(tySize 32)
	toBitVector x = fromIntegral x
	fromBitVector x = fromIntegral x
	bitVectorSize x = 32

instance BitRepr Word8 where
	type BitVectorSize Word8 = $(tySize 8)
	toBitVector x = fromIntegral x
	fromBitVector x = fromIntegral x
	bitVectorSize x = 8

instance BitRepr Nil where
	type BitVectorSize Nil = $(tySize 0)
	toBitVector x = 0
	fromBitVector x = Nil
	bitVectorSize x = 0

instance (BitRepr a, BitRepr as
	, Nat (Plus (BitVectorSize a) (BitVectorSize as)))
	=> BitRepr (a :. as) where
	type BitVectorSize (a :. as) = Plus (BitVectorSize a) (BitVectorSize as)
	toBitVector (a :. as) = B.shiftL (toBitVector a) (bitVectorSize as)
		B..|. toBitVector as
	fromBitVector x = a :. as
		where
			mask :: BitRepr a => a -> Integer
			mask x = B.shiftL (1 :: Integer) (bitVectorSize x) - 1
			ys = x B..&. mask as
			y = B.shiftR x (bitVectorSize as) B..&. mask a
			a = fromBitVector y
			as = fromBitVector ys
	bitVectorSize (a :. as) = bitVectorSize a + bitVectorSize as

instance BitRepr () where
	type BitVectorSize () = $(tySize 0)
	toBitVector = const 0
	fromBitVector = const ()

-------------------------------------------------------------------------------
-- Dumping HDL.

data HDLGenState = HDLGenState {
	-- errors, if we encounter any.
	  hdlgErrors		:: [String]
	-- Mapping from entities to their "real" names.
	, hdlgGeneratedEntities	:: Map.Map (String, Int) String
	-- how deep we recurred?
	, hdlgRecursionLevel	:: Int
	-- lines of generated text. In reverse order.
	, hdlgTextLines		:: [String]
	-- nesting level.
	, hdlgNestLevel		:: Int
	-- what kind of language we generate.
	, hdlgLanguage		:: HDL
	-- set of defined names.
	, hdlgDefinedNames	:: Set.Set String
	}
	deriving (Prelude.Eq, Prelude.Ord, Show)
type HDLGen a = State HDLGenState a

emptyHDLGenState hdl = HDLGenState {
	  hdlgErrors		= []
	, hdlgGeneratedEntities	= Map.empty
	, hdlgRecursionLevel	= 0
	, hdlgTextLines		= []
	, hdlgNestLevel		= 0
	, hdlgLanguage		= hdl
	, hdlgDefinedNames	= Set.empty
	}

runHDLGeneration :: GenHDL a => HDL -> a -> (String, [String])
runHDLGeneration hdl entity = (text, errors)
	where
		errors = hdlgErrors state
		text = unlines $ reverse $ hdlgTextLines state
		(_,state) = runState (generateHDL entity) (emptyHDLGenState hdl)

generateLine :: String -> HDLGen ()
generateLine s = modify $ \hdlg -> hdlg {
		  hdlgTextLines = (replicate (hdlgNestLevel hdlg) ' '++s) : hdlgTextLines hdlg
		}

generateEmptyLines :: Int -> HDLGen ()
generateEmptyLines n = modify $ \hdlg -> hdlg {
		  hdlgTextLines = (replicate n "") ++ hdlgTextLines hdlg
		}

generateNest :: HDLGen a -> HDLGen a
generateNest act = do
	nest <- liftM hdlgNestLevel get
	modify $ \hdlg -> hdlg { hdlgNestLevel = nest + 4 }
	x <- act
	modify $ \hdlg -> hdlg { hdlgNestLevel = nest }
	return x

generateDashes :: HDLGen ()
generateDashes = modify $ \hdlg -> hdlg {
		  hdlgTextLines = dashesLine (hdlgLanguage hdlg) (hdlgNestLevel hdlg)
			 : hdlgTextLines hdlg
		}
	where
		dashesLine hdl n = concat [replicate n ' ',prefix hdl, replicate (79-n-2) '-']
		prefix hdl = case hdl of
			VHDL -> "--"
			Verilog -> "//"

generateError :: String -> HDLGen ()
generateError err = modify $ \hdlg -> hdlg { hdlgErrors = err : hdlgErrors hdlg}

generateComment :: String -> HDLGen ()
generateComment c = do
	hdl <- liftM hdlgLanguage get
	let commentPrefix = case hdl of
		VHDL -> "--"
		Verilog -> "//"
	generateLine $ unwords [commentPrefix,c]

generateDashesComment :: String -> HDLGen ()
generateDashesComment c = do
	generateDashes
	generateComment c

generateDefineName :: String -> HDLGen ()
generateDefineName name = modify $ \hdlg -> hdlg {
	  hdlgDefinedNames = Set.insert name $ hdlgDefinedNames hdlg
	}

generateFilterDefined :: [a] -> (a -> String) -> HDLGen [a]
generateFilterDefined things nameProjection = do
	defined <- liftM hdlgDefinedNames get
	let things' = filter (not . flip Set.member defined . nameProjection) things
	mapM (generateDefineName . nameProjection) things'
	return things'

class GenHDL a where
	generateHDL :: a -> HDLGen ()

names :: HDLSignals s => s -> [String]
names s = map fst $ signalsWires s
entityPortsList dir signals = (
			 map fst wiresKinds
			,map (\(name,kind) -> (name,unwords [name,":",dir,vhdlType kind])) wiresKinds)
			where
				wiresKinds = signalsWires signals
				vhdlType BitSignal = "bit"
				vhdlType (BusSignal width) =
					"unsigned ("++show (width-1)++" downto 0)"
generateHDLForEntity :: (HDLSignals ins, HDLSignals outs, ClockList clocks) =>
	String -> Int -> ins -> outs -> clocks -> Netlist domain -> HDLGen ()
generateHDLForEntity name index ins outs clocks netlist = do
	hdl <- liftM hdlgLanguage get
	n <- liftM (Map.lookup key . hdlgGeneratedEntities) get
	case n of
		Nothing -> do
			ourName <- registerOurEntity
			mapM_ subEntity $ netlistOperations netlist
			case hdl of
				VHDL -> vhdlText ourName
				Verilog -> verilogText ourName
		Just _ -> return ()
	where
		key = (name, index)
		registerOurEntity = do
			names <- liftM (Set.fromList . Map.elems . hdlgGeneratedEntities) get
			let newNames = map (name++) $
				map ('_':) $ map show [(1::Int)..]
			let ourName = head $ filter (not . (`Set.member` names)) newNames
			modify $ \hdlgs -> hdlgs { hdlgGeneratedEntities = Map.insert key ourName $ hdlgGeneratedEntities hdlgs }
			return ourName
		subEntity :: NetlistOp domain -> HDLGen ()
		subEntity (Instance entity ins outs) = do
			generateHDL entity
		subEntity _ = return ()
		generateEntityClocksResets clks = map addTypeDir $ clocks ++ resets
			where
				addTypeDir name = name ++ ": in std_logic"
				clocks = clockListClocks clks
				resets = clockListResets clks
		generateVHDLDeclarations ops' = do
			ops <- generateFilterDefined ops' fst
			forM ops $ \(name, kind) -> do
				let ty = case kind of
					BitSignal -> "bit"
					BusSignal n -> "unsigned ("++show (n-1)++" downto 0)"
				generateLine $ concat ["signal ", name, " : ", ty,";"]
			return ()
		declareOperationSignals :: NetlistOp domain -> HDLGen ()
		declareOperationSignals op = generateVHDLDeclarations $ case op of
			Register _ wa wb -> signalsWires $ wa :. Nil
			Assign wa op -> signalsWires $ wa :. Nil
			Instance entity ins outs -> signalsWires outs
		vhdlOperation :: NetlistOp domain -> HDLGen ()
		vhdlOperation op = case op of
			Register def wa wb -> do
				let c = wireClock wa
				let cn = clockName c
				let edge = (if clockFrontEdge c then "rising_edge" else "falling_edge")
					++"("++cn++")"
				let rn = clockResetName c
				let resetFunc = 
					rn ++ " = "
					++ (if clockResetPositive c then "'1'" else "'0'")
				generateLine $ "process ("++cn++", "++rn++") is"
				generateLine $ "begin"
				generateNest $ do
					generateLine $ unwords ["if",resetFunc, "then"]
					generateNest $ vhdlOperation (Assign wa (constant def))
					generateLine $ unwords ["elsif",edge, "then"]
					generateNest $ vhdlOperation (Assign wa wb)
					generateLine "end if;"
				generateLine $ "end process;"
			Assign wa op -> do
				generateLine $ concat
					[signalName wa, " <= "
					,opToHDL VHDL op, ";"]
			Instance entity ins outs -> do
				let (eins, eouts, eclks) = getInputsOuputsClocks entity
				let insNames = names ins
				let outsNames = names outs
				let einsNames = names eins
				let eoutsNames = names eouts
				let clocks = nub $ clockListClocks eclks
				let resets = nub $ clockListResets eclks
				let connect a b = a ++" => " ++ b
				let allNames = zipWith connect insNames einsNames
					++ zipWith connect outsNames eoutsNames
					++ map (\c -> connect c c) clocks
					++ map (\c -> connect c c) resets
				let withCommas = zipWith (++) ("  ":repeat ", ") allNames
				generateLine "entity ("
				generateNest $ mapM generateLine withCommas
				generateLine ");"
		vhdlText name = do
			generateEmptyLines 2
			generateDashesComment $ "Entity declaration and architecture for "++name++"."
			generateEmptyLines 1
			generateLine "library ieee;"
			generateLine "use ieee.std_logic_1164.all;"
			generateLine "use ieee.numeric_bit.all;"
			generateEmptyLines 1
			generateLine $ "entity "++name++" is"
			generateNest $ do
				generateLine "port ("
				let (inputsNames,inputs) =
					entityPortsList "in" ins
				let (outputsNames, outputs) =
					entityPortsList "out" outs
				let clockResets = generateEntityClocksResets clocks
				let inouts = inputs ++ outputs
				let allSignals = (map snd inouts) ++ clockResets
				let signals = reverse $
					zipWith (++) (reverse allSignals) ("" : repeat ";")
				mapM generateDefineName $ map fst inouts
				generateNest $ do
					mapM generateLine signals
				generateLine ");"
				return $ inputsNames ++ outputsNames
			generateLine $ "end entity "++name++";"
			generateEmptyLines 2
			generateLine $ "architecture hhdl_generated of "++name++" is"
			generateNest $ do
				addSupportFunctions
				mapM declareOperationSignals $ netlistOperations netlist
			generateLine $ "begin"
			generateNest $ do
				mapM vhdlOperation $ netlistOperations netlist
			generateLine $ "end architecture hhdl_generated;"
			return ()

		verilogText name = do
			generateLine $ "Verilog text for entity "++name

		addSupportFunctions = mapM generateLine [
			  replicate 60 '-'
			, "-- Supporting functions."
			, ""
			, "pure function select_func(s : in bit; t, f : in bit) return bit is"
			, "begin"
			, "    if s = '1' then"
			, "        return t;"
			, "    else"
			, "        return f;"
			, "    end if;"
			, "end function select_func;"
			, ""
			, "pure function select_func(s : in bit; t, f : in unsigned) return unsigned is"
			, "begin"
			, "    if s = '1' then"
			, "        return t;"
			, "    else"
			, "        return f;"
			, "    end if;"
			, "end function select_func;"
			, ""
			, "pure function bit_equality(a, b : in bit) return bit is"
			, "begin"
			, "    if a = b then"
			, "        return '1';"
			, "    else"
			, "        return '0';"
			, "    end if;"
			, "end function bit_equality;"
			, ""
			, "pure function bit_equality(a, b : in unsigned) return bit is"
			, "begin"
			, "    if a = b then"
			, "        return '1';"
			, "    else"
			, "        return '0';"
			, "    end if;"
			, "end function bit_equality;"
			, ""
			]

instance GenHDL (Comb ins outs) where
	generateHDL (Comb name index ins outs netlist) = do
		generateHDLForEntity name index ins outs Nil netlist

instance GenHDL (Clocked cs ins outs) where
	generateHDL (Clocked clocks name index ins outs netlist) = do
		generateHDLForEntity name index ins outs clocks netlist

instance GenHDL (Mealy c ins outs) where
	generateHDL (Mealy c name index ins outs netlist) = do
		generateHDLForEntity name index ins outs (c :. Nil) netlist

writeHDLText :: GenHDL a => HDL -> a -> (String -> IO ()) -> IO ()
writeHDLText hdl entity write = do
	let (text, errors) = runHDLGeneration hdl entity
	write text
	case errors of
		[] -> return ()
		errs -> do
			putStrLn $ "\n\n\nErrors:"
			mapM putStrLn errs
			putStrLn "------------------"
			putStrLn $ "Total " ++ show (length errs) ++ " errors in HDL generation."

-------------------------------------------------------------------------------
-- Bit vectors.

data BV size = BV Integer

instance Nat size => BitRepr (BV size) where
	type BitVectorSize (BV size) = size
	toBitVector (BV i) = i
	fromBitVector i = r
		where
			r = BV (i B..&. bitMask r)

instance Show (BV size) where
	showsPrec n (BV i) = (concat [o,Text.Printf.printf "BV 0x%x" i,c]++)
		where
			(o,c)
				| n > 10 = ("(",")")
				| otherwise = ("","")

instance Nat size => Equal (BV size) where
	type EqResult (BV size) = Bool
	a .== b = toBitVector a .== toBitVector b
	a ./= b = toBitVector a ./= toBitVector b

_toSelBusSizeBitVector :: AlgTypeBitEnc a => a -> BV (SelectorBusSize a)
_toSelBusSizeBitVector = undefined

_toSelBusSizeBitVectorWireExpr :: AlgTypeBitEnc a => Wire c a -> BV (SelectorBusSize a)
_toSelBusSizeBitVectorWireExpr = undefined

_toArgsBusSizeBitVector :: AlgTypeBitEnc a => Wire c a -> Wire c (BV (ArgsBusSize a))
_toArgsBusSizeBitVector = undefined

-------------------------------------------------------------------------------
-- Netlist operations.

addNetlistOperation op =
	modify $ \nlms -> nlms {
	  nlmsNetlist = Netlist $ op : netlistOperations (nlmsNetlist nlms)
	}
register :: (ClockAllowed c clocks, BitRepr a, Show a) => a -> Wire c a -> NLM clocks (Wire c a)
register resetValue computedValue = do
	w <- tempWire
	modify $ \nlms -> nlms {
		  nlmsNetlist = Netlist (Register resetValue w computedValue : netlistOperations (nlmsNetlist nlms))
		}
	return w

instantiate :: (Instantiable entity, ClockSubset (EntityClocks entity) clocks
	, WiresList (EntityIns entity), WiresList (EntityOuts entity)) =>
	entity -> EntityIns entity -> NLM clocks (EntityOuts entity)
instantiate entity ins = do
	outs <- mkWireList Nothing
	addNetlistOperation $ Instance entity ins outs
	return outs

assignWire :: (BitRepr ty) => Wire c ty -> NLM registers (Wire c ty)
assignWire what = do
	assignFlattened what

assignWithForcedCopy n wire = do
	t <- mkWire n
	addNetlistOperation $ Assign t wire
	return t

assignFlattened :: (BitRepr ty) => Wire c ty -> NLM registers (Wire c ty)
assignFlattened w@(Wire (sz, WIdent _)) = return w
assignFlattened w@(Wire e) = do
	e <- exprFlatten e
	assignWithForcedCopy Nothing e

extendZero :: (Nat src, Nat dest) => Wire c (BV src) -> Wire c (BV dest)
extendZero (Wire what) = let r = Wire (bitVectorSize r, WUn (Extend ExtZero) what) in r

extendSign :: (Nat src, Nat dest) => Wire c (BV src) -> Wire c (BV dest)
extendSign (Wire what) = let r = Wire (bitVectorSize r, WUn (Extend ExtSign) what) in r

castWires :: (BitRepr src, BitRepr res, BitVectorSize src ~ BitVectorSize res) =>
	Wire c src -> Wire c res
castWires (Wire what) = Wire what

_runPureNetlist :: NLM Nil a -> NLM clocks a
_runPureNetlist action = do
	s <- get
	let (a,s') = runState action (copyNLMS s)
	put (copyNLMSBack s' s)
	return a
	where
		copyNLMS (NLMS (Netlist netlist) cntr) = NLMS (Netlist []) cntr
		copyNLMSBack :: NLMS Nil -> NLMS clocks -> NLMS clocks
		copyNLMSBack (NLMS (Netlist ops1) cntr) (NLMS (Netlist ops2) _)
			= NLMS (Netlist $ copyOps ops1 ops2) cntr
		copyOps :: [NetlistOp Nil] -> [NetlistOp clocks] -> [NetlistOp clocks]
		copyOps [] ops2 = ops2
		copyOps (Assign to what : ops1) ops2 = copyOps ops1 (ops2++[Assign to what])
		copyOps (Instance ent ins outs  : ops1) ops2 = copyOps ops1 (ops2++[Instance ent ins outs])

-------------------------------------------------------------------------------
-- Operations for expressions.

class BitRepr (WireOpListTypes a) => WireOpList a where
	type WireOpListTypes a
--	type WireOpListClock a
	opsToHDL :: HDL -> a -> [String]
instance WireOpList Nil where
	type WireOpListTypes Nil = Nil
	opsToHDL hdl = const []
instance (WireOpList xs
	, Nat (Plus (BitVectorSize x) (BitVectorSize (WireOpListTypes xs)))) => WireOpList (Wire c x :. xs) where
	type WireOpListTypes (Wire c x :. xs) = x :. WireOpListTypes xs
	opsToHDL hdl (a :. as) = opToHDL hdl a : opsToHDL hdl as

type family SplitProjection c w
class BitRepr w => SplitWires w where
	splitWires :: Wire c w -> SplitProjection c w

instance (BitRepr a, BitRepr b, Nat (Plus (BitVectorSize a) (BitVectorSize b)), Nat (BitVectorSize(a,b))) => BitRepr (a,b) where
	type BitVectorSize (a,b) = Plus (BitVectorSize a) (BitVectorSize b)
	toBitVector (x0,x1) = B.shiftL (toBitVector x0) (bitVectorSize x1) B..|. toBitVector x1
	fromBitVector v = (x0,x1)
		where
			x1 = fromBitVector v
			x0 = fromBitVector (B.shiftR v (bitVectorSize x1))

type instance SplitProjection c (a,b) = (Wire c a, Wire c b)
instance (BitRepr a, BitRepr b, BitRepr (a,b)) => SplitWires (a,b) where
	splitWires wab = (wa, wb)
		where
			wa = Wire (bitVectorSize wa, WSlice wab $ wireBusSize wb)
			wb = Wire (bitVectorSize wb, WSlice wab 0)

splitWires2 :: (BitRepr a, BitRepr b, BitRepr (a,b)) => Wire clk (a,b) -> (Wire clk a, Wire clk b)
splitWires2 = splitWires

$(liftM concat $ forM [3..8] $ \n -> let
		typeNames' = map (\i -> TH.mkName ("t_"++show i)) [1..n]
		typeNames = map TH.VarT typeNames'
		ty = foldl TH.AppT (TH.TupleT n) typeNames
		clkN = TH.mkName "clk"
		clk = TH.VarT clkN
		wireTy ty = TH.ConT (TH.mkName "Wire") `TH.AppT` clk `TH.AppT` ty
		wiresTy = foldl TH.AppT (TH.TupleT n) $ map wireTy typeNames
		bitReprP ty = TH.ClassP (TH.mkName "BitRepr") [ty]
		bitVectorSizeT ty = TH.ConT (TH.mkName "BitVectorSize") `TH.AppT` ty
		commonCxt = map bitReprP typeNames
		brCxt = TH.ClassP (TH.mkName "Nat") [bitVectorSizeT ty] : commonCxt
		swCxt = bitReprP ty : commonCxt
		argNames = map (\i -> TH.mkName ("x"++show i)) [1..n]
		shiftNames = map (\i -> TH.mkName ("s"++show i)) [1..n]
		argVars = map TH.VarE argNames
		prevArgs = Prelude.scanr (:) [] argVars
		sumWidths ws = foldr (\a b -> TH.InfixE (Just a) (TH.VarE $ TH.mkName "+") (Just b)) (TH.LitE $ TH.IntegerL 0) $ map (TH.AppE (TH.VarE (TH.mkName "wireBusSize"))) ws
		def v widths = flip (TH.ValD (TH.VarP v)) [] $ TH.NormalB $
			TH.ConE (TH.mkName "Expr") `TH.AppE`
			(TH.ConE (TH.mkName "SplitWiresOp")
				`TH.AppE` vV `TH.AppE` sumWidths widths)
		defs = zipWith def argNames (tail prevArgs)
		vN = TH.mkName "v"
		vV = TH.VarE vN
		bitVecSizeTy = TH.TySynInstD (TH.mkName "BitVectorSize") [ty] $
			foldl1 (\a b -> TH.ConT (TH.mkName "Plus") `TH.AppT` a `TH.AppT` b) $ map bitVectorSizeT typeNames
		defShift Nothing def arg = TH.ValD (TH.VarP def) (TH.NormalB $ TH.LitE $ TH.IntegerL 0) []
		defShift (Just prev) def arg = TH.ValD (TH.VarP def) (TH.NormalB $ TH.InfixE (Just (TH.VarE prev)) (TH.VarE $ TH.mkName "+") (Just sz)) []
			where
				sz = TH.VarE (TH.mkName "bitVectorSize") `TH.AppE` TH.VarE arg
		shiftDefs = Prelude.zipWith3 defShift (map Just (Prelude.init shiftNames) ++ [Nothing]) shiftNames argNames
		toBVE = Prelude.foldr1 (\x y -> TH.InfixE (Just x) (TH.VarE $ TH.mkName "Data.Bits..|.") (Just y))
			$ zipWith (\x s -> TH.VarE (TH.mkName "Data.Bits.shiftL")
				`TH.AppE` (TH.VarE (TH.mkName "toBitVector") `TH.AppE` TH.VarE x)
				`TH.AppE` TH.VarE s) argNames shiftNames
		toBV = TH.FunD (TH.mkName "toBitVector")
			[TH.Clause [TH.TupP $ map TH.VarP argNames] (TH.NormalB toBVE) shiftDefs]
		fromBVEShiftDef x s pxs = [
			  TH.ValD (TH.VarP x) (TH.NormalB convertedX) []
			, TH.ValD (TH.VarP s) (TH.NormalB shiftE) []
			]
			where
				vx = TH.VarE x
				convertedX = TH.VarE (TH.mkName "fromBitVector") `TH.AppE` shiftedV
				shiftedV = TH.VarE (TH.mkName "Data.Bits.shiftR") `TH.AppE` vV `TH.AppE` TH.VarE s
				shiftE = case pxs of
					Nothing -> TH.LitE $ TH.IntegerL 0
					Just (x,s) -> TH.InfixE
						(Just $ TH.VarE (TH.mkName "bitVectorSize") `TH.AppE` TH.VarE x)
						(TH.VarE $ TH.mkName "+")
						(Just $ TH.VarE s)
		shiftArgs as = map Just (tail as) ++ [Nothing]
		fromBVEShiftDefs = concat $ zipWith3 fromBVEShiftDef argNames shiftNames (shiftArgs $ zip argNames shiftNames)
		fromBVE = TH.TupE $ map TH.VarE argNames
		fromBV = TH.FunD (TH.mkName "fromBitVector")
			[TH.Clause [TH.VarP vN] (TH.NormalB fromBVE) fromBVEShiftDefs]
		split = TH.FunD (TH.mkName "splitWires")
			[TH.Clause [TH.VarP vN] (TH.NormalB $ TH.TupE argVars) defs]
		specializedSplitN = TH.mkName $ "splitWires"++show n
		decls = [ TH.InstanceD swCxt (TH.ConT (TH.mkName "SplitWires") `TH.AppT` ty) [split]
			, TH.TySynInstD (TH.mkName "SplitProjection") [clk,ty] wiresTy
			, TH.InstanceD brCxt (TH.ConT (TH.mkName "BitRepr") `TH.AppT` ty) [bitVecSizeTy, toBV, fromBV]
			, TH.SigD specializedSplitN $ TH.ForallT (map TH.PlainTV $ clkN : typeNames') brCxt $ (TH.AppT (TH.AppT TH.ArrowT $ wireTy ty) wiresTy)
			, TH.FunD specializedSplitN [TH.Clause [] (TH.NormalB $ TH.VarE (TH.mkName "splitWires")) []]
			]
	in do
--		runIO $ mapM (putStrLn . show . ppr) decls
		return decls
 )

_castAlgTypeToPair :: (Nat (Plus (SelectorBusSize a) (ArgsBusSize a)), BitRepr a
	, Plus (SelectorBusSize a) (ArgsBusSize a) ~ BitVectorSize a, AlgTypeBitEnc a) => Wire c a -> Wire c (BV (SelectorBusSize a), BV (ArgsBusSize a))
_castAlgTypeToPair w = castWires w
_splitAlgType :: (Plus (SelectorBusSize a) (ArgsBusSize a) ~ BitVectorSize a, Nat (Plus (SelectorBusSize a) (ArgsBusSize a)), AlgTypeBitEnc a, BitRepr a) => Wire c a -> (Wire c (BV (SelectorBusSize a)), Wire c (BV (ArgsBusSize a)))
_splitAlgType w = splitWires $ _castAlgTypeToPair w
_castArgsWires :: (Nat (ArgsBusSize a), AlgTypeBitEnc a, BitRepr a, BitRepr b) => Wire c a -> Wire c (BV (ArgsBusSize a)) -> Wire c b
_castArgsWires a w = r
	where
		r = castWires (extendZero w)

data Join c w where
	Join :: (BitRepr a, BitRepr b) => Wire c a -> Wire c b -> Join c (a :. b)

instance BitRepr w => WireOp (Join c w) where
	type WireOpType (Join c w) = w
	opToHDL hdl (Join l r) = case hdl of
		VHDL -> unwords ["(",opToHDL hdl l,"&",opToHDL hdl r,")"]
		Verilog -> concat ["{",opToHDL hdl l,",",opToHDL hdl r,"}"]
	sizedExpr (Join l r) = liftM2 Join (assignFlattened l) (assignFlattened r)

infixr 5 &
(&) :: (BitRepr a, BitRepr b, Nat (Plus (BitVectorSize a) (BitVectorSize b))) => Wire c a -> Wire c b -> Wire c (a :. b)
a & b = Expr $ Join a b

data Equality c w where
	-- first is the flag for equality testing, if true.
	Equality :: BitRepr w => Bool -> Wire c w -> Wire c w -> Equality c Bool

instance BitRepr w => WireOp (Equality c w) where
	type WireOpType (Equality c w) = w
	opToHDL hdl (Equality eq l r) = case hdl of
		VHDL -> concat ["bit_equality( ", opToHDL hdl l,", ", opToHDL hdl r,")"]
		Verilog -> error "Equality Verilog!!!"
		where
			op = case hdl of
				VHDL -> if eq then "=" else "/="
				Verilog -> if eq then "==" else "!="
	sizedExpr (Equality eq l r) = liftM2 (Equality eq) (assignFlattened l) (assignFlattened r)

instance (Eq w, EqResult w ~ Bool, BitRepr w) => Eq (Wire c w) where
	type EqResult (Wire c w) = Wire c Bool
	a == b = Expr $ Equality True  a b
	a /= b = Expr $ Equality False a b

data Select c w where
	Select :: Wire c Bool -> Wire c a -> Wire c a -> Select c a

instance BitRepr a => WireOp (Select c a) where
	type WireOpType (Select c a) = a
	opToHDL hdl (Select c l r) = case hdl of
		VHDL -> concat["select_func(",cv, ", ", lv,", ",rv,")"]
		Verilog -> error "Verilog Select!!!"
		where
			cv = opToHDL hdl c
			lv = opToHDL hdl l
			rv = opToHDL hdl r
	sizedExpr (Select c l r) = do
		c <- assignFlattened c
		l <- assignFlattened l
		r <- assignFlattened r
		return $ Select c l r

selectWires :: BitRepr a => Wire c Bool -> Wire c a -> Wire c a -> Wire c a
selectWires sel true false = Expr $ Select sel true false

-------------------------------------------------------------------------------
-- Pattern matching.
-- We hardwire (pun intended) Wire(s) into Patterns because we can match
-- only on bit vectors. And those bit vectors get transferred by Wire(s).

type family ConcatPatList a b
type instance ConcatPatList a b = ConcatWiresList (a :. b)
--type instance ConcatPatList (x :. xs) ys = x :. (ConcatPatList xs ys)

class (WiresList (ConcatWiresList a)) => WiresListConcat a where
	type ConcatWiresList a
	concatWiresList :: a -> ConcatWiresList a

instance WiresListConcat Nil where
	type ConcatWiresList Nil = Nil
	concatWiresList Nil = Nil

instance WiresList as => WiresListConcat (Nil :. as) where
	type ConcatWiresList (Nil :. as) = as
	concatWiresList (Nil :. as) = as

instance (WiresListConcat (as :. bs), WiresList (a :. ConcatWiresList (as :. bs))) => WiresListConcat ((a :. as) :. bs) where
	type ConcatWiresList ((a :. as) :. bs) = a :. ConcatWiresList (as :. bs)
	concatWiresList ((a :. as) :. bs) = a :. concatWiresList (as :. bs)

data PatMatch v r where
	PatMatch :: (Wire c v -> NLM Nil (Wire c Bool, Wire c result))
		-> PatMatch (Wire c v) (Wire c result)

data Pattern w o where
	Pattern :: {unPattern :: WiresList o => (Wire c w -> NLM Nil (o, Wire c Bool))} -> Pattern (Wire c w) o

match :: (ClockAllowed c registers, BitRepr v, BitRepr r) => Wire c v
	-> [PatMatch (Wire c v) (Wire c r)] -> NLM registers (Wire c r)
match v ms = do
	w <- assignWire v
	_runPureNetlist $ reduceMatches w ms
	where
		reduceMatches :: BitRepr r => Wire c v -> [PatMatch (Wire c v) (Wire c r)] -> NLM Nil (Wire c r)
		reduceMatches w [] = error "Empty list of pattern matches!"
		reduceMatches w [PatMatch pm] = do
			(_,r) <- pm w
			return r
		reduceMatches w pms = do
			pms' <- reduceMatchesByTwo pms
			reduceMatches w pms'
		reduceMatchesByTwo :: BitRepr r => [PatMatch (Wire c v) (Wire c r)] -> NLM Nil [PatMatch (Wire c v) (Wire c r)]
		reduceMatchesByTwo [] = return []
		reduceMatchesByTwo [pm] = return [pm]
		reduceMatchesByTwo (PatMatch pm1:PatMatch pm2:pms) = do
			let pm = PatMatch $ \v -> do
				(f1,r1) <- pm1 v
				(f2,r2) <- pm2 v
				fw <- assignWire $ f1 || f2
				sw <- assignWire $ selectWires f1 r1 r2
				return (fw, sw)
			pms' <- reduceMatchesByTwo pms
			return $ pm : pms'

infixl 8 -->
(-->) :: WiresList wires => Pattern (Wire c t) wires -> (wires -> NLM Nil (Wire c result))
	-> PatMatch (Wire c t) (Wire c result)
(Pattern p) --> f = PatMatch $ \w -> do
	(ws,flag) <- p w
	r <- f ws
	return (flag, r)

-- |Constant match.
pcst :: (Eq a, EqResult a ~ Bool, Eq (Wire c a), Show a, BitRepr a) => a -> Pattern (Wire c a) Nil
pcst c = Pattern $ \w -> return (Nil, w == constant c)

pvar :: BitRepr a => Pattern (Wire c a) (Wire c a :. Nil)
pvar = Pattern $ \w -> return (w :. Nil, constant True)

pwild :: BitRepr a => Pattern (Wire c a) Nil
pwild = Pattern $ \w -> return (Nil, constant True)

-- Pattern matching for some Prelude types.
$(reifyGenerateMakeMatch [''Maybe, ''Either, ''Bool])

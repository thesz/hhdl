{-# LANGUAGE TemplateHaskell, PatternGuards #-}

module Hardware.HHDL.TH(reifyGenerateMakeMatch, generateMakeMatches) where

import Control.Monad
import Data.List
import Language.Haskell.TH

import Hardware.HHDL.TyLeA

-------------------------------------------------------------------------------
-- Build BitRepr instance, make and pattern combinators for algebraic types.
--
-- For every constructor Cons in declarations we will build mkCons with Cons'
-- arguments wrapped into WireOps amd pCons pattern match which matches
-- constructor against Wire.

generateMakeMatches :: Q [Dec] -> Q [Dec]
generateMakeMatches decs = do
	ds <- decs
	liftM concat $ forM ds generateMakeMatch

reifyGenerateMakeMatch :: [Name] -> Q[Dec]
reifyGenerateMakeMatch names = liftM concat $ mapM checkReifyGenerate names
	where
		checkReifyGenerate n = do
			i <- reify n
			case i of
				TyConI dec -> generateMakeMatchGen dec
				_ -> error $ show n ++ " does not reify to type declaration."

logGen s = runIO $ appendFile "gen" $ s++"\n"

generateMakeMatch dec = liftM (dec:) $ generateMakeMatchGen dec

generateMakeMatchGen :: Dec -> Q [Dec]
generateMakeMatchGen d@(DataD cxt name args conses _)
	| not $ null cxt = declError "Context is not empty."
	| Nothing <- bindersAreVars = declError "Only variable args are supported."
	| Just argVars <- bindersAreVars = do
		let justTyName = mkName $ nameBase name
		ds <- forM (zip [0..] conses) (uncurry $ generateConMakeMatch justTyName argVars)
		argsBusSize <- generateArgsBusSize justTyName argVars conses
		selBusSize <- generateSelBusSize justTyName argVars conses
		bitReprIns <- generateBitRepr justTyName argVars conses
		let result = argsBusSize : selBusSize : bitReprIns ++ concat ds
		logGen $ unlines (map (show . ppr) result)
		return result
	where
		declError e = error $ unlines [
			  e
			, "", ""
			, "Declaration:"
			, show (ppr d)
			]
		bindersAreVars = mapM binderIsVar args
		binderIsVar (PlainTV  v) = return v
		binderIsVar _ = Nothing
generateMakeMatchGen d = return []

generateConMakeMatch :: Name -> [Name] -> Integer -> Con -> Q [Dec]
generateConMakeMatch dataName args selectorIndex c@(NormalC conName types) = do
	return [makeType, makeFunc, matchTypeD, matchFunc]
--	return [matchTypeD, matchFunc]
	where
		matchName = mkName $ "p"++nameBase conName
		matchFunc = FunD matchName
			[Clause argPatterns (NormalB $ ConE (mkName "Pattern") `AppE` (LamE [wP] (DoE matchStats))) []]
		wN = mkName "w"
		wP = VarP wN
		wV = VarE wN
		returnStat e = NoBindS $ VarE (mkName "return") `AppE` e
		cN = mkName "c"
		cP = VarP cN
		cV = VarE cN
		asN = mkName "as"
		asP = VarP asN
		asV = VarE asN
		conpN = mkName "conp"
		conpV = VarE conpN
		conpP = VarP conpN
		resultingCondN = mkName "resultingCond"
		resultingCondV = VarE resultingCondN
		resultingCondP = VarP resultingCondN
		argumentsWiresN = mkName "argumentsWires"
		argumentsWiresV = VarE argumentsWiresN
		argumentsWiresP = VarP argumentsWiresN
		constructorSplit = VarE (mkName "_splitAlgType") `AppE` wV
		argMatch (argPat, argWire, matchResult, matchCond) = BindS
			(TupP [VarP matchResult, VarP matchCond]) f
			where
				unpatterned = VarE (mkName "unPattern") `AppE` VarE argPat
				f = unpatterned `AppE` VarE argWire
		splitWiresN e
			| length types > 1 = VarE (mkName $ "splitWires"++show (length types))
				`AppE` e
			| length types == 1 = e
		splitAssign = case types of
			[] -> []
			[_] -> [LetS
                                [ValD (VarP $ head aws) (NormalB $ castWires $ extendZero asV) []]]
			xs -> [LetS
                                [ ValD argumentsWiresP (NormalB $ castWires $ extendZero asV) []
				, ValD (TupP $ map VarP aws) (NormalB $ splitWiresN argumentsWiresV) []]]
		consT a b = ConT (mkName ":.") `AppT` a `AppT` b
		consE a b = ConE (mkName ":.") `AppE` a `AppE` b
		nil = ConE nilN
		assignWire p e = BindS p $ VarE (mkName "assignWire") `AppE` e
		matchStats = concat [
			  [LetS [ValD (TupP [cP,asP]) (NormalB constructorSplit) []]]
			, splitAssign
			--, [BindS conpP (VarE (mkName "assignWire") `AppE` (VarE (mkName "_fixAsBoolWire") `AppE` (InfixE (Just cV) (VarE $ mkName "==") (Just $ VarE (mkName "asTypeOf") `AppE` (LitE $ IntegerL $ fromIntegral selectorIndex) `AppE` cV ))))]
			, [assignWire conpP (InfixE (Just cV) (VarE $ mkName "==") (Just $ VarE (mkName "asTypeOf") `AppE` (LitE $ IntegerL $ fromIntegral selectorIndex) `AppE` cV ))]
			, map argMatch $ zip4 argNames aws mrs mcs
			, [assignWire resultingCondP $ foldr and conpV $ map VarE mcs]
			, [returnStat $ TupE [concatWLs mrs, resultingCondV]]
			]
			where
				and a b = InfixE (Just a) (VarE $ mkName "&&") (Just b)
				concatWL a = VarE (mkName "concatWiresList") `AppE` a
				concatWLs vs = concatWL $ foldr consE nil $ map VarE mrs
		matchTypeD = SigD matchName matchType
		concatTyLists a b = ConT (mkName "ConcatPatList") `AppT` a `AppT` b
		patternT ty o = ConT (mkName "Pattern") `AppT` wireT ty `AppT` o
		wireT ty = ConT (mkName "Wire") `AppT` clkT `AppT` ty
		nilN = mkName "Nil"
		nilT = ConT nilN
		mkMatchType _ t _ [] [] = let 
			in (patternT resultT nilT, nilT, [], [])
		mkMatchType n t os wss [] = let
				concatenated = add concatTyLists $ reverse $ map VarT wss
				listOfTyLists = foldr consT nilT $ reverse $ map VarT wss
			in (t $ patternT resultT $ ConT (mkName "ConcatWiresList") `AppT` listOfTyLists, concatenated, os, wss)
		mkMatchType n t os wss (ty:tys) =
			mkMatchType (n+1) t' (out:os) (out:wss) tys
			where
				t' = t . (patternT ty (VarT out) `arr`)
				arr a b = ArrowT `AppT` a `AppT` b
				out = mkName $ "o_"++show n
		baseDataTy = foldl AppT (ConT dataName) $ map VarT args
		matchType = ForallT (map PlainTV vars) (nub context) ty
			where
				bitReprInst ty = ClassP (mkName "BitRepr") [ty]
				bitVectorNatInst ty = ClassP (mkName "Nat") [bitVectorSize ty]
				wiresList c = ClassP (mkName "WiresList") [c]
				context = --wiresList cs
					{-:-} bitReprInst baseDataTy
					: bitVectorNatInst baseDataTy
					: ClassP (mkName "AlgTypeBitEnc") [baseDataTy]
					: map (wiresList . VarT) os
					++ map (bitReprInst . VarT) args
					++ map (bitVectorNatInst . VarT) args
					++ argumentsNat
					++ [resultsWiresList]
				(ty,cs,os,vs) = mkMatchType 0 id [] [] (map snd types)
				vars = nub $ tyVars ty
				tyVars (AppT a b) = tyVars a ++ tyVars b
				tyVars (VarT v) = [v]
				tyVars _ = []
		clk = mkName "c"
		clkT = VarT clk
		nameMake = mkName $ "mk"++nameBase conName
		wire = AppT (ConT $ mkName "Wire") clkT
		resultT = foldl AppT (ConT dataName) (map VarT args)
		mkTy [] = AppT wire resultT
		mkTy (t:ts) = AppT (AppT ArrowT (AppT wire (snd t))) (mkTy ts)
		typesVars = nub $ concatMap (typeVars . snd) types ++ args
		typeVars (AppT a b) = typeVars a ++ typeVars b
		typeVars (VarT v) = [v]
		typeVars _ = []
		mkCxt _   [] = []
		mkCxt brs (ty:ts) =
			bitRepr ++ mkCxt (ty:brs) ts
			where
				bitRepr
					| ty `elem` brs = []
					| not (anyVars ty) = []
					| otherwise =
						[ClassP (mkName "BitRepr") [ty]]
		anyVars (AppT a b) = anyVars a || anyVars b
		anyVars (VarT _) = True
		anyVars _ = False
		context = nub $ mkCxt [] (map VarT args ++ map snd types)++algTypeCxt
			++ sumNat (map snd types) ++ [wholeTypeNat]
			++ argumentsNat
		argumentsNat = map sumNat $ init $ tails types
			where
				sumNat ts = ClassP (mkName "Nat") [foldl1 plusT $ map (bitVectorSize . snd) ts]
		resultsWiresList = ClassP (mkName "WiresListConcat")
			[foldr consT nilT $ map (VarT . mkName) $ map (("o_"++) . show) $ zipWith const [0..] types]
		bitVectorSize ty = ConT (mkName "BitVectorSize") `AppT` ty
		natPred ty = ClassP (mkName "Nat") [ty]
		plusT a b = ConT (mkName "Plus") `AppT` a `AppT` b
		sumNat [] = []
		sumNat [ty]
			| anyVars ty = [natPred ty]
			| otherwise = []
		sumNat (ty:tys) = sumNat tys ++ thisNat ++ [sumNats]
			where
				thisNat
					| anyVars ty = [natPred $ bitVectorSize ty]
					| otherwise = []
				(t:ts) = map bitVectorSize $ (ty:tys)
				sumNats = natPred (add plusT $ t:ts)
		add f [a] = a
		add f (a:as) = f a (add f as)
		selectorBusSize ty = ConT selectorBusSizeName `AppT` ty
		argsBusSize ty = ConT (mkName "ArgsBusSize") `AppT` ty
		wholeTypeNat = natPred (foldl1 plusT $ selectorBusSize resultT : argsBusSize resultT : [])
		algTypeCxt
			| not $ null args = [ClassP (mkName "AlgTypeBitEnc") [resultT]]
			| otherwise = []
		makeType = SigD nameMake $ ForallT (map PlainTV $ clk : typesVars) context $ mkTy types
		namesWithPrefix pfx = zipWith (\i _ -> mkName $ pfx++"_"++show i) [0..] types
		argNames = namesWithPrefix "a"
		aws = namesWithPrefix "argumentWire"
		mrs = namesWithPrefix "matchResult"
		mcs = namesWithPrefix "matchCond"
		argPatterns = map VarP argNames
		argsVector = case map VarE argNames of
			[] -> VarE (mkName "constant") `AppE` LitE (IntegerL 0)
			(as) -> extendZero $ castWires $ add join as
		resultN = mkName "result"
		resultV = VarE resultN
		resultD = ValD (VarP resultN)
			(NormalB (castWires (selectorV `join` argsVectorV)))
			[]
		selectorN = mkName "selector"
		selectorV = VarE selectorN
		selectorD = ValD (VarP selectorN) (NormalB sel) []
			where
				sel = VarE (mkName "constant") `AppE` e
				e = InfixE
					(Just $ LitE (IntegerL selectorIndex))
					(VarE $ mkName "asTypeOf")
					(Just $ VarE (mkName "_toSelBusSizeBitVectorWireExpr") `AppE` resultV)
		castWires x = VarE (mkName "castWires") `AppE` x
		join a b = InfixE (Just a) (VarE $ mkName "&") (Just b)
		argsVectorN = mkName "argsVector"
		argsVectorV = VarE argsVectorN
		extendZero e = (VarE $ mkName "extendZero") `AppE` e
		argsVectorD = ValD (VarP argsVectorN) (NormalB r) []
			where
				e = argsVector
				r = InfixE (Just e) (VarE (mkName "asTypeOf"))
					(Just $ VarE (mkName "_toArgsBusSizeBitVector") `AppE` resultV)
		makeFunc = FunD nameMake
			[Clause argPatterns (NormalB resultV)
				[resultD, selectorD, argsVectorD
				]]

generateConMakeMatch dataName args selectorIndex c =
	error $ unlines ["Only normal constructors are supported!", "We're given "++show (ppr c)++"."]

bitVectorSize :: Type -> Type
bitVectorSize a = AppT (ConT $ mkName "BitVectorSize") a
tyBinary f a b = AppT (AppT (ConT $ mkName f) a) b
sizeMax a b = tyBinary "Max" a b
sizeAdd a b = tyBinary "Plus" a b

argumentsBusSize = mkName "ArgsBusSize"

data V a = T a | P (V a) (V a) | M (V a) (V a)
	deriving (Eq, Show)

opt :: Eq a => V a -> V a
opt v = snd r
	where
		r = minimumBy (\a b -> compare (fst a) (fst b)) fixedWeighted
		fixed = incrComb [v]
		fixedWeighted = map (\v -> (nops v, v)) fixed
		incrComb vs
			| length vs == length next = vs
			| otherwise = incrComb next
			where
				next = nub $ concatMap comb vs

{-
t = foldl1 M $ map (foldl1 P) $ map (map T) ts
ts = nub [
	 [1,2]		--	JALR 1.regv 2.RI
	,[3,1,1,2]	--	Ternary	3.TernaryOp 1.regv 1.regv 2.RI
	,[4,1,1]	--	Mult 4.Signed 1.regv 1.regv
	,[4,1,1]	--	Div 4.Signed 1.regv 1.regv
	,[5,1,2,6]	--	Shift 5.ShiftOp 1.regv 2.RI 6.Imm5
	--,[]		--	SysCall
	,[7,1,1]	--	Trap 7.Cond 1.regv 1.regv
	,[2]		--	MFHi 2.RI
	,[2]		--	MFLo 2.RI
	,[1]		--	JR 1.regv
	,[4,1,1,2]	--	SLT 4.Signed 1.regv 1.regv 2.RI
	,[8,1,2,9]	--	Imm16Op 8.ImmOp 1.regv 2.RI 9.Imm16
	,[10,11]	--	J 10.Link 11.Imm26
	,[12,4,1,2,9]	--	Load 12.Gran 4.Signed 1.regv 2.RI 9.Imm16
	,[2,9]		--	LUI 2.RI 9.Imm16
	,[12,1,1,9]	--	Store 12.Gran 1.regv 1.regv 9.Imm16
	,[7,10,1,1,9]	--	Branch 7.Cond 10.Link 1.regv 1.regv 9.Imm16
	]
-}


nops (T _) = 1
nops (P a b) = nops a + nops b + 1
nops (M a b) = nops a + nops b + 1

comb (P a b) = concat [[P x y, P y x] | x <- comb a, y <- comb b]
comb (M a b)
	| a == b = comb a
comb (M (P a b) (P c d))
	| a == c = comb $ P a (M b d)
comb (M (P a b) c)
	| c == a = comb $ P a b
	| c == b = comb $ P a b
comb (M a b) = concat [[M x y, M y x] | x <- comb a, y <- comb b]
comb v = [v]

opt2 :: Eq a => [[a]] -> V a
opt2 [[a]] = T a
opt2 [as] = foldl1 P $ map T as
opt2 tss = result
	where
		inc t [] = [(1,t)]
		inc t ((c,a):cas)
			| t == a = (c+1,a) : cas
			| otherwise = (c,a) : inc t cas
		mostOccured = snd $ maximumBy (\a b -> compare (fst a) (fst b))$
			foldr inc [] $ concat tss
		(withMostOccured', withoutMostOccured) =
			partition (mostOccured `elem`) tss
		delMostOccured [] = []
		delMostOccured (x:xs)
			| x == mostOccured = xs
			| otherwise = x : delMostOccured xs
		withMostOccured = filter (not . null) $
			map delMostOccured withMostOccured'
		left = case withMostOccured of
			[] -> T mostOccured
			_ -> P (T mostOccured) $ opt2 withMostOccured
		right = opt2 withoutMostOccured
		result = case withoutMostOccured of
			[] -> left
			_ -> M left right
		


generateArgsBusSize :: Name -> [Name] -> [Con] -> Q Dec
generateArgsBusSize dataName argVars conses = do
	case interestingConses of
		[] -> return ()
		_ -> do
			logGen $ "Starting expression: "++show v
			logGen $ "Optimized expression: "++show ov
	return result
	where
		result = TySynInstD argumentsBusSize
			[foldl AppT (ConT dataName) (map VarT argVars)] $
			newVariant
		newVariant = case interestingConses of
			[] -> tySizePure 0
			_ -> fromV ov
		oldVariant =
			case conArgsSizes of
				[] -> tySizePure 0
				cs -> foldl1 (\a b -> sizeMax a b) cs
		fromV (T t) = bitVectorSize t
		fromV (P a b) = sizeAdd (fromV a) (fromV b)
		fromV (M a b) = sizeMax (fromV a) (fromV b)
		consesArgs :: [[Type]]
		consesArgs = map conArgs conses
		conArgs (NormalC _ as) = map snd as
		conArgs c = error $ "Unsupported constructor "++show (ppr c)
		conArgsSizes = map conArgsSize interestingConses
		interestingConses = nub $ filter (not . null) consesArgs
		v = foldl1 M $ map (foldl1 P) $ map (map T) interestingConses
		ov =
			--opt v
			opt2 interestingConses
		conArgsSize [] = tySizePure 0
		conArgsSize as = foldl1 sizeAdd (map bitVectorSize as)

selectorBusSizeName = mkName "SelectorBusSize"

generateSelBusSize :: Name -> [Name] -> [Con] -> Q Dec
generateSelBusSize dataName argVars conses = do
	return result
	where
		result = TySynInstD selectorBusSizeName
			[foldl AppT (ConT dataName) (map VarT argVars)] $
			tySizePure (log2 $ length conses)

log2 0 = 0
log2 1 = 0
log2 n = 1 + log2 (div (n+1) 2)

generateBitRepr :: Name -> [Name] -> [Con] -> Q [Dec]
generateBitRepr dataName argVars conses = return [bitReprInstance, algTypeEncInstance]
	where
		bitReprName = mkName "BitRepr"
		algTypeEncName = mkName "AlgTypeBitEnc"
		bitReprInstance = InstanceD context (AppT (ConT bitReprName) dataType) decls
		algTypeEncInstance = InstanceD
			[ClassP (mkName "Nat") [AppT (ConT $ mkName "ArgsBusSize") dataType]]
			(AppT (ConT algTypeEncName) dataType)
			[]
		dataType = foldl AppT (ConT dataName) (map VarT argVars)
		decls = [bitVectorSizeInst, toBitVector, fromBitVector]
		context = natHeads++varBitRepr++[algType]
		natHeads = map (\t -> ClassP (mkName "Nat") [t])
			[bitVectorSize dataType] --, AppT (ConT $ mkName "ArgsBusSize") dataType]
		varBitRepr = map (\v -> ClassP bitReprName [VarT v]) argVars
		algType = ClassP algTypeEncName [dataType]

		nx = mkName "x"
		vx = VarE nx
                toBitVector = FunD (mkName "toBitVector") [Clause [VarP nx] (NormalB toBitVectorCase) []]
		toBitVectorCase = CaseE vx $ zipWith toBitVectorConsMatch [0..] conses
		nxi = zipWith (\i _ -> mkName $ "x_"++show i) [0..]
		nsi = zipWith (\i _ -> mkName $ "s_"++show i) [0..]
		pxi = map VarP . nxi
		vxi = map VarE . nxi
		toBitVectorConsMatch i (NormalC cn as) = Match pattern (NormalB e) []
			where
				pattern = AsP (mkName "y") (ConP (mkName $ nameBase cn) (pxi as))
				ci = LitE $ IntegerL (fromIntegral i)
				vs = vxi as
				argsVector = foldl combine (LitE $ IntegerL 0) vs
				combine acc x = r
					where
						sacc = VarE (mkName "Data.Bits.shiftL") `AppE` acc `AppE` (AppE (VarE $ mkName $ "bitVectorSize") x)
						r = InfixE (Just sacc) (VarE $ mkName "Data.Bits..|.") (Just $ VarE (mkName "toBitVector") `AppE` x)
				e = (VarE $ mkName "_combineConstructorIndexArgs") `AppE` argsVector `AppE` (VarE (mkName "algTypeArgsBusSize") `AppE` VarE (mkName "y")) `AppE` ci
                fromBitVector = FunD (mkName "fromBitVector") [Clause [VarP nx] (NormalB (VarE $ mkName "r"))
			[ValD (VarP nr) (NormalB fromBitVectorE) []]]
		nr = mkName "r"
		vr = VarE $ nr
		fromBitVectorConsMatch i (NormalC n as) =
				Match (LitP $ IntegerL (fromInteger i)) (NormalB r) decls
			where
				xs = nxi as
				ss = nsi as
				decls = snd $ foldl accShift (LitE $ IntegerL 0, []) (zip ss xs)
				accShift (p,acc) (s,x) = (VarE s,sdecl:xdecl:acc)
					where
						xdecl = ValD (VarP x)
							(NormalB $ VarE (mkName "fromBitVector") `AppE` (VarE (mkName "Data.Bits.shiftR") `AppE` vx `AppE` p))
							[]
						sdecl = ValD (VarP s)
							(NormalB $ InfixE (Just p) (VarE $ mkName "+") (Just $ VarE (mkName "bitVectorSize") `AppE` VarE x))
							[]
				r = foldr (flip AppE) (ConE $ mkName $ nameBase n) (map VarE xs)
		fromBitVectorE = CaseE sel $ zipWith fromBitVectorConsMatch [0..] conses
			where
				sel = InfixE (Just shifted) (VarE $ mkName "Data.Bits..&.") (Just $ VarE (mkName "algTypeSelectorBusMask") `AppE` vr)
				shifted = (VarE $ mkName "Data.Bits.shiftR") `AppE` vx `AppE` (VarE (mkName "algTypeArgsBusSize") `AppE` vr)
		bitVectorSizeInst = TySynInstD (mkName "BitVectorSize") [dataType]
			(sizeAdd (AppT (ConT selectorBusSizeName) dataType)
				(AppT (ConT argumentsBusSize) dataType))

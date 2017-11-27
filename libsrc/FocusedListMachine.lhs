> {-# LANGUAGE MultiParamTypeClasses, RankNTypes, GADTs, TupleSections
> , DeriveFunctor, ScopedTypeVariables, DataKinds, KindSignatures, TypeFamilies
> , PolyKinds, TypeOperators, FlexibleContexts, FlexibleInstances
> , NoMonomorphismRestriction, TypeSynonymInstances, KindSignatures
> , ImpredicativeTypes #-}

> module FocusedListMachine where

== Imports ==

DSL-Interpreter pairings & their construction

< import Control.Monad
< import Control.Comonad

> import Control.Monad.Free
> import Control.Comonad.Cofree

< import Data.Functor.Adjunction

> import Data.Functor.Pairing

In here, we use corecords for the programs, and records for the interpreters.

> import Data.Vinyl
> import Data.Vinyl.CoRec
> import Data.Vinyl.Functor
> import Data.Proxy
> import Data.Functor.Product

Notation

> import Control.Arrow ((&&&), first)

Algorithms

> import Data.Maybe (mapMaybe)



== Orientation ==

* Transpose: Inventory analogy

* Cofree for interpreters, free for DSLs (Liang)
** Divides goals well
* Sum and product types w/ same labels of factors ~ Corecords and records
** Expresses divisions in implementation well and nimble code derivation

* Transpose: GUI projections



== Machines ==

* Benefits of trying to implement a couple actions directly before proceeding
** Exercizes with holes

-----



Use of records here has nothing to do with use for DSLs and interpreters.
The goal of using Vinyl over plain records here is to reuse code for handling
commands as transitions of different machines as subrecord updates.



> type LimaStateFactors sym =
> 	'[ '("LimaSymTable", [sym])
> 	, '("LimaFocusMain", Maybe Int)
> 	, '("LimaFocusPicked", Maybe Int)
> 	, '("LimaFocusSelection", [Int]) ]

> type FocusedLimaStateFactors sym =
> 	'[ '("LimaSymTable", [sym])
> 	, '("LimaFocusMain", Maybe Int) ]

> type BifocusedLimaStateFactors sym =
> 	'[ '("LimaSymTable", [sym])
> 	, '("LimaFocusMain", Maybe Int)
> 	, '("LimaFocusPicked", Maybe Int) ]

> type SelectingLimaStateFactors sym =
> 	'[ '("LimaSymTable", [sym])
> 	, '("LimaFocusMain", Maybe Int)
> 	, '("LimaFocusSelection", [Int]) ]



> newtype FocusedLima sym
> 	= FocusedLima (FieldRec (FocusedLimaStateFactors sym))
> 	deriving (Show)

> newtype BifocusedLima sym
> 	= BifocusedLima (FieldRec (BifocusedLimaStateFactors sym))
> 	deriving (Show)

> newtype SelectingLima sym
> 	= SelectingLima (FieldRec (SelectingLimaStateFactors sym))
> 	deriving (Show)

> instance Functor FocusedLima where
> 	fmap f ( FocusedLima (x :& xs) ) = FocusedLima
> 		$ fieldMap (fmap f) x :& rmap id xs

> overBFLimaAsFLima ::
> 	( FocusedLima a -> FocusedLima b )
> 	-> BifocusedLima a -> BifocusedLima b
> overBFLimaAsFLima f ( BifocusedLima xs ) = BifocusedLima
> 	 	$ {- Over newtype wrapper ~ over it as a FocusedLima -}
> 		( ( (\(FocusedLima a) -> a) . ) . (. FocusedLima) )
> 			f
> 			(rcast xs)
> 		{- And leave the rest as it is -}
> 	 	<+> rmap id (rcast xs)

> instance Functor BifocusedLima where
> 	fmap f = overBFLimaAsFLima (fmap f)

> overSelLimaAsFLima ::
> 	( FocusedLima a -> FocusedLima b )
> 	-> SelectingLima a -> SelectingLima b
> overSelLimaAsFLima f ( SelectingLima xs ) = SelectingLima
> 	 	$ {- Over newtype wrapper ~ over it as a FocusedLima -}
> 		( ( (\(FocusedLima a) -> a) . ) . (. FocusedLima) )
> 			f
> 			(rcast xs)
> 		{- And leave the rest as it is -}
> 	 	<+> rmap id (rcast xs)

> instance Functor SelectingLima where
> 	fmap f = overSelLimaAsFLima (fmap f)



=== Bounding indices ===

> predAsNat :: Int -> Int
> predAsNat z | z <= 0 = 0
> predAsNat z = pred z

> succBoundedBy :: Int -> Int -> Int
> succBoundedBy b z | b > (1+z) = (1+z)
> succBoundedBy b _ = b-1

> clampAt :: Int -> Int -> Int
> clampAt k z = if z < 0 then 0
> 	else if z > (k-1) then (k-1)
> 	else z



=== Setting, inserting, & deleting on the symbol table ===

* Underlying BFLima library, specs

-----

> insertAt :: Int -> sym -> [sym] -> [sym]
> insertAt i x = uncurry (++) . fmap (x:) . splitAt i

> replaceAt :: Int -> sym -> [sym] -> [sym]
> replaceAt i x = uncurry (++) . fmap ((x:) . tail) . splitAt i

> deleteAt :: Int -> [sym] -> [sym]
> deleteAt i = uncurry (++) . fmap tail . splitAt i



=== Measuring ===

> getSymTableSize :: forall sym rs proxy. ( '("LimaSymTable", [sym]) ∈ rs )
> 	=> proxy sym -> FieldRec rs -> Int
> getSymTableSize _ =
> 	length . getField . rget (Proxy :: Proxy '("LimaSymTable", [sym]))

> getListPartSize_flima :: forall sym. FocusedLima sym -> Int
> getListPartSize_flima (FocusedLima xs) = getSymTableSize (Proxy :: Proxy sym) xs

> getListPartSize_bf :: forall sym. BifocusedLima sym -> Int
> getListPartSize_bf (BifocusedLima xs) = getSymTableSize (Proxy :: Proxy sym) xs

> getListPartSize_sellima :: forall sym. SelectingLima sym -> Int
> getListPartSize_sellima (SelectingLima xs) = getSymTableSize (Proxy :: Proxy sym) xs



== Categories of atomic terms ==

* Clean up bit on pairings below.
* Move pairings & (co)records to appropriate places.

* Discrete

* Transpose:
** A criterion for minimizing...
** Organizing command ontology...

* Symbol commands
* Focus commands
* Focused list machine commands
* Bifocused list machine commands

-----

Support

> data IY (inTy :: l -> * -> *) (outTy :: l -> * -> *) (a :: *) (k :: *) (term :: l)
> 	= IYform (inTy term a, outTy term a -> k)

> data RO (inTy :: l -> * -> *) (outTy :: l -> * -> *) (a :: *) (k :: *) (term :: l)
> 	= ROform (inTy term a -> (outTy term a, k))

> newtype Cmd xs inTy outTy a k = Cmd( CoRec (IY inTy outTy a k) xs )

> newtype Hdl xs inTy outTy a k = Hdl( Rec (RO inTy outTy a k) xs )

> type Prgm xs inTy outTy a k = Free (Cmd xs inTy outTy a) k

> type Interp xs inTy outTy a k = Cofree (Hdl xs inTy outTy a) k



> -- | Could be treated as a functor instance for the last-argpair flip
> -- Then, as if derived instance.
> iyMap :: (k -> k') -> IY inTY outTy a k l -> IY inTY outTy a k' l
> iyMap f (IYform (l, r)) = IYform (l, f . r)

or
< iyMap f (IYform lr) = IYform $ fmap (f.) lr

> -- | Could be treated as a functor instance for the last-argpair flip
> -- Then, as if derived instance.
> roMap :: (k -> k') -> RO inTY outTy a k l -> RO inTY outTy a k' l
> roMap f (ROform fnToO) = ROform $ (fmap . fmap) f fnToO

> instance Functor (Hdl xs inTy outTy a) where
> 	fmap f (Hdl r) = Hdl (rmap (roMap f) r)

> instance Functor (Cmd xs inTy outTy a) where
> 	fmap f (Cmd (CoRec iy)) = (Cmd (CoRec (iyMap f iy)))



> pairCH_typical :: Pairing (Cmd xs inTy outTy a) (Hdl xs inTy outTy a)
> pairCH_typical fn (Hdl h) (Cmd (CoRec (IYform (i, kfn))))
> 	= case rget Proxy h of ROform g -> (pairRL . pairLR) fn g (i, kfn)

Hahahahaha that was so easy.
Credit to (Data.Vinyl.CoRec.match).

> instance CmdsHandlersPair (Cmd xs inTy outTy a) (Hdl xs inTy outTy a)
> 	where pairCH = pairCH_typical

-----



About newtypes below:
* We need both pattern matching and partial application.
Type families can't be partially applied.
* Shape of recursive sublanguages' command and handler functor newtypes:
** Squashes the newtypes for nonrecursive sublanguage input & output functor
newtypes into the constructions of `IY` & `RO` & how they reorder the arguments
so that the language term is last, & they can be a functor over language terms,
so they can form co/records over the term category.



> data LimaSymTerm = LimaSetSym | LimaGetSym

> type LimaSymTerms = ['LimaSetSym, 'LimaGetSym]

> type family LimaSym_InTy (t :: LimaSymTerm) (a :: *) :: * where
> 	LimaSym_InTy 'LimaSetSym a = a
> 	LimaSym_InTy 'LimaGetSym a = ()

> type family LimaSym_OutTy (t :: LimaSymTerm) (a :: *) :: * where
> 	LimaSym_OutTy 'LimaSetSym a = ()
> 	LimaSym_OutTy 'LimaGetSym a = Maybe a

> newtype LimaSym_InTy' f a
> 	= LimaSym_InTy' (LimaSym_InTy f a)

> newtype LimaSym_OutTy' f a
> 	= LimaSym_OutTy' (LimaSym_OutTy f a)



> data LimaIndTerm =
> 	LimaGetFocusInd
> 	| LimaRefocusInd
> 	| LimaTrashFocus
> 	| LimaRefocusNext
> 	| LimaRefocusPrev

> type LimaIndTerms =
> 	[ 'LimaGetFocusInd
> 	, 'LimaRefocusInd
> 	, 'LimaTrashFocus
> 	, 'LimaRefocusNext
> 	, 'LimaRefocusPrev ]

> type family LimaInd_InTy (t :: LimaIndTerm) (a :: *) :: * where
> 	LimaInd_InTy 'LimaGetFocusInd a = ()
> 	LimaInd_InTy 'LimaRefocusInd a = Maybe Int
> 	LimaInd_InTy 'LimaTrashFocus a = ()
> 	LimaInd_InTy 'LimaRefocusNext a = ()
> 	LimaInd_InTy 'LimaRefocusPrev a = ()

> type family LimaInd_OutTy (t :: LimaIndTerm) (a :: *) :: * where
> 	LimaInd_OutTy 'LimaGetFocusInd a = Maybe Int
> 	LimaInd_OutTy 'LimaRefocusInd a = ()
> 	LimaInd_OutTy 'LimaTrashFocus a = ()
> 	LimaInd_OutTy 'LimaRefocusNext a = ()
> 	LimaInd_OutTy 'LimaRefocusPrev a = ()

> newtype LimaInd_InTy' f a
> 	= LimaInd_InTy' (LimaInd_InTy f a)

> newtype LimaInd_OutTy' f a
> 	= LimaInd_OutTy' (LimaInd_OutTy f a)



Then where the focus command terms would normally be

< type LimaFocusTerms =
< 	[ 'LimaFocusIndTerm
< 	, 'LimaFocusSymTerm ]

and bound like

< type family LimaFocus_CmdTy (t :: LimaFocusTerm) :: * -> * -> * where
< 	LimaFocus_CmdTy 'LimaFocusIndTerm = LimaIndCmd
< 	...

we ignore the term category for that language and implement the command
and handler types as independent datatypes.

This is to avoid requiring dependently typed functions.



> data BFLimaListTerm =
> 	BFLimaInsertSym
> 	| BFLimaDeleteSym

> type BFLimaListTerms =
> 	[ 'BFLimaInsertSym
> 	, 'BFLimaDeleteSym ]

> type family BFLimaList_InTy (t :: BFLimaListTerm) (a :: *) :: * where
> 	BFLimaList_InTy 'BFLimaInsertSym a = a
> 	BFLimaList_InTy 'BFLimaDeleteSym a = ()

> type family BFLimaList_OutTy (t :: BFLimaListTerm) (a :: *) :: * where
> 	BFLimaList_OutTy 'BFLimaInsertSym a = ()
> 	BFLimaList_OutTy 'BFLimaDeleteSym a = ()

> newtype BFLimaList_InTy' f a
> 	= BFLimaList_InTy' (BFLimaList_InTy f a)

> newtype BFLimaList_OutTy' f a
> 	= BFLimaList_OutTy' (BFLimaList_OutTy f a)



Same story as `LimaFocusTerms`, where we'd have the termlist

< type BFLimaTerms =
< 	[ 'BFLimaListPartTerm
< 	, 'BFLimaMainFocusTerm
< 	, 'BFLimaPickedFocusTerm ]

but implement the command and handler types independently & discard the
term category.



== DSL commands ==

* Everything

-----



About the below newtypes:
* For languages with recursive sublanguages:
** Shape is the newtype wrapper of `Cmd`, which alters argument order,
squashed in with the establishing of shorthand notation that siblings'
type synonyms perform.
* For the languages without recursive sublanguages:
** Newtype involved since otherwise there's multiple copies of (`Cmd` [exact args])
appearing in other places, leading to error propogation.

> newtype LimaSymCmd a k
> 	= LimaSymCmd (Cmd LimaSymTerms LimaSym_InTy' LimaSym_OutTy' a k)
> 	deriving (Functor)

> newtype LimaIndCmd a k
> 	= LimaIndCmd (Cmd LimaIndTerms LimaInd_InTy' LimaInd_OutTy' a k)
> 	deriving (Functor)

> data LimaFocusCmd a k =
> 	LimaFocusIndCmd (LimaIndCmd a k)
> 	| LimaFocusSymCmd (LimaSymCmd a k)
> 	deriving (Functor)



> newtype BFLimaListCmd a k
> 	= BFLimaListCmd (Cmd BFLimaListTerms BFLimaList_InTy' BFLimaList_OutTy' a k)
> 	deriving (Functor)

> data BFLimaCmd a k =
> 	BFLimaListPartCmd (BFLimaListCmd a k)
> 	| BFLimaMainFocusCmd (LimaFocusCmd a k)
> 	| BFLimaPickedFocusCmd (LimaFocusCmd a k)
> 	deriving (Functor)



== Handlers ==

* Compare ontologies ((commands -> operations) by reaction policies,
	implementations, cocommands, coatoms)

-----



About the below newtypes:
* For the languages without recursive sublanguages:
** Newtype involved since otherwise there's multiple copies of (`Cmd` [exact args])
appearing in other places, leading to error propogation.

> newtype LimaSymHdl a k
> 	= LimaSymHdl (Hdl LimaSymTerms LimaSym_InTy' LimaSym_OutTy' a k)
> 	deriving (Functor)

> newtype LimaIndHdl a k
> 	= LimaIndHdl (Hdl LimaIndTerms LimaInd_InTy' LimaInd_OutTy' a k)
> 	deriving (Functor)

> data LimaFocusHdl a k = LimaFocusHdl {
> 	limaFocusIndHdl :: LimaIndHdl a k
> 	, limaFocusSymHdl :: LimaSymHdl a k
>	}	deriving (Functor)



> newtype BFLimaListHdl a k
> 	= BFLimaListHdl (Hdl BFLimaListTerms BFLimaList_InTy' BFLimaList_OutTy' a k)
> 	deriving (Functor)

> data BFLimaHdl a k = BFLimaHdl {
> 	bflimaListPartHdl :: BFLimaListHdl a k
> 	, bflimaMainFocusHdl :: LimaFocusHdl a k
> 	, bflimaPickedFocusHdl :: LimaFocusHdl a k
> 	}	deriving (Functor)



=== Handler type by solving for duality with commands type ===

* Derive, explain, replace derivation of handler type train of thought
& cmd-handlers pairing train of thought

-----



> instance CmdsHandlersPair (LimaSymCmd a) (LimaSymHdl a)
> 	where pairCH fn (LimaSymHdl r) (LimaSymCmd c) = pairCH fn r c

> instance CmdsHandlersPair (LimaIndCmd a) (LimaIndHdl a)
> 	where pairCH fn (LimaIndHdl r) (LimaIndCmd c) = pairCH fn r c

> instance CmdsHandlersPair (LimaFocusCmd a) (LimaFocusHdl a)
> 	where
> 	pairCH fn (LimaFocusHdl r _) (LimaFocusIndCmd c) = pairCH fn r c
> 	pairCH fn (LimaFocusHdl _ r) (LimaFocusSymCmd c) = pairCH fn r c



> instance CmdsHandlersPair (BFLimaListCmd a) (BFLimaListHdl a)
> 	where pairCH fn (BFLimaListHdl r) (BFLimaListCmd c) = pairCH fn r c

> instance CmdsHandlersPair (BFLimaCmd a) (BFLimaHdl a)
> 	where
> 	pairCH fn (BFLimaHdl r _ _) (BFLimaListPartCmd c) = pairCH fn r c
> 	pairCH fn (BFLimaHdl _ r _) (BFLimaMainFocusCmd c) = pairCH fn r c
> 	pairCH fn (BFLimaHdl _ _ r) (BFLimaPickedFocusCmd c) = pairCH fn r c



=== Configurations ===

* Explanation
* Library - functions
* Library - operations
* Library - handler configurations

-----



Support

> liftRO ::
> 	( inTy' term a -> i ) {- Decompose input -}
> 	-> ( o -> outTy' term a ) {- Compose output -}
> 	-> proxy term
> 	-> ( d -> (i -> (o, b)) ) {- Goal process -}
> 	{- Lifted process for configuring a handler to use -}
> 	-> d -> RO inTy' outTy' a b term
> liftRO decomp comp _ fn d = ROform $ first comp . fn d . decomp

-----



> liftCoLimaSym ::
> 	proxy term
> 	-> ( d -> (LimaSym_InTy term a -> (LimaSym_OutTy term a, b)) )
> 	-> d -> RO LimaSym_InTy' LimaSym_OutTy' a b term
> liftCoLimaSym = liftRO (\(LimaSym_InTy' a) -> a) LimaSym_OutTy'

Here we start with the operation you might already have expressed as
an update to a piece of state.

< coLimaSetSymIntuitive :: a -> (a -> a)
< coLimaSetSymIntuitive = const id

This is not far from something that can be used to configure a handler.
All it needs is for the result function to produce some output, some
response for future programs, not considering its side effects on state.

This version conforms to the structure of a handler projection for the
`LimaSetSym` command:

> coLimaSetSym :: a -> (a -> ((), a))
> coLimaSetSym = const $ (const () &&& id)

That can then be lifted to an explicitly typed handler factor

< coLimaSetSymRO :: a -> RO LimaSym_InTy' LimaSym_OutTy' a a 'LimaSetSym
< coLimaSetSymRO = liftCoLimaSym (Proxy :: Proxy 'LimaSetSym)
< 	coLimaSetSymConforming

Could also deconstruct the `Hdl` part and `(<+>)` instead of `(:&)`, but this
makes the transition in types less transparent when developing from
featureset to handlerset

< coLimaSetSymHdl ::
< 	a -> Hdl '[ 'LimaSetSym ] LimaSym_InTy' LimaSym_OutTy' a a
< coLimaSetSymHdl = Hdl . (:& RNil) . coLimaSetSymRO

Likewise for LimaGetSym, the configuration of a state symbol's getting is
the determination of what `Maybe a` will be given when requesting this
state, together with the no-op update to the state this request does.

< coLimaGetSymIntuitive :: a -> (Maybe a, a)
< coLimaGetSymIntuitive = (Just &&& id)

> coLimaGetSym :: a -> (() -> (Maybe a, a))
> coLimaGetSym = const . (Just &&& id)

< coLimaGetSymRO :: a -> RO LimaSym_InTy' LimaSym_OutTy' a a 'LimaGetSym
< coLimaGetSymRO = liftCoLimaSym (Proxy :: Proxy 'LimaGetSym) coLimaGetSym

Putting together the two handler factors gives us the fully configured handler,
or rather putting together the two initializers of command interpretations
gives an initializer for the handler.

< confLimaSymHdl :: a -> LimaSymHdl a a
< confLimaSymHdl a = LimaSymHdl . Hdl
< 	$ coLimaSetSymRO a :& coLimaGetSymRO a :& RNil

The process for lifting conforming command initializers being regular plumbing,
we can treat it as setting the fields of the handler, leading to a nice, isolated
point at which consistency of all field values with the commands they handle is
enforced as written, at the culmination of the language handling implementation
and by the lift specialized at its preparation.

> confLimaSymHdl :: a -> LimaSymHdl a a
> confLimaSymHdl a = LimaSymHdl . Hdl
> 	$ liftCoLimaSym (Proxy :: Proxy 'LimaSetSym) coLimaSetSym a
> 	:& liftCoLimaSym (Proxy :: Proxy 'LimaGetSym) coLimaGetSym a
> 	:& RNil



From the top:

> atfocCoLimaSetSymIntuitive :: ([sym], Maybe Int) -> (sym -> ([sym], Maybe Int))
> atfocCoLimaGetSymIntuitive :: ([sym], Maybe Int) -> (Maybe sym, ([sym], Maybe Int))

> atfocCoLimaSetSymIntuitive state@(_, Nothing) = const state
> atfocCoLimaSetSymIntuitive (syms, mi@(Just i)) = (flip (replaceAt i) syms &&& const mi)

> atfocCoLimaGetSymIntuitive state@(_, Nothing) = (Nothing, state)
> atfocCoLimaGetSymIntuitive state@(syms, Just i) = (Just (syms!!i), state)

> atfocCoLimaSetSym :: ([sym], Maybe Int) -> (sym -> ((), ([sym], Maybe Int)))
> atfocCoLimaGetSym :: ([sym], Maybe Int) -> (() -> (Maybe sym, ([sym], Maybe Int)))

> atfocCoLimaSetSym = fmap ((),) . atfocCoLimaSetSymIntuitive
> atfocCoLimaGetSym = const . atfocCoLimaGetSymIntuitive

> confLimaFocusSymHdl :: ([sym], Maybe Int) -> LimaSymHdl sym ([sym], Maybe Int)
> confLimaFocusSymHdl a = LimaSymHdl . Hdl
> 	$ liftCoLimaSym (Proxy :: Proxy 'LimaSetSym) atfocCoLimaSetSym a
> 	:& liftCoLimaSym (Proxy :: Proxy 'LimaGetSym) atfocCoLimaGetSym a
> 	:& RNil



> liftCoLimaInd ::
> 	proxy term
> 	-> ( d -> (LimaInd_InTy term a -> (LimaInd_OutTy term a, b)) )
> 	-> d -> RO LimaInd_InTy' LimaInd_OutTy' a b term
> liftCoLimaInd = liftRO (\(LimaInd_InTy' a) -> a) LimaInd_OutTy'

> coLimaGetFocusIndIntuitive :: ([sym], Maybe Int) -> (Maybe Int, ([sym], Maybe Int))
> coLimaRefocusIndIntuitive :: ([sym], Maybe Int) -> (Maybe Int -> ([sym], Maybe Int))
> coLimaTrashFocusIntuitive :: ([sym], Maybe Int) -> ([sym], Maybe Int)
> coLimaRefocusNextIntuitive :: ([sym], Maybe Int) -> ([sym], Maybe Int)
> coLimaRefocusPrevIntuitive :: ([sym], Maybe Int) -> ([sym], Maybe Int)

> coLimaGetFocusIndIntuitive = (snd &&& id)
> coLimaRefocusIndIntuitive = flip $ fmap . const
> coLimaTrashFocusIntuitive = fmap $ const Nothing
> coLimaRefocusNextIntuitive state@(syms, _)
> 	= ( fmap . fmap ) ( succBoundedBy (length syms) ) state
> coLimaRefocusPrevIntuitive = fmap . fmap $ predAsNat

> coLimaGetFocusInd :: ([sym], Maybe Int) -> ( () -> ( Maybe Int, ([sym], Maybe Int) ) )
> coLimaRefocusInd :: ([sym], Maybe Int) -> ( Maybe Int -> ( (), ([sym], Maybe Int) ) )
> coLimaTrashFocus :: ([sym], Maybe Int) -> ( () -> ( (), ([sym], Maybe Int) ) )
> coLimaRefocusNext :: ([sym], Maybe Int) -> ( () -> ( (), ([sym], Maybe Int) ) )
> coLimaRefocusPrev :: ([sym], Maybe Int) -> ( () -> ( (), ([sym], Maybe Int) ) )

> coLimaGetFocusInd = const . coLimaGetFocusIndIntuitive
> coLimaRefocusInd = fmap ((),) . coLimaRefocusIndIntuitive
> coLimaTrashFocus = const . ((),) . coLimaTrashFocusIntuitive
> coLimaRefocusNext = const . ((),) . coLimaRefocusNextIntuitive
> coLimaRefocusPrev = const . ((),) . coLimaRefocusPrevIntuitive

> confLimaIndHdl :: ([sym], Maybe Int) -> LimaIndHdl sym ([sym], Maybe Int)
> confLimaIndHdl a = LimaIndHdl . Hdl
> 	$ liftCoLimaInd (Proxy :: Proxy 'LimaGetFocusInd) coLimaGetFocusInd a
> 	:& liftCoLimaInd (Proxy :: Proxy 'LimaRefocusInd) coLimaRefocusInd a
> 	:& liftCoLimaInd (Proxy :: Proxy 'LimaTrashFocus) coLimaTrashFocus a
> 	:& liftCoLimaInd (Proxy :: Proxy 'LimaRefocusNext) coLimaRefocusNext a
> 	:& liftCoLimaInd (Proxy :: Proxy 'LimaRefocusPrev) coLimaRefocusPrev a
> 	:& RNil



> confLimaFocusHdl :: ([sym], Maybe Int) -> LimaFocusHdl sym ([sym], Maybe Int)
> confLimaFocusHdl = uncurry LimaFocusHdl
> 	. (confLimaIndHdl &&& confLimaFocusSymHdl)



> liftCoBFLimaList ::
> 	proxy term
> 	-> ( d -> (BFLimaList_InTy term a -> (BFLimaList_OutTy term a, b)) )
> 	-> d -> RO BFLimaList_InTy' BFLimaList_OutTy' a b term
> liftCoBFLimaList = liftRO (\(BFLimaList_InTy' a) -> a) BFLimaList_OutTy'

> coFLimaInsertSymIntuitive :: FocusedLima sym -> ( sym -> FocusedLima sym )
> coFLimaDeleteSymIntuitive :: FocusedLima sym -> FocusedLima sym

> coFLimaInsertSymIntuitive ( FocusedLima (Field syms :& Field Nothing :& RNil) ) s
> 	= FocusedLima $ Field (s:syms) :& Field (Just 0) :& RNil
> coFLimaInsertSymIntuitive ( FocusedLima (Field syms :& Field (Just mai) :& RNil) ) s
> 	= FocusedLima
> 		$ Field (insertAt (1+mai) s syms)
> 		:& Field (Just $ (succBoundedBy . (1+) $ length syms) mai) :& RNil

> coFLimaDeleteSymIntuitive state@( FocusedLima (_ :& Field Nothing :& RNil) )
> 	= state
> coFLimaDeleteSymIntuitive ( FocusedLima (Field syms :& Field (Just mai) :& RNil) )
> 	= let
> 		mami' = case (compare mai 0) of
> 			GT -> Just (predAsNat mai)
> 			LT -> error "Main focus index was negative."
> 			EQ -> Nothing
> 	in FocusedLima $ Field (mami' `seq` deleteAt mai syms) :& Field mami' :& RNil

> coBFLimaInsertSymIntuitive :: BifocusedLima sym -> ( sym -> BifocusedLima sym )
> coBFLimaDeleteSymIntuitive :: BifocusedLima sym -> BifocusedLima sym

> coBFLimaInsertSymIntuitive
> 	( BifocusedLima rs@(Field syms :& Field mami :& pkmiF :& RNil) ) s
> 	= overBFLimaAsFLima (flip coFLimaInsertSymIntuitive s)
> 	$ BifocusedLima $ rput ((fieldMap . fmap) (pkmiT mami) pkmiF) rs
> 	where
> 		pkmiT Nothing x = ($x) $ succBoundedBy . (1+) $ length syms
> 		pkmiT (Just mai) x = if (mai > x) then x else pkmiT Nothing x

> coBFLimaDeleteSymIntuitive state@( BifocusedLima (_ :& Field Nothing :& _) )
> 	= state
> coBFLimaDeleteSymIntuitive
> 	( BifocusedLima rs@(_ :& Field (Just mai) :& pkmiF :& RNil) )
> 	= overBFLimaAsFLima coFLimaDeleteSymIntuitive
> 	$ BifocusedLima $ rput ((fieldMap . (=<<)) pkmiT pkmiF) rs
> 	where
> 		pkmiT x = case (compare x mai) of
> 			GT -> Just (predAsNat x)
> 			LT -> Just x
> 			EQ -> Nothing

> coSelLimaInsertSymIntuitive :: SelectingLima sym -> ( sym -> SelectingLima sym )
> coSelLimaDeleteSymIntuitive :: SelectingLima sym -> SelectingLima sym

> coSelLimaInsertSymIntuitive
> 	( SelectingLima rs@(Field syms :& Field mami :& pkmiF :& RNil) ) s
> 	= overSelLimaAsFLima (flip coFLimaInsertSymIntuitive s)
> 	$ SelectingLima $ rput ((fieldMap . fmap) (pkmiT mami) pkmiF) rs
> 	where
> 		pkmiT Nothing x = ($x) $ succBoundedBy . (1+) $ length syms
> 		pkmiT (Just mai) x = if (mai > x) then x else pkmiT Nothing x

> coSelLimaDeleteSymIntuitive state@( SelectingLima (_ :& Field Nothing :& _) )
> 	= state
> coSelLimaDeleteSymIntuitive
> 	( SelectingLima rs@(_ :& Field (Just mai) :& pkmiF :& RNil) )
> 	= overSelLimaAsFLima coFLimaDeleteSymIntuitive
> 	$ SelectingLima $ rput ((fieldMap . mapMaybe) pkmiT pkmiF) rs
> 	where
> 		pkmiT x = case (compare x mai) of
> 			GT -> Just (predAsNat x)
> 			LT -> Just x
> 			EQ -> Nothing

> coFLimaInsertSym :: FocusedLima sym -> ( sym -> ((), FocusedLima sym) )
> coFLimaDeleteSym :: FocusedLima sym -> ( () -> ((), FocusedLima sym) )

> coFLimaInsertSym = fmap ((),) . coFLimaInsertSymIntuitive
> coFLimaDeleteSym = const . ((),) . coFLimaDeleteSymIntuitive

> coBFLimaInsertSym :: BifocusedLima sym -> ( sym -> ((), BifocusedLima sym) )
> coBFLimaDeleteSym :: BifocusedLima sym -> ( () -> ((), BifocusedLima sym) )

> coBFLimaInsertSym = fmap ((),) . coBFLimaInsertSymIntuitive
> coBFLimaDeleteSym = const . ((),) . coBFLimaDeleteSymIntuitive

> coSelLimaInsertSym :: SelectingLima sym -> ( sym -> ((), SelectingLima sym) )
> coSelLimaDeleteSym :: SelectingLima sym -> ( () -> ((), SelectingLima sym) )

> coSelLimaInsertSym = fmap ((),) . coSelLimaInsertSymIntuitive
> coSelLimaDeleteSym = const . ((),) . coSelLimaDeleteSymIntuitive

> confFLimaListHdl :: FocusedLima sym -> BFLimaListHdl sym (FocusedLima sym)
> confFLimaListHdl a = BFLimaListHdl . Hdl
> 	$ liftCoBFLimaList (Proxy :: Proxy 'BFLimaInsertSym) coFLimaInsertSym a
> 	:& liftCoBFLimaList (Proxy :: Proxy 'BFLimaDeleteSym) coFLimaDeleteSym a
> 	:& RNil

> confBFLimaListHdl :: BifocusedLima sym -> BFLimaListHdl sym (BifocusedLima sym)
> confBFLimaListHdl a = BFLimaListHdl . Hdl
> 	$ liftCoBFLimaList (Proxy :: Proxy 'BFLimaInsertSym) coBFLimaInsertSym a
> 	:& liftCoBFLimaList (Proxy :: Proxy 'BFLimaDeleteSym) coBFLimaDeleteSym a
> 	:& RNil

> confSelLimaListHdl :: SelectingLima sym -> BFLimaListHdl sym (SelectingLima sym)
> confSelLimaListHdl a = BFLimaListHdl . Hdl
> 	$ liftCoBFLimaList (Proxy :: Proxy 'BFLimaInsertSym) coSelLimaInsertSym a
> 	:& liftCoBFLimaList (Proxy :: Proxy 'BFLimaDeleteSym) coSelLimaDeleteSym a
> 	:& RNil



> confSubrecLimaFocusHdl ::
> 	proxy s
> 	-> FieldRec '[ '("LimaSymTable", [sym]), '(s, Maybe Int) ]
> 	-> LimaFocusHdl sym ( FieldRec '[ '("LimaSymTable", [sym]), '(s, Maybe Int) ] )
> confSubrecLimaFocusHdl _ (Field syms :& Field mai :& RNil)
> 	= fmap (\(x,y) -> Field x :& Field y :& RNil) $ confLimaFocusHdl (syms, mai)

> confFLimaFocusHdl :: FocusedLima sym -> LimaFocusHdl sym (FocusedLima sym)
> confFLimaFocusHdl (FocusedLima rs) = fmap FocusedLima
> 	$ confSubrecLimaFocusHdl Proxy rs

> confBFLimaMainFocusHdl ::
> 	BifocusedLima sym -> LimaFocusHdl sym (BifocusedLima sym)
> confBFLimaMainFocusHdl (BifocusedLima rs) = fmap BifocusedLima
> 	$ rsubset (confSubrecLimaFocusHdl (Proxy :: Proxy "LimaFocusMain")) rs

> confBFLimaPickedFocusHdl ::
> 	BifocusedLima sym -> LimaFocusHdl sym (BifocusedLima sym)
> confBFLimaPickedFocusHdl (BifocusedLima rs) = fmap BifocusedLima
> 	$ rsubset (confSubrecLimaFocusHdl (Proxy :: Proxy "LimaFocusPicked")) rs

> confSelLimaFocusHdl ::
> 	SelectingLima sym -> LimaFocusHdl sym (SelectingLima sym)
> confSelLimaFocusHdl (SelectingLima rs) = fmap SelectingLima
> 	$ rsubset (confSubrecLimaFocusHdl (Proxy :: Proxy "LimaFocusMain")) rs



> confBFLimaHdl :: BifocusedLima sym -> BFLimaHdl sym (BifocusedLima sym)
> confBFLimaHdl bflima = BFLimaHdl
> 	(confBFLimaListHdl bflima)
> 	(confBFLimaMainFocusHdl bflima)
> 	(confBFLimaPickedFocusHdl bflima)



== Interpreters ==

* Type
* Default configuration

-----



> type BFLimaInterp a k = Cofree (BFLimaHdl a) k



> blankFLima :: FocusedLima sym
> blankFLima = FocusedLima $ Field [] :& Field Nothing :& RNil

> blankBFLima :: BifocusedLima sym
> blankBFLima = BifocusedLima $ Field [] :& Field Nothing :& Field Nothing :& RNil

> blankSelLima :: SelectingLima sym
> blankSelLima = SelectingLima $ Field [] :& Field Nothing :& Field [] :& RNil



> blankBFLimaInterp :: BFLimaInterp sym (BifocusedLima sym)
> blankBFLimaInterp = coiter confBFLimaHdl blankBFLima



== DSL expressions ==

* Reiterate that expressions are inhabitants of the free monad over the corecord
* Derive embedding of commands / atomic terms into programs / expressions

-----

Support:

Creates the lifts of atomic commands into expressions/programs.

The proxy here is to keep track of the term name for things that
eliminate it, which could be the `inTy` and `outTy` functors,
but generally aren't. It would be easier to call the appropriate
command by name if singletons were generated for the terms
and used instead of the proxies, since the generated singletons
would have the name of the term in them.

In most cases, one wants to use `liftPrgm'` instead of `liftPrgm`,
because we're typically writing the true input and output type functors
as type families, which must be wrapped in a newtype so they can be
partially applied. This requires construction & destruction to be
configured for before the programs look to have the right type.

> liftPrgm :: (term ∈ termsList)
> 	=> proxy term
> 	-> inTy term a
> 	-> Free (Cmd termsList inTy outTy a) (outTy term a)
> liftPrgm _ v = liftF $ Cmd (CoRec (IYform (v, id)))

Applied to a proxy, constructor, and destructor corresponding to wrapped
input/output types, creates the unwrapped command (see `liftPrgm`).

> liftPrgm' :: (term ∈ termsList)
> 	=> (i -> inTy' term a)
> 	-> (outTy' term a -> o)
> 	-> proxy term
> 	-> i
> 	-> Free (Cmd termsList inTy' outTy' a) o
> liftPrgm' to from p = fmap from . liftPrgm p . to

I badly want the proxy's type to become its value.
But it's copy & paste, which will have to be good enough.

-----



> type LimaSymPrgm a k = Free (LimaSymCmd a) k

> type LimaIndPrgm a k = Free (LimaIndCmd a) k

> type LimaFocusPrgm a k = Free (LimaFocusCmd a) k

> type BFLimaListPrgm a k = Free (BFLimaListCmd a) k

> type BFLimaPrgm a k = Free (BFLimaCmd a) k



> liftedLimaSymCmd :: (term ∈ LimaSymTerms)
> 	=> proxy term
> 	-> LimaSym_InTy term a
> 	-> LimaSymPrgm a (LimaSym_OutTy term a)
> liftedLimaSymCmd = (hoistFree LimaSymCmd .)
> 	. liftPrgm' LimaSym_InTy' (\(LimaSym_OutTy' x) -> x)

Entering in things of this form will let us query GHC for its type to replace in:

< limaSetSym :: LimaSym_InTy 'LimaSetSym a -> LimaSymPrgm a (LimaSym_OutTy 'LimaSetSym a)
< limaSetSym = liftedLimaSymCmd (Proxy :: Proxy 'LimaSetSym)

> limaSetSym :: a -> LimaSymPrgm a ()
> limaSetSym = liftedLimaSymCmd (Proxy :: Proxy 'LimaSetSym)

> limaGetSym :: () -> LimaSymPrgm a (Maybe a)
> limaGetSym = liftedLimaSymCmd (Proxy :: Proxy 'LimaGetSym)



> liftedLimaIndCmd :: (term ∈ LimaIndTerms)
> 	=> proxy term
> 	-> LimaInd_InTy term a
> 	-> LimaIndPrgm a (LimaInd_OutTy term a)
> liftedLimaIndCmd = (hoistFree LimaIndCmd .)
> 	. liftPrgm' LimaInd_InTy' (\(LimaInd_OutTy' x) -> x)

< limaterm :: LimaInd_InTy 'Limaterm a -> LimaIndPrgm a (LimaInd_OutTy 'Limaterm a)
< limaterm = liftedLimaIndCmd (Proxy :: Proxy 'Limaterm)

< limaGetFocusInd :: LimaInd_InTy 'LimaGetFocusInd a -> LimaIndPrgm a (LimaInd_OutTy 'LimaGetFocusInd a)
< limaGetFocusInd = liftedLimaIndCmd (Proxy :: Proxy 'LimaGetFocusInd)

> limaGetFocusInd :: () -> LimaIndPrgm a (Maybe Int)
> limaGetFocusInd = liftedLimaIndCmd (Proxy :: Proxy 'LimaGetFocusInd)

> limaRefocusInd :: Maybe Int -> LimaIndPrgm a ()
> limaRefocusInd = liftedLimaIndCmd (Proxy :: Proxy 'LimaRefocusInd)

> limaTrashFocus :: () -> LimaIndPrgm a ()
> limaTrashFocus = liftedLimaIndCmd (Proxy :: Proxy 'LimaTrashFocus)

> limaRefocusNext :: () -> LimaIndPrgm a ()
> limaRefocusNext = liftedLimaIndCmd (Proxy :: Proxy 'LimaRefocusNext)

> limaRefocusPrev :: () -> LimaIndPrgm a ()
> limaRefocusPrev = liftedLimaIndCmd (Proxy :: Proxy 'LimaRefocusPrev)



focus program sections for constituent sublanguages

> limaFocusSymPrgm :: LimaSymPrgm a k -> LimaFocusPrgm a k
> limaFocusSymPrgm = hoistFree $ LimaFocusSymCmd

> limaFocusIndPrgm :: LimaIndPrgm a k -> LimaFocusPrgm a k
> limaFocusIndPrgm = hoistFree $ LimaFocusIndCmd



> liftedBFLimaListCmd :: (term ∈ BFLimaListTerms)
> 	=> proxy term
> 	-> BFLimaList_InTy term a
> 	-> BFLimaListPrgm a (BFLimaList_OutTy term a)
> liftedBFLimaListCmd = (hoistFree BFLimaListCmd .)
> 	. liftPrgm' BFLimaList_InTy' (\(BFLimaList_OutTy' x) -> x)

< bflimaterm :: BFLimaList_InTy 'BFLimaterm a -> BFLimaListPrgm a (BFLimaList_OutTy 'BFLimaterm a)
< bflimaterm = liftedBFLimaListCmd (Proxy :: Proxy 'BFLimaterm)

< bflimaInsertSym :: BFLimaList_InTy 'BFLimaInsertSym a -> BFLimaListPrgm a (BFLimaList_OutTy 'BFLimaInsertSym a)
< bflimaInsertSym = liftedBFLimaListCmd (Proxy :: Proxy 'BFLimaInsertSym)

> bflimaInsertSym :: a -> BFLimaListPrgm a ()
> bflimaInsertSym = liftedBFLimaListCmd (Proxy :: Proxy 'BFLimaInsertSym)

> bflimaDeleteSym :: () -> BFLimaListPrgm a ()
> bflimaDeleteSym = liftedBFLimaListCmd (Proxy :: Proxy 'BFLimaDeleteSym)



bifocused list machine program sections for constituent sublanguages

> bflimaListPartPrgm :: BFLimaListPrgm a k -> BFLimaPrgm a k
> bflimaListPartPrgm = hoistFree $ BFLimaListPartCmd

> bflimaMainFocusPrgm :: LimaFocusPrgm a k -> BFLimaPrgm a k
> bflimaMainFocusPrgm = hoistFree $ BFLimaMainFocusCmd

> bflimaPickedFocusPrgm :: LimaFocusPrgm a k -> BFLimaPrgm a k
> bflimaPickedFocusPrgm = hoistFree $ BFLimaPickedFocusCmd



and the shortcuts

> bflimaMainFocusSymPrgm :: LimaSymPrgm a k -> BFLimaPrgm a k
> bflimaMainFocusSymPrgm = hoistFree
> 	$ BFLimaMainFocusCmd . LimaFocusSymCmd

> bflimaMainFocusIndPrgm :: LimaIndPrgm a k -> BFLimaPrgm a k
> bflimaMainFocusIndPrgm = hoistFree
> 	$ BFLimaMainFocusCmd . LimaFocusIndCmd

> bflimaPickedFocusSymPrgm :: LimaSymPrgm a k -> BFLimaPrgm a k
> bflimaPickedFocusSymPrgm = hoistFree
> 	$ BFLimaPickedFocusCmd . LimaFocusSymCmd

> bflimaPickedFocusIndPrgm :: LimaIndPrgm a k -> BFLimaPrgm a k
> bflimaPickedFocusIndPrgm = hoistFree
> 	$ BFLimaPickedFocusCmd . LimaFocusIndCmd



=== Early attempt to make a derivation of the strings for the boilerplate lifts
of atomic commands into program space ===

We can't derive these expressions until dependent haskell exists, because
it constitutes a `(term :: termTy) -> f term`. Generating singletons
is the closest thing.

Please don't leave your atoms without type signatures, that just means the
language is undocumented.

> liftAtomString ::
> 	String {- Input type functor -}
> 	-> String {- Output type functor -}
> 	-> String {- Program type name -}
> 	-> String {- Specialization of liftPrgm' -}
> 	-> (String, String) {- (Term title, name of its lift) -}
> 	-> String
> liftAtomString inTFName outTFName prgmTyName specialLiftName (termName, liftName)
> 	= unlines $
> 		[ liftName ++ " :: " ++ inTFName ++ " '" ++ termName ++ " a -> " ++ prgmTyName ++ " a (" ++ outTFName ++ " '" ++ termName ++" a)"
> 		, liftName ++ " = " ++ specialLiftName ++ " (Proxy :: Proxy '" ++ termName ++ ")" ]



== Pairings between programs and states ==

* Examples
* Extended program inventory

-----



Support

> stepDSLState :: (CmdsHandlersPair f g, Functor g)
> 	=> (stateTy -> g stateTy)
> 	-> Free f k
> 	-> stateTy -> stateTy
> stepDSLState f = flip $ pair const . coiter f

> stepPrgmState ::
> 	(stateTy -> Hdl termList inTy outTy a stateTy)
> 	-> Prgm termList inTy outTy a k
> 	-> stateTy -> stateTy
> stepPrgmState = stepDSLState



> debugOutputAndState :: (Show a, Show b) => a -> b -> IO ()
> debugOutputAndState a b =
> 	print (take 44 $ repeat '-')
> 	>> print "Program/expression output:"
> 	>> print b
> 	>> print "Interpreted state:"
> 	>> print a
> 	>> print (take 44 $ repeat '-')

> debugInterpDSL :: (Show stateTy, Show k, CmdsHandlersPair f g, Functor g)
> 	=> Cofree g stateTy {- Initial interpreter state -}
> 	-> Free f k {- Program to debug -}
> 	-> IO ()
> debugInterpDSL = pair debugOutputAndState

-----



> stepBFLima :: BFLimaPrgm sym a -> BifocusedLima sym -> BifocusedLima sym
> stepBFLima = stepDSLState confBFLimaHdl

> debugBFLimaPrgm :: forall sym a. (Show sym, Show a)
> 	=> BFLimaPrgm sym a -> IO ()
> debugBFLimaPrgm = debugInterpDSL
> 	(blankBFLimaInterp :: BFLimaInterp sym (BifocusedLima sym))



There. Like magic:

< debugBFLimaPrgm $ (bflimaListPartPrgm . bflimaInsertSym) 'a'
"--------------------------------------------"
"Program/expression output:"
()
"Interpreted state:"
BifocusedLima {LimaSymTable :-> "a", LimaFocusMain :-> Just 0, LimaFocusPicked :-> Nothing}
"--------------------------------------------"

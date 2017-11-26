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

> import Data.Functor.Pairing hiding (pair, pairCH)
> import qualified Data.Functor.Pairing as Pairing (pair, pairCH)

In here, we use corecords for the programs, and records for the interpreters.

> import Data.Vinyl
> import Data.Vinyl.CoRec
> import Data.Vinyl.Functor
> import Data.Proxy
> import Data.Functor.Product

Notation

> import Control.Arrow ((&&&))



== Orientation ==

* Transpose: Inventory analogy

* Cofree for interpreters, free for DSLs (Liang)
** Divides goals well
* Sum and product types w/ same labels of factors ~ Corecords and records
** Expresses divisions in implementation well and nimble code derivation

* Transpose: GUI projections



== Machines ==

* Focused, bifocused, field lists, record types
* Benefits of trying to implement a couple actions directly before proceeding
** Exercizes with holes



=== Bounding indices ===

* Library



=== Setting, inserting, & deleting on the symbol table ===

* Library, specs



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



< type Pairing f g = forall a b c. (a -> b -> c) -> g a -> f b -> c

"zapWithAdjunction" in reverse

> zWA :: (a -> b -> c) -> (x, a) -> (x -> b) -> c
> zWA fn (x,a) xfnToB = fn a (xfnToB x)

> pairCH :: Pairing (Cmd xs inTy outTy a) (Hdl xs inTy outTy a)
> pairCH fn (Hdl h) (Cmd (CoRec (IYform (i, kfn))))
> 	= case rget Proxy h of ROform g -> (pRL . pLR) fn g (i, kfn)
> 	where
> 		pLR = zWA
> 		pRL = flip . pLR . flip

Hahahahaha that was so easy.
Credit to (Data.Vinyl.CoRec.match).



> class CanonicalPairing f g where
> 	pairCan :: Pairing f g

> instance CanonicalPairing (Cmd xs inTy outTy a) (Hdl xs inTy outTy a)
> 	where pairCan = pairCH

> pair :: (CanonicalPairing f g) => Pairing (Free f) (Cofree g)
> pair p (a :< _) (Pure x) = p a x
> pair p (_ :< gCga) (Free fFfx) = pairCan (pair p) gCga fFfx

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

> type family LimaSym_InTy (t :: LimaSymTerm) :: * -> * where
> 	LimaSym_InTy 'LimaSetSym = Identity
> 	LimaSym_InTy 'LimaGetSym = Const ()

> type family LimaSym_OutTy (t :: LimaSymTerm) :: * -> * where
> 	LimaSym_OutTy 'LimaSetSym = Const ()
> 	LimaSym_OutTy 'LimaGetSym = Maybe

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

> type family LimaInd_InTy (t :: LimaIndTerm) :: * -> * where
> 	LimaInd_InTy 'LimaGetFocusInd = Const ()
> 	LimaInd_InTy 'LimaRefocusInd = Const (Maybe Int)
> 	LimaInd_InTy 'LimaTrashFocus = Const ()
> 	LimaInd_InTy 'LimaRefocusNext = Const ()
> 	LimaInd_InTy 'LimaRefocusPrev = Const ()

> type family LimaInd_OutTy (t :: LimaIndTerm) :: * -> * where
> 	LimaInd_OutTy 'LimaGetFocusInd = Const (Maybe Int)
> 	LimaInd_OutTy 'LimaRefocusInd = Const ()
> 	LimaInd_OutTy 'LimaTrashFocus = Const ()
> 	LimaInd_OutTy 'LimaRefocusNext = Const ()
> 	LimaInd_OutTy 'LimaRefocusPrev = Const ()

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

> type family BFLimaList_InTy (t :: BFLimaListTerm) :: * -> * where
> 	BFLimaList_InTy 'BFLimaInsertSym = Identity
> 	BFLimaList_InTy 'BFLimaDeleteSym = Const ()

> type family BFLimaList_OutTy (t :: BFLimaListTerm) :: * -> * where
> 	BFLimaList_OutTy 'BFLimaInsertSym = Const ()
> 	BFLimaList_OutTy 'BFLimaDeleteSym = Const ()

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

> data LimaFocusHdl a k =
> 	LimaFocusIndHdl (LimaIndHdl a k)
> 	| LimaFocusSymHdl (LimaSymHdl a k)
>	deriving (Functor)



> newtype BFLimaListHdl a k
> 	= BFLimaListHdl (Hdl BFLimaListTerms BFLimaList_InTy' BFLimaList_OutTy' a k)
> 	deriving (Functor)

> data BFLimaHdl a k =
> 	BFLimaListPartHdl (BFLimaListHdl a k)
> 	| BFLimaMainFocusHdl (LimaFocusHdl a k)
> 	| BFLimaPickedFocusHdl (LimaFocusHdl a k)
> 	deriving (Functor)



=== Handler type by solving for duality with commands type ===

* Derive, explain, replace derivation of handler type train of thought
& cmd-handlers pairing train of thought



=== Configurations ===

* Explanation
* Library - functions
* Library - operations
* Library - handler configurations



== Interpreters ==

* Type
* Default configuration



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

> limaSetSym :: Identity a -> LimaSymPrgm a (Const () a)
> limaSetSym = liftedLimaSymCmd (Proxy :: Proxy 'LimaSetSym)

> limaGetSym :: Const () a -> LimaSymPrgm a (Maybe a)
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

> limaGetFocusInd :: Const () a -> LimaIndPrgm a (Const (Maybe Int) a)
> limaGetFocusInd = liftedLimaIndCmd (Proxy :: Proxy 'LimaGetFocusInd)

> limaRefocusInd :: Const (Maybe Int) a -> LimaIndPrgm a (Const () a)
> limaRefocusInd = liftedLimaIndCmd (Proxy :: Proxy 'LimaRefocusInd)

> limaTrashFocus :: Const () a -> LimaIndPrgm a (Const () a)
> limaTrashFocus = liftedLimaIndCmd (Proxy :: Proxy 'LimaTrashFocus)

> limaRefocusNext :: Const () a -> LimaIndPrgm a (Const () a)
> limaRefocusNext = liftedLimaIndCmd (Proxy :: Proxy 'LimaRefocusNext)

> limaRefocusPrev :: Const () a -> LimaIndPrgm a (Const () a)
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

> bflimaInsertSym :: Identity a -> BFLimaListPrgm a (Const () a)
> bflimaInsertSym = liftedBFLimaListCmd (Proxy :: Proxy 'BFLimaInsertSym)

> bflimaDeleteSym :: Const () a -> BFLimaListPrgm a (Const () a)
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



== Pairings between outputs and states ==

* Library
* Examples



== Pairings between programs and states ==

* Library
* Examples
* Extended program inventory

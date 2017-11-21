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



> type Pairing f g = forall a b c. (a -> b -> c) -> g a -> f b -> c

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



> data LimaTermOverSym = LimaSetSym | LimaGetSym

> type LimaTermsOverSym = ['LimaSetSym, 'LimaGetSym]

> type family LimaTermOverSym_InTy (t :: LimaTermOverSym) :: * -> * where
> 	LimaTermOverSym_InTy 'LimaSetSym = Identity
> 	LimaTermOverSym_InTy 'LimaGetSym = Const ()

> type family LimaTermOverSym_OutTy (t :: LimaTermOverSym) :: * -> * where
> 	LimaTermOverSym_OutTy 'LimaSetSym = Const ()
> 	LimaTermOverSym_OutTy 'LimaGetSym = Maybe

We need both pattern matching and partial application.
Type families can't be partially applied.

> newtype LimaTermOverSym_InTy' f a
> 	= LimaTermOverSym_InTy' (LimaTermOverSym_InTy f a)

> newtype LimaTermOverSym_OutTy' f a
> 	= LimaTermOverSym_OutTy' (LimaTermOverSym_OutTy f a)



> data LimaTermOverFocus =
> 	LimaGetFocusInd
> 	| LimaRefocusInd
> 	| LimaTrashFocus
> 	| LimaRefocusNext
> 	| LimaRefocusPrev
> 	| LimaFocusSymCmd LimaTermOverSym

> type LimaTermsOverFocus =
> 	[ 'LimaGetFocusInd
> 	, 'LimaRefocusInd
> 	, 'LimaTrashFocus
> 	, 'LimaRefocusNext
> 	, (forall (limaTermOverSym :: LimaTermOverSym).
> 		'LimaFocusSymCmd limaTermOverSym)]

> type family LimaTermOverFocus_InTy (t :: LimaTermOverFocus) :: * -> * where
> 	LimaTermOverFocus_InTy 'LimaGetFocusInd = Const ()
> 	LimaTermOverFocus_InTy 'LimaRefocusInd = Const (Maybe Int)
> 	LimaTermOverFocus_InTy 'LimaTrashFocus = Const ()
> 	LimaTermOverFocus_InTy 'LimaRefocusNext = Const ()
> 	LimaTermOverFocus_InTy 'LimaRefocusPrev = Const ()
> 	LimaTermOverFocus_InTy ('LimaFocusSymCmd limaTermOverSym)
> 		= LimaTermOverSym_InTy limaTermOverSym

> type family LimaTermOverFocus_OutTy (t :: LimaTermOverFocus) :: * -> * where
> 	LimaTermOverFocus_OutTy 'LimaGetFocusInd = Const (Maybe Int)
> 	LimaTermOverFocus_OutTy 'LimaRefocusInd = Const ()
> 	LimaTermOverFocus_OutTy 'LimaTrashFocus = Const ()
> 	LimaTermOverFocus_OutTy 'LimaRefocusNext = Const ()
> 	LimaTermOverFocus_OutTy 'LimaRefocusPrev = Const ()
> 	LimaTermOverFocus_OutTy ('LimaFocusSymCmd limaTermOverSym)
> 		= LimaTermOverSym_OutTy limaTermOverSym

> newtype LimaTermOverFocus_InTy' f a
> 	= LimaTermOverFocus_InTy' (LimaTermOverFocus_InTy f a)

> newtype LimaTermOverFocus_OutTy' f a
> 	= LimaTermOverFocus_OutTy' (LimaTermOverFocus_OutTy f a)



> data BFLimaTerm =
> 	BFLimaInsertSym
> 	| BFLimaDeleteSym
> 	| BFLimaMainFocusCmd LimaTermOverFocus
> 	| BFLimaPickedFocusCmd LimaTermOverFocus

> type BFLimaTerms =
> 	[ 'BFLimaInsertSym
> 	, 'BFLimaDeleteSym
> 	, (forall (limaTermOverFocus :: LimaTermOverFocus).
> 		'BFLimaMainFocusCmd limaTermOverFocus)
> 	, (forall (limaTermOverFocus :: LimaTermOverFocus).
> 		'BFLimaPickedFocusCmd limaTermOverFocus)]

> type family BFLimaTerm_InTy (t :: BFLimaTerm) :: * -> * where
> 	BFLimaTerm_InTy 'BFLimaInsertSym = Identity
> 	BFLimaTerm_InTy 'BFLimaDeleteSym = Const ()
> 	BFLimaTerm_InTy ('BFLimaMainFocusCmd limaTermOverFocus)
> 		= LimaTermOverFocus_InTy limaTermOverFocus
> 	BFLimaTerm_InTy ('BFLimaPickedFocusCmd limaTermOverFocus)
> 		= LimaTermOverFocus_InTy limaTermOverFocus

> type family BFLimaTerm_OutTy (t :: BFLimaTerm) :: * -> * where
> 	BFLimaTerm_OutTy 'BFLimaInsertSym = Const ()
> 	BFLimaTerm_OutTy 'BFLimaDeleteSym = Const ()
> 	BFLimaTerm_OutTy ('BFLimaMainFocusCmd limaTermOverFocus)
> 		= LimaTermOverFocus_OutTy limaTermOverFocus
> 	BFLimaTerm_OutTy ('BFLimaPickedFocusCmd limaTermOverFocus)
> 		= LimaTermOverFocus_OutTy limaTermOverFocus

> newtype BFLimaTerm_InTy' f a
> 	= BFLimaTerm_InTy' (BFLimaTerm_InTy f a)

> newtype BFLimaTerm_OutTy' f a
> 	= BFLimaTerm_OutTy' (BFLimaTerm_OutTy f a)



> type LimaTermOverSym_Client a k
> 	= Cmd LimaTermsOverSym
> 		LimaTermOverSym_InTy' LimaTermOverSym_OutTy'
> 		a k

> type LimaTermOverFocus_Client a k
> 	= Cmd LimaTermsOverFocus
> 		LimaTermOverFocus_InTy' LimaTermOverFocus_OutTy'
> 		a k

> type BFLimaTerm_Client a k
> 	= Cmd BFLimaTerms
> 		BFLimaTerm_InTy' BFLimaTerm_OutTy'
> 		a k



== DSL commands ==

* Everything



== Handlers ==

* Compare ontologies ((commands -> operations) by reaction policies,
	implementations, cocommands, coatoms)



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



== Pairings between outputs and states ==

* Library
* Examples



== Pairings between programs and states ==

* Library
* Examples
* Extended program inventory

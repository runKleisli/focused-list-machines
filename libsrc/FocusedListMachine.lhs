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



> data LimaSymTerm = LimaSetSym | LimaGetSym

> type LimaSymTerms = ['LimaSetSym, 'LimaGetSym]

> type family LimaSym_InTy (t :: LimaSymTerm) :: * -> * where
> 	LimaSym_InTy 'LimaSetSym = Identity
> 	LimaSym_InTy 'LimaGetSym = Const ()

> type family LimaSym_OutTy (t :: LimaSymTerm) :: * -> * where
> 	LimaSym_OutTy 'LimaSetSym = Const ()
> 	LimaSym_OutTy 'LimaGetSym = Maybe

We need both pattern matching and partial application.
Type families can't be partially applied.

> newtype LimaSym_InTy' f a
> 	= LimaSym_InTy' (LimaSym_InTy f a)

> newtype LimaSym_OutTy' f a
> 	= LimaSym_OutTy' (LimaSym_OutTy f a)



> data LimaFocusTerm =
> 	LimaGetFocusInd
> 	| LimaRefocusInd
> 	| LimaTrashFocus
> 	| LimaRefocusNext
> 	| LimaRefocusPrev
> 	| LimaFocusSymCmd LimaSymTerm

> type LimaFocusTerms =
> 	[ 'LimaGetFocusInd
> 	, 'LimaRefocusInd
> 	, 'LimaTrashFocus
> 	, 'LimaRefocusNext
> 	, (forall (limaSymTerm :: LimaSymTerm).
> 		'LimaFocusSymCmd limaSymTerm)]

> type family LimaFocus_InTy (t :: LimaFocusTerm) :: * -> * where
> 	LimaFocus_InTy 'LimaGetFocusInd = Const ()
> 	LimaFocus_InTy 'LimaRefocusInd = Const (Maybe Int)
> 	LimaFocus_InTy 'LimaTrashFocus = Const ()
> 	LimaFocus_InTy 'LimaRefocusNext = Const ()
> 	LimaFocus_InTy 'LimaRefocusPrev = Const ()
> 	LimaFocus_InTy ('LimaFocusSymCmd limaSymTerm)
> 		= LimaSym_InTy limaSymTerm

> type family LimaFocus_OutTy (t :: LimaFocusTerm) :: * -> * where
> 	LimaFocus_OutTy 'LimaGetFocusInd = Const (Maybe Int)
> 	LimaFocus_OutTy 'LimaRefocusInd = Const ()
> 	LimaFocus_OutTy 'LimaTrashFocus = Const ()
> 	LimaFocus_OutTy 'LimaRefocusNext = Const ()
> 	LimaFocus_OutTy 'LimaRefocusPrev = Const ()
> 	LimaFocus_OutTy ('LimaFocusSymCmd limaSymTerm)
> 		= LimaSym_OutTy limaSymTerm

> newtype LimaFocus_InTy' f a
> 	= LimaFocus_InTy' (LimaFocus_InTy f a)

> newtype LimaFocus_OutTy' f a
> 	= LimaFocus_OutTy' (LimaFocus_OutTy f a)



> data BFLimaTerm =
> 	BFLimaInsertSym
> 	| BFLimaDeleteSym
> 	| BFLimaMainFocusCmd LimaFocusTerm
> 	| BFLimaPickedFocusCmd LimaFocusTerm

> type BFLimaTerms =
> 	[ 'BFLimaInsertSym
> 	, 'BFLimaDeleteSym
> 	, (forall (limaFocusTerm :: LimaFocusTerm).
> 		'BFLimaMainFocusCmd limaFocusTerm)
> 	, (forall (limaFocusTerm :: LimaFocusTerm).
> 		'BFLimaPickedFocusCmd limaFocusTerm)]

> type family BFLima_InTy (t :: BFLimaTerm) :: * -> * where
> 	BFLima_InTy 'BFLimaInsertSym = Identity
> 	BFLima_InTy 'BFLimaDeleteSym = Const ()
> 	BFLima_InTy ('BFLimaMainFocusCmd limaFocusTerm)
> 		= LimaFocus_InTy limaFocusTerm
> 	BFLima_InTy ('BFLimaPickedFocusCmd limaFocusTerm)
> 		= LimaFocus_InTy limaFocusTerm

> type family BFLima_OutTy (t :: BFLimaTerm) :: * -> * where
> 	BFLima_OutTy 'BFLimaInsertSym = Const ()
> 	BFLima_OutTy 'BFLimaDeleteSym = Const ()
> 	BFLima_OutTy ('BFLimaMainFocusCmd limaFocusTerm)
> 		= LimaFocus_OutTy limaFocusTerm
> 	BFLima_OutTy ('BFLimaPickedFocusCmd limaFocusTerm)
> 		= LimaFocus_OutTy limaFocusTerm

> newtype BFLima_InTy' f a
> 	= BFLima_InTy' (BFLima_InTy f a)

> newtype BFLima_OutTy' f a
> 	= BFLima_OutTy' (BFLima_OutTy f a)



== DSL commands ==

* Everything

-----



> type LimaSymCmd a k
> 	= Cmd LimaSymTerms
> 		LimaSym_InTy' LimaSym_OutTy'
> 		a k

> type LimaFocusCmd a k
> 	= Cmd LimaFocusTerms
> 		LimaFocus_InTy' LimaFocus_OutTy'
> 		a k

> type BFLimaCmd a k
> 	= Cmd BFLimaTerms
> 		BFLima_InTy' BFLima_OutTy'
> 		a k



== Handlers ==

* Compare ontologies ((commands -> operations) by reaction policies,
	implementations, cocommands, coatoms)

-----



> type LimaSymHdl a k = Hdl LimaSymTerms LimaSym_InTy' LimaSym_OutTy' a k

> type LimaFocusHdl a k = Hdl LimaFocusTerms LimaFocus_InTy' LimaFocus_OutTy' a k

> type BFLimaHdl a k = Hdl BFLimaTerms BFLima_InTy' BFLima_OutTy' a k



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



> -- | Equal to `Free (LimaSymCmd a) k`
> type LimaSymPrgm a k = Free (Cmd LimaSymTerms LimaSym_InTy' LimaSym_OutTy' a) k

> -- | Equal to `Free (LimaFocusCmd a) k`
> type LimaFocusPrgm a k = Free (Cmd LimaFocusTerms LimaFocus_InTy' LimaFocus_OutTy' a) k

> -- | Equal to `Free (BFLimaCmd a) k`
> type BFLimaPrgm a k = Free (Cmd BFLimaTerms BFLima_InTy' BFLima_OutTy' a) k



> liftedBFLimaTerm :: (term ∈ BFLimaTerms)
> 	=> proxy term
> 	-> BFLima_InTy term a
> 	-> BFLimaPrgm a (BFLima_OutTy term a)
> liftedBFLimaTerm = liftPrgm' BFLima_InTy' (\(BFLima_OutTy' x) -> x)

> bflimaInsertSym :: Identity a -> BFLimaPrgm a (Const () a)
> bflimaInsertSym = liftedBFLimaTerm (Proxy :: Proxy 'BFLimaInsertSym)

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

> liftAtomStringBFLima :: (String, String) {- (Term title, name of its lift) -} -> IO ()
> liftAtomStringBFLima = putStrLn . liftAtomString "BFLima_InTy" "BFLima_OutTy" "BFLimaPrgm" "liftedBFLimaTerm"

> liftAtomStringBFLima' :: String -> IO ()
> liftAtomStringBFLima' (_:_:_:xs) = liftAtomStringBFLima ("BFL"++xs, "bfl"++xs)
> liftAtomStringBFLima' _ = error "String not long enough to be a term name."

> liftedAtomStringsBFLima :: IO ()
> liftedAtomStringsBFLima = mapM_ liftAtomStringBFLima'
> 	$ ["BFLimaInsertSym", "BFLimaDeleteSym",
> 	"BFLimaMainFocusCmd", -- ignore this one
> 	"BFLimaPickedFocusCmd"] -- ignore this one

> bflimaDeleteSym :: BFLima_InTy 'BFLimaDeleteSym a
> 	-> BFLimaPrgm a (BFLima_OutTy 'BFLimaDeleteSym a)
> bflimaDeleteSym = liftedBFLimaTerm (Proxy :: Proxy 'BFLimaDeleteSym)

Oh whoops! We can't make these parametricly, haha!

When you try & use (:: x) to type something based on a variable (x), it
actually treats them as different variables!
In this case, it quite luckily gives us an ambiguous types error.

< bflimaMainFocusCmd limaFocusTerm = liftedBFLimaTerm (Proxy :: Proxy ('BFLimaMainFocusCmd limaFocusTerm))

< bflimaPickedFocusCmd limaFocusTerm = liftedBFLimaTerm (Proxy :: Proxy ('BFLimaPickedFocusCmd limaFocusTerm))

Okay. But.. now we're stuck, cause we can't use `hoistFree` on a constructor
to take lifts of recursive sublanguage commands into their free monad and
transform them into the corresponding programs over the parent language.

There is in fact no transformation from commands in the recursive sublanguage
to commands in the parent language, without such a constructor, because
such a transformation would need to be able to compare the values of
the co/sheaf on the preimage and image of the section and verify that
they are in fact equal. The only thing identifying the terms is the
section. Comparing the values of the functor defining what a command is
implies comparing the unpromoted form of sublanguage terms (arguments
to parent language terms) to the promoted form (arguments to the functor,
as elements of the type-level list of all promoted terms).

Thus there is nothing to `hoistFree` over recursive sublanguage programs
to convert them to programs in the parent language.



== Pairings between outputs and states ==

* Library
* Examples



== Pairings between programs and states ==

* Library
* Examples
* Extended program inventory

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
> 	, 'LimaRefocusNext ]

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



> data LimaFocusTerm =
> 	LimaFocusIndTerm
> 	| LimaFocusSymTerm

Approximately
< 	LimaFocusIndCmd LimaIndTerm
< 	LimaFocusSymCmd LimaSymTerm

> type LimaFocusTerms =
> 	[ 'LimaFocusIndTerm
> 	, 'LimaFocusSymTerm ]

> type family LimaFocus_CmdTy (t :: LimaFocusTerm) :: * -> * -> * where
> 	LimaFocus_CmdTy 'LimaFocusIndTerm = LimaIndCmd
> 	LimaFocus_CmdTy 'LimaFocusSymTerm = LimaSymCmd

> type family LimaFocus_HdlTy (t :: LimaFocusTerm) :: * -> * -> * where
> 	LimaFocus_HdlTy 'LimaFocusIndTerm = LimaIndHdl
> 	LimaFocus_HdlTy 'LimaFocusSymTerm = LimaSymHdl

> newtype LimaFocus_CmdTy' a k f
> 	= LimaFocus_CmdTy' (LimaFocus_CmdTy f a k)

> newtype LimaFocus_HdlTy' a k f
> 	= LimaFocus_HdlTy' (LimaFocus_HdlTy f a k)



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



> data BFLimaTerm =
> 	BFLimaListPartTerm
> 	| BFLimaMainFocusTerm
> 	| BFLimaPickedFocusTerm

> type BFLimaTerms =
> 	[ 'BFLimaListPartTerm
> 	, 'BFLimaMainFocusTerm
> 	, 'BFLimaPickedFocusTerm ]

> type family BFLima_CmdTy (t :: BFLimaTerm) :: * -> * -> * where
> 	BFLima_CmdTy 'BFLimaListPartTerm = BFLimaListCmd
> 	BFLima_CmdTy 'BFLimaMainFocusTerm = LimaFocusCmd
> 	BFLima_CmdTy 'BFLimaPickedFocusTerm = LimaFocusCmd

> type family BFLima_HdlTy (t :: BFLimaTerm) :: * -> * -> * where
> 	BFLima_HdlTy 'BFLimaListPartTerm = BFLimaListHdl
> 	BFLima_HdlTy 'BFLimaMainFocusTerm = LimaFocusHdl
> 	BFLima_HdlTy 'BFLimaPickedFocusTerm = LimaFocusHdl

> newtype BFLima_CmdTy' a k f
> 	= BFLima_CmdTy' (BFLima_CmdTy f a k)

> newtype BFLima_HdlTy' a k f
> 	= BFLima_HdlTy' (BFLima_HdlTy f a k)



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

> newtype LimaFocusCmd a k
> 	= LimaFocusCmd ( CoRec (LimaFocus_CmdTy' a k) LimaFocusTerms )



More about (CmdTy)s not being injective later...

< instance Functor (LimaFocusCmd a) where
< 	fmap f (LimaFocusCmd (CoRec (LimaFocus_CmdTy' x)))
< 		= LimaFocusCmd (CoRec (LimaFocus_CmdTy' (fmap f x)))

This almost works:

< instance Functor (LimaFocusCmd a) where
< 	fmap f (LimaFocusCmd x) = LimaFocusCmd (coRecMap (LimaFocus_CmdTy' . fmap f . (\(LimaFocus_CmdTy' y) -> y)) x)

... but it boils the missing piece down to inference of (Functor) for
`LimaFocus_CmdTy term a` for all `term :: LimaFocusTerm`.
Ultimately, we need a separate function for performing an `fmap`-like
`LimaFocus_CmdTy' _ _ _ -> LimaFocus_CmdTy' _ _ _` for the same reason
we need `iyMap` & `roMap` -- the last argument of the `LimaFocus_CmdTy'`
predicate is the term instead of the type being mapped over.

< limaFocusCmdTyMap ::
< 	( k -> k' )
< 	-> LimaFocus_CmdTy' a k l
< 	-> LimaFocus_CmdTy' a k' l

< limaFocusCmdTyMap f (LimaFocus_CmdTy' (x :: LimaIndCmd a k))
< 	= LimaFocus_CmdTy' $ fmap f x

Stuck term:

< limaFocusCmdTyMap f
< 	(LimaFocus_CmdTy' (x :: LimaFocus_CmdTy 'LimaFocusIndTerm a k))
< 	= LimaFocus_CmdTy' $ fmap f x

```
    • Couldn't match type ‘LimaFocus_CmdTy l’ with ‘LimaIndCmd’
      Expected type: LimaFocus_CmdTy l a k
        Actual type: LimaFocus_CmdTy 'LimaFocusIndTerm a k
    • When checking that the pattern signature:
          LimaFocus_CmdTy 'LimaFocusIndTerm a k
        fits the type of its context: LimaFocus_CmdTy l a k
      In the pattern: x :: LimaFocus_CmdTy  'LimaFocusIndTerm a k
      In the pattern:
        LimaFocus_CmdTy' (x :: LimaFocus_CmdTy  'LimaFocusIndTerm a k)
    • Relevant bindings include
        limaFocusCmdTyMap :: (k -> k')
                             -> LimaFocus_CmdTy' a k l -> LimaFocus_CmdTy' a k' l
          (bound at libsrc/FocusedListMachine.lhs:360:3)
    |
361 | >       (LimaFocus_CmdTy' (x :: LimaFocus_CmdTy 'LimaFocusIndTerm a k))
    |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

Simply can't restrict the constructor itself in the match:

< limaFocusCmdTyMap f
< 	((LimaFocus_CmdTy' :: LimaFocus_CmdTy 'LimaFocusIndTerm a k -> LimaFocus_CmdTy' a k 'LimaFocusIndTerm) x)
< 	= LimaFocus_CmdTy' $ fmap f x

So we try to restrict the full term matched instead of the inner term.
This should work because `LimaFocus_CmdTy' _ _ 'LimaFocusIndTerm`
types as a `'LimaFocusIndTerm _ _ (term :: LimaFocusTerm)` at the
syntactic level and doesn't reduce to a term which doesn't, while `x`
must then have a type that reduces to `LimaFocus_CmdTy 'LimaFocusIndTerm _ _`
as a consequence of inferring the type of the full term.

 (x :: LimaFocus_CmdTy 'LimaFocusIndTerm a k))
 
< limaFocusCmdTyMap f
< 	(LimaFocus_CmdTy' x :: LimaFocus_CmdTy' a k 'LimaFocusIndTerm)
< 	= LimaFocus_CmdTy' $ fmap f x

Nope! It doesn't want that either, it says `l` is a rigid type variable and
can't be matched with `'LimaFocusIndTerm`.

< unifyCmdTyAndIndCmd ::
< 	LimaIndCmd a k'
< 	-> LimaFocus_CmdTy 'LimaFocusIndTerm a k'
< unifyCmdTyAndIndCmd = id

Okay, one more time with an inner constructor:

< limaFocusCmdTyMap ::
< 	( k -> k' )
< 	-> LimaFocus_CmdTy' a k l
< 	-> LimaFocus_CmdTy' a k' l
< limaFocusCmdTyMap f (LimaFocus_CmdTy' (x@(LimaIndCmd x') :: LimaFocus_CmdTy 'LimaFocusIndTerm a k))
< 	= LimaFocus_CmdTy' $ fmap f x

Nope! Refuses to type `LimaIndCmd x'` as `LimaFocus_CmdTy l a k` because
it won't unify `l` with `'LimaFocusIndTerm` no matter what.

If we could `fmap` using a dictionary for a functor constraint on
`LimaFocus_CmdTy l a k` over all `l : LimaFocusTerm`,
we might could apply the CmdTy `fmap`s using that instead and
save having to unify `l` with any constant.

This requires `Constraint` be a kind... so, requires `-XConstraintKinds`.

< type family LimaFocus_CmdTy_Functor (term :: LimaFocusTerm) :: * -> Constraint
< 	where
< 		LimaFocus_CmdTy_Functor term a = Functor (LimaFocus_CmdTy term a)

< type LFTFunctorDict term a = Dict (LimaFocus_CmdTy_Functor term) a

...and so we might as well try and make our own version of `Dict` that takes
a `(* -> *) -> Constraint` instead of a `* -> Constraint`, namely `Functor`.

But at this point I doubt this approach completely.

	So it would seem that wrapping recursive sublanguage commands in
constructors implicitly requires dependent types to work when the parent
language commands are typed as values of a copresheaf on a term category.
	Without those constructors, using a constructor of a parent language *term*
from a recursive sublanguage term and automatically inheriting input and output
types, we arrive at a more elegant picture where the need for dependent types is
obvious from the need to promote the recursive sublanguage term used in such a
term-level constructor so it can be used as a parameter in the sublanguage's input
and output types (_InTy, _OutTy).
	Note that the introduction of some of the
newtypes here is in response to not being able to implement some `liftPrgm'`
derivations without having functor instances. `liftPrgm'` derivations are where
the approach with term-level nesting of the recursive sublanguages fails &
demonstrates that requirement on dependent functions for promotion.
	Without being able to make commands `LimaFocusCmd a k` in the parent
language `LimaFocusTerm` a functor, we can't apply `hoistFree` to the section of
the recursive sublanguage's commands into the parent language's commands
to derive programs in the parent language from programs in the sublanguage:

```hoistFree :: Functor g => (forall a. f a -> g a) -> Free f b -> Free g b
~ hoistFree :: Functor (LimaFocusCmd a)
	=> (forall k. LimaIndCmd a k -> LimaFocusCmd a k)
	-> LimaIndPrgm a k' -> LimaFocusPrgm a k'```



> newtype BFLimaListCmd a k
> 	= BFLimaListCmd (Cmd BFLimaListTerms BFLimaList_InTy' BFLimaList_OutTy' a k)
> 	deriving (Functor)

> newtype BFLimaCmd a k
> 	= BFLimaCmd ( CoRec (BFLima_CmdTy' a k) BFLimaTerms )



== Handlers ==

* Compare ontologies ((commands -> operations) by reaction policies,
	implementations, cocommands, coatoms)

-----



About the below newtypes:
* For languages with recursive sublanguages:
** Shape is the newtype wrapper of `Cmd`, which alters argument order,
squashed in with the establishing of shorthand notation that siblings'
type synonyms perform.
* For the languages without recursive sublanguages:
** Newtype involved since otherwise there's multiple copies of (`Cmd` [exact args])
appearing in other places, leading to error propogation.

> newtype LimaSymHdl a k
> 	= LimaSymHdl (Hdl LimaSymTerms LimaSym_InTy' LimaSym_OutTy' a k)
> 	deriving (Functor)

> newtype LimaIndHdl a k
> 	= LimaIndHdl (Hdl LimaIndTerms LimaInd_InTy' LimaInd_OutTy' a k)
> 	deriving (Functor)

> newtype LimaFocusHdl a k
> 	= LimaFocusHdl ( Rec (LimaFocus_HdlTy' a k) LimaFocusTerms )

> newtype BFLimaListHdl a k
> 	= BFLimaListHdl (Hdl BFLimaListTerms BFLimaList_InTy' BFLimaList_OutTy' a k)
> 	deriving (Functor)

> newtype BFLimaHdl a k
> 	= BFLimaHdl ( Rec (BFLima_HdlTy' a k) BFLimaTerms )



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

> liftedLimaIndCmd :: (term ∈ LimaIndTerms)
> 	=> proxy term
> 	-> LimaInd_InTy term a
> 	-> LimaIndPrgm a (LimaInd_OutTy term a)
> liftedLimaIndCmd = (hoistFree LimaIndCmd .)
> 	. liftPrgm' LimaInd_InTy' (\(LimaInd_OutTy' x) -> x)



Extending the lifted `LimaIndPrgm` recursive sublanguage programs
to `LimaFocusPrgm` parent language programs:

Comparison with command datatype implementation of paired DSLs & Interpreters:
Not important we haven't made this work out, but we can write this more general
term, by GHC wants `LimaFocus_CmdTy` to be an injective type function:

< limaFocusSublangCmd :: (term ∈ LimaFocusTerms)
< 	=> proxy term
< 	-> LimaFocus_CmdTy term a k
< 	-> LimaFocusCmd a k
< limaFocusSublangCmd _ = LimaFocusCmd . CoRec . LimaFocus_CmdTy'

Which lets one write (possibly requiring
`Proxy :: Proxy (LimaFocus_CmdTy 'LimaFocusIndTerm a k)`)

< liftedLimaFocusIndCmd :: LimaIndPrgm a k -> LimaFocusPrgm a k
< liftedLimaFocusIndCmd = hoistFree $ limaFocusSublangCmd Proxy

which parallels the hoisting of a constructor of a parent language command
from a recursive sublanguage command.

Instead, we just inline for each variant:

< liftedLimaFocusIndCmd :: LimaIndPrgm a k -> LimaFocusPrgm a k
< liftedLimaFocusIndCmd = hoistFree $ LimaFocusCmd . CoRec . LimaFocus_CmdTy'

This requires `LimaFocusCmd a` to be a functor, & we see this fails.



> liftedBFLimaListCmd :: (term ∈ BFLimaListTerms)
> 	=> proxy term
> 	-> BFLimaList_InTy term a
> 	-> BFLimaListPrgm a (BFLimaList_OutTy term a)
> liftedBFLimaListCmd = (hoistFree BFLimaListCmd .)
> 	. liftPrgm' BFLimaList_InTy' (\(BFLimaList_OutTy' x) -> x)

-----



Old



< liftedBFLimaTerm :: (term ∈ BFLimaTerms)
< 	=> proxy term
< 	-> BFLima_InTy term a
< 	-> BFLimaPrgm a (BFLima_OutTy term a)
< liftedBFLimaTerm = liftPrgm' BFLima_InTy' (\(BFLima_OutTy' x) -> x)

< bflimaInsertSym :: Identity a -> BFLimaPrgm a (Const () a)
< bflimaInsertSym = liftedBFLimaTerm (Proxy :: Proxy 'BFLimaInsertSym)

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

< liftAtomStringBFLima :: (String, String) {- (Term title, name of its lift) -} -> IO ()
< liftAtomStringBFLima = putStrLn . liftAtomString "BFLima_InTy" "BFLima_OutTy" "BFLimaPrgm" "liftedBFLimaTerm"

< liftAtomStringBFLima' :: String -> IO ()
< liftAtomStringBFLima' (_:_:_:xs) = liftAtomStringBFLima ("BFL"++xs, "bfl"++xs)
< liftAtomStringBFLima' _ = error "String not long enough to be a term name."

< liftedAtomStringsBFLima :: IO ()
< liftedAtomStringsBFLima = mapM_ liftAtomStringBFLima'
< 	$ ["BFLimaInsertSym", "BFLimaDeleteSym",
< 	"BFLimaMainFocusCmd", -- ignore this one
< 	"BFLimaPickedFocusCmd"] -- ignore this one

< bflimaDeleteSym :: BFLima_InTy 'BFLimaDeleteSym a
< 	-> BFLimaPrgm a (BFLima_OutTy 'BFLimaDeleteSym a)
< bflimaDeleteSym = liftedBFLimaTerm (Proxy :: Proxy 'BFLimaDeleteSym)

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

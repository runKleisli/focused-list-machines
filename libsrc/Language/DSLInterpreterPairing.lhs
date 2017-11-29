> {-# LANGUAGE MultiParamTypeClasses, RankNTypes, GADTs, TupleSections
> , DeriveFunctor, ScopedTypeVariables, DataKinds, TypeFamilies, PolyKinds
> , TypeOperators, FlexibleContexts #-}

> module Language.DSLInterpreterPairing where

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
> import Data.Proxy

Notation

> import Control.Arrow (first)



== Categories of atomic terms ==

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



=== Configurations ===

> liftRO ::
> 	( inTy' term a -> i ) {- Decompose input -}
> 	-> ( o -> outTy' term a ) {- Compose output -}
> 	-> proxy term
> 	-> ( d -> (i -> (o, b)) ) {- Goal process -}
> 	{- Lifted process for configuring a handler to use -}
> 	-> d -> RO inTy' outTy' a b term
> liftRO decomp comp _ fn d = ROform $ first comp . fn d . decomp



== DSL expressions ==

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

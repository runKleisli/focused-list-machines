> {-# LANGUAGE MultiParamTypeClasses, RankNTypes, GADTs, TupleSections
> , DeriveFunctor, ScopedTypeVariables, DataKinds, KindSignatures, TypeFamilies
> , PolyKinds, TypeOperators, FlexibleContexts, FlexibleInstances
> , NoMonomorphismRestriction, TypeSynonymInstances, KindSignatures #-}

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

> type Pairing f g = forall a b c. (a -> b -> c) -> g a -> f b -> c

"zapWithAdjunction"

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

-----

> data LimaTermOverSym = LimaSetSym | LimaGetSym

> type family LimaTermOverSym_InTy (t :: LimaTermOverSym) :: * -> * where
> 	LimaTermOverSym_InTy 'LimaSetSym = Identity
> 	LimaTermOverSym_InTy 'LimaGetSym = Const ()

> type family LimaTermOverSym_OutTy (t :: LimaTermOverSym) :: * -> * where
> 	LimaTermOverSym_OutTy 'LimaSetSym = Const ()
> 	LimaTermOverSym_OutTy 'LimaGetSym = Maybe

We need both pattern matching and partial application.

> newtype LimaTermOverSym_InTy' f a
> 	= LimaTermOverSym_InTy' (LimaTermOverSym_InTy f a)

> newtype LimaTermOverSym_OutTy' f a
> 	= LimaTermOverSym_OutTy' (LimaTermOverSym_OutTy f a)



> type LimaTermOverSym_Client a k
> 	= Cmd ['LimaSetSym, 'LimaGetSym]
> 		LimaTermOverSym_InTy' LimaTermOverSym_OutTy'
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

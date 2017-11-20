> {-# LANGUAGE MultiParamTypeClasses, Rank2Types, GADTs, TupleSections
> , DeriveFunctor, ScopedTypeVariables #-}

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

* Discrete

* Transpose:
** A criterion for minimizing...
** Organizing command ontology...

* Focused list machine commands
* Bifocused list machine commands



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

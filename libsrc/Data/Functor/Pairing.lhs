> {-# LANGUAGE MultiParamTypeClasses, Rank2Types #-}

> module Data.Functor.Pairing where

== Preliminaries ==

> import Control.Monad
> import Control.Comonad

> import Control.Monad.Free
> import Control.Comonad.Cofree

> import Data.Functor.Adjunction

=== Our pairing hierarchy ===

> type Pairing f g = forall a b c. (a -> b -> c) -> g a -> f b -> c

Pairs must be manually assembled

> pairRL :: (Adjunction f g) => Pairing f g
> pairRL = zapWithAdjunction

> pairLR :: (Adjunction f g) => Pairing g f
> pairLR = flip . pairRL . flip

but then we can fix the pairing to use between the term & handler type.

> class CmdsHandlersPair f g where
> 	pairCH :: Pairing f g

We induce the free-cofree pairing from such a canonical pairing, letting us pair
expressions and interpreters.

> pair :: (CmdsHandlersPair f g) => Pairing (Free f) (Cofree g)
> pair p (a :< _) (Pure x) = p a x
> pair p (_ :< gCga) (Free fFfx) = pairCH (pair p) gCga fFfx

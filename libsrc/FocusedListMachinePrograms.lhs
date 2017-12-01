> module FocusedListMachinePrograms where

== Imports ==

> import FocusedListMachine

== Program inventory ==

The requirements of the machine's DSL (BifocusedLimaPrgm) include programs
derived from the primitive ones, the atomic terms.

These form higher-level primitives, & a user of the machine might be restricted
to using a higher-level set of primitives when operating the machine, say
without the ability to move the picked focus but being able to swap its position
with the main focus, which can move. This would make the picked focus serve
as a focus recall & reference system but not a handy navigation system, which
allows expressions for navigating with the main focus to become simpler.

For symbols:
* Wiping
** A special case of setting where the symbol type is a Maybe (or some pointed type!)
* Transforming
** Combination of getting and setting

> limaWipeSym :: LimaSymPrgm (Maybe sym) ()
> limaWipeSym = limaSetSym Nothing

> limaRunOverSym :: (Maybe a -> a) -> LimaSymPrgm a ()
> limaRunOverSym = (limaGetSym () >>=) . (limaSetSym .)

For the bifocused list machine:

* With both foci
** SwapFocus
*** Interchange the focus indices
*** Decomposes into getting and setting indices
** PickFocus
*** Copying (overwriting) the main focus index to the picked focus index
*** Decomposes into getting and setting indices
** SetPickedSymToMain
*** Decomposes into getting the main focus sym, then setting the picked symbol
*** Copying (overwriting) the main focus value to the picked focus value
*** We need the reverse, setting focal value from picked's, just as much.
*** That decomposes into doing the first between swaps (though that runs slower).

> bflimaSwapFocus :: BFLimaPrgm sym ()
> bflimaSwapFocus = do
> 	mami <- bflimaMainFocusIndPrgm $ limaGetFocusInd ()
> 	pkmi <- bflimaPickedFocusIndPrgm $ limaGetFocusInd ()
> 	bflimaMainFocusIndPrgm $ limaRefocusInd pkmi
> 	bflimaPickedFocusIndPrgm $ limaRefocusInd mami

> bflimaPickFocus :: BFLimaPrgm sym ()
> bflimaPickFocus =
> 	bflimaMainFocusIndPrgm (limaGetFocusInd ())
> 	>>= bflimaPickedFocusIndPrgm . limaRefocusInd

> bflimaSetPickedSymToMain :: BFLimaPrgm sym ()
> bflimaSetPickedSymToMain =
> 	bflimaMainFocusSymPrgm (limaGetSym ())
> 	>>= maybe (return ()) (bflimaPickedFocusSymPrgm . limaSetSym)

> bflimaSetMainSymToPicked :: BFLimaPrgm sym ()
> bflimaSetMainSymToPicked =
> 	bflimaPickedFocusSymPrgm (limaGetSym ())
> 	>>= maybe (return ()) (bflimaMainFocusSymPrgm . limaSetSym)



== Analysis ==

Suppose we take this program for writing [@'a','b',#'c'] to the blank state, where
(@) denotes the main focus position, & (#) denotes the picked.

< debugBFLimaPrgm $ bflimaListPartPrgm (bflimaInsertSym 'a' >> bflimaInsertSym 'b' >> bflimaInsertSym 'c') >> bflimaPickFocus >> bflimaMainFocusIndPrgm (limaRefocusPrev () >> limaRefocusPrev ())

"--------------------------------------------"
"Program/expression output:"
()
"Interpreted state:"
BifocusedLima {LimaSymTable :-> "abc", LimaFocusMain :-> Just 0, LimaFocusPicked :-> Just 2}
"--------------------------------------------"

From this state, we can use one focus to modify the value at another:

MainSym := PickedSym

< debugBFLimaPrgm $ bflimaListPartPrgm (bflimaInsertSym 'a' >> bflimaInsertSym 'b' >> bflimaInsertSym 'c') >> bflimaPickFocus >> bflimaMainFocusIndPrgm (limaRefocusPrev () >> limaRefocusPrev ()) >> bflimaSetMainSymToPicked

"--------------------------------------------"
"Program/expression output:"
()
"Interpreted state:"
BifocusedLima {LimaSymTable :-> "cbc", LimaFocusMain :-> Just 0, LimaFocusPicked :-> Just 2}
"--------------------------------------------"

PickedSym := MainSym

< debugBFLimaPrgm $ bflimaListPartPrgm (bflimaInsertSym 'a' >> bflimaInsertSym 'b' >> bflimaInsertSym 'c') >> bflimaPickFocus >> bflimaMainFocusIndPrgm (limaRefocusPrev () >> limaRefocusPrev ()) >> bflimaSetPickedSymToMain

"--------------------------------------------"
"Program/expression output:"
()
"Interpreted state:"
BifocusedLima {LimaSymTable :-> "aba", LimaFocusMain :-> Just 0, LimaFocusPicked :-> Just 2}
"--------------------------------------------"



Watch what happens to the picked focus as we delete things beyond it.

0 deletions ['a',#'b',@'c']:

< debugBFLimaPrgm $ bflimaListPartPrgm (bflimaInsertSym 'a' >> bflimaInsertSym 'b' >> bflimaInsertSym 'c') >> bflimaMainFocusIndPrgm (limaRefocusPrev ()) >> bflimaPickFocus >> bflimaMainFocusIndPrgm (limaRefocusNext ())

"--------------------------------------------"
"Program/expression output:"
()
"Interpreted state:"
BifocusedLima {LimaSymTable :-> "abc", LimaFocusMain :-> Just 2, LimaFocusPicked :-> Just 1}
"--------------------------------------------"

1 deletion ['a',@#'b']:

< ... >> bflimaListPartPrgm (bflimaDeleteSym ())

"--------------------------------------------"
"Program/expression output:"
()
"Interpreted state:"
BifocusedLima {LimaSymTable :-> "ab", LimaFocusMain :-> Just 1, LimaFocusPicked :-> Just 1}
"--------------------------------------------"

2 deletions [@'a']:

< ... >> bflimaListPartPrgm (bflimaDeleteSym ())

"--------------------------------------------"
"Program/expression output:"
()
"Interpreted state:"
BifocusedLima {LimaSymTable :-> "a", LimaFocusMain :-> Just 0, LimaFocusPicked :-> Nothing}
"--------------------------------------------"

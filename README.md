Focused List Machines
======

About
------

The DSL-interpreter pairing as a concept is a division of labor and typing of components to a language ecosystem that allows one to generate different parts of the ecosystem or their typing from one another. It is an application of adjunctions, which is what it sounds like, but in a not so obvious way, and is a mathematical duality.

This project realizes the DSL-interpreter pairing through Vinyl co/records, creating domain specific languages for controlling machines that work similar to the inventory in Minecraft, a playlist viewer, or a file manager that can't open any folders.

As this is a port of a project originally done without Vinyl co/records, the documentation can be expected, but hasn't been carried over yet, and will need to be adapted to the modularization induced by the use of Vinyl co/records.

Zippers are out of the scope of this project.

References on the topic of the DSL-interpreter pairing:

* [D. Laing, "Cofun" series](http://dlaing.org/cofun/)
  * Mainly, D. Laing, "Free for DSLs, cofree for interpreters"
* [D. Piponi, "Cofree meets free"](http://blog.sigfpe.com/2014/05/cofree-meets-free.html)
* [G. Gonzalez, Comonads are objects](http://www.haskellforall.com/2013/02/you-could-have-invented-comonads.html)

...and other nice articles less directly relevant to this project's actual code.



The DSL-interpreter pairing through the Vinyl lens
------

The existence of the DSL-interpreter pairing means that once one type is determined, so is the other, that implementing both comes down to filling out values for opposite sides of the system, and that there is a way of extending

```pair :: CmdsHandlersPair f g => (a -> b -> c) -> Cofree g a -> Free f b -> c```

a combination like

```debugOutputAndState :: (Show a, Show b) => a -> b -> IO ()```

of state and possible program output into combinations like

```
debugInterpDSL :: (Show stateTy, Show k, CmdsHandlersPair f g, Functor g)
	=> Cofree g stateTy {- Initial interpreter state -}
	-> Free f k {- Program to debug -}
	-> IO ()
```

of DSL programs formally producing such values with interpreters of the programs that can base the interpretation on such an internal state, and simply a way to combine state and program that apply the program as a state transition.

```
stepDSLState _configurer :: Free f k -> stateTy -> stateTy

stepPrgmState ::
	(stateTy -> Hdl termList inTy outTy a stateTy)
	-> Prgm termList inTy outTy a k
	-> stateTy -> stateTy
stepPrgmState = stepDSLState
```

The DSL's terms are assigned input and output types as abstract programs in the language during specification. When using Vinyl, these parts of the spec are implemented:

```
data LimaSymTerm = LimaSetSym | LimaGetSym

type LimaSymTerms = ['LimaSetSym, 'LimaGetSym]

type family LimaSym_InTy (t :: LimaSymTerm) (a :: *) :: * where
	LimaSym_InTy 'LimaSetSym a = a
	LimaSym_InTy 'LimaGetSym a = ()

type family LimaSym_OutTy (t :: LimaSymTerm) (a :: *) :: * where
	LimaSym_OutTy 'LimaSetSym a = ()
	LimaSym_OutTy 'LimaGetSym a = Maybe a
```

Note that where a command doesn't require any input, `()` is the input type used, since one can always supply a unique `()` to a command requiring this, and where a command doesn't have meaningful output, `()` is the output type used, since all implementations have that one way to produce a `()`.

The commands to run the programs on such a Haskell input value are values of a command type described in (Laing, "Cofun"). The action to perform on state in response to a command being called is a configurer for that command's part of a handler. The command & handler types are determined by the input & output types.

The command values are actually all trivial, because they only need to produce a formal output given an input.

However, the handlers' configurers, meaning producers of handlers from an initial state of some type, are the types of state transitions depending on a real value of this type. Hence, one can imagine starting from the library of state transitions, and working back to the language, which is generated as soon as the input and output types of formal commands are known. Besides the `StateTy -> StateTy` part of the library functions, there may be dependencies on information besides the initial & posttransition state, as in `setColorAndName :: Color -> String -> StateTy -> StateTy`, and the product `(Color, String)` over these gives the input required in a command to use this library function. It may be the command extracts some information from the state `getColorAndName :: StateTy -> (Color, String)`, besides what it does to the state, and this product of extra information types gives the output type for a corresponding command. If one then configures the assignment of input & output types to terms using this kind of reasoning, the corresponding handler type will contain a projection type that can be satisfied by trivially modifying the original library function's application to the initial state's, though we have to use newtype wrappers which obscure this a little:

```
LimaSymHdl a k
	-- >:i LimaSymHdl
~= Hdl LimaSymTerms LimaSym_InTy' LimaSym_OutTy' a k
	-- >:i LimaSym_InTy'
	-- >:i LimaSym_OutTy'
~= Hdl LimaSymTerms LimaSym_InTy LimaSym_OutTy
	-- >:i RO LimaSym_InTy LimaSym_OutTy
~= ( coLimaSetSym_ :: a -> ((), k), coLimaGetSym_ :: () -> (Maybe a, k)),

StateTy -> LimaSymHdl a StateTy
~= (StateTy -> a -> ((), StateTy), StateTy -> () -> (Maybe a, StateTy))

getSymPlainly :: StateTy -> Maybe a
coLimaGetSymConforming :: StateTy -> () -> (Maybe a, StateTy)

coLimaGetSym :: a {- Initial state -} -> () -> (Maybe a, a {- Final state -})
coLimaGetSym a () = (Just a {- What to tell the caller -}, a {- Unchanged state -})
```

and indeed one can use the tension between the opposite ends of implementation & specification to use one to constrain the other. Since the term category is absent in the plain sum/product datatypes approach, there is nothing calculating the constraints in the relationship between commands, handlers, input/output typings, & backend library semantics for the user, so it requires an investment studying the DSL-interpreter pairing to be recognized, but if one tracks the invocations of `liftRO` & `liftPrgm`, it's revealed there are ways to use the types to impose on one another in ways the compiler can calculate:

```
confLimaSymHdl2 :: a -> LimaSymHdl a a
confLimaSymHdl2 a = LimaSymHdl . Hdl
	$ liftCoLimaSym (Proxy :: Proxy 'LimaSetSym) _setSymFn a
	:& liftCoLimaSym (Proxy :: Proxy 'LimaGetSym) _getSymFn a
	:& RNil

• Found hole: _setSymFn :: a -> a -> ((), a)
• Found hole: _getSymFn :: a -> () -> (Maybe a, a)

term category LimaSymTerm, input & output assignments,
assignments' newtype wrappers (consequence of trying to use w/ (Hdl))
==> implementation of liftCoLimaSym
==> implementation of confLimaSymHdl2 up to holes
```

A handler must be capable of responding to every command, so it must be a product over the types that would handle single commands and the product can be indexed over the terms of the language. A command can invoke precisely one of the several terms of the language, so it is a coproduct over the terms of the language of the command types determined by each one. So each term of the language has a section of the command type & a projection of the handler type.

The pairing is a use of adjunctions that relate commands & handlers, & the ones covered by (Laing, "Cofun") are all combinations of product and function type constructions related by the product-function adjunction, `curry`ing and `uncurry`ing. We call these `IY` and `RO` for the one-term commands & handlers in the factorization, while (Laing, "Cofun", "Pairing over the network") calls them `Client` & `Interpreter`, though the "interpreter" type there differs from the one paired with the DSL programs directly like what we call the interpreter type here, & differs from the program that performs the interpretations, semantic assignments or Haskell bindings, of DSL programs, which is more like the different constructions produced in terms of the `Pairing` called `pair` between DSL programs & interpreters.

Sum & product datatypes correspond to corecords & records. Corecords are containers of values at a field label, where the names are distinguished by the coproduct's datatype constructors.

Vinyl treats co/records as types parametrized over a common field label category, so that corecords (values for one field to have) can be used to set the fields of a record.

Take the field label category to be the terms of a language, ignoring input and composition. Assume the term category has only identity arrows, for simplicity. Then, for example, we can configure assignments of Haskell input and output types for those terms as functors from the term category to `(*)`. Hence, we can treat inputs & outputs for a particular term as corecords at that term using those functors. So, `CoRec inputType termsList`.

By combining the functors in two ways, we can express commands in the language as corecords over the term category, express handlers as records over the term category. Because the term category & input & output type functors are shared between these structures, Haskell knows one is a coproduct of a certain form, the other a product, & that the names are reused between them such that the coproduct section for one term is from a type dual to the product section for the same term. This means we can generate the command-handler pairing and induced DSL-interpreter pairing of the kind discussed in (Liang, "Cofun").

As discussed in (Liang, "Cofun"), the paired types are all of a form determined by the input and output types each term in the language should have as a program. Not only are these the forms between which a pairing is generated, but we can define what it means to be a command or handler in terms of the specification of input and output types, which subverts the goal of deducing the handler or command type & the following process of deducing its dual. Such a process must still be performed for more complicated pairings, but can be done by analogy. The key is that this approach applies whenever the terms of a language are organized into sublanguages having uniform command and handler types.

The result is in the Vinyl approach, one proceeds directly to the enumeration of terms or supported commands, and then specification of the input and output types of commands, whether trying to produce an interpretation of an abstract language or trying to make a programming language for interfacing with an existing library.

The missing piece for a user to learn is the change of goals from handler projections to handler projection configurers. These configurers correspond to an underlying state transition library. So it's key to be able to convert between the goals, but this hasn't been automated.

This should be automated, if the goal of using Vinyl here is automating the typing ontology & the constraints & inferences between typings within the ontology that is taught by the DSL-interpreter pairing, & generating the goals for instantiating the DSL & interpreter part of a language ecosystem given intuitive constraints, the typing of inputs & outputs. However, this adds extra newtype wrappers & boilerplate with no benefits that can't be gained from looking at the way an example's backend is packed into a handler configurer, or looking at the type of `coiter`. At least, the constraint between names matching being enforced by the type system is a shortcut past that phase of understanding command-handler pairings & how to structure an implementation given understanding of only one component of the problem.



The list machines (Limas)
------

Three machines are presented:

```
FocusedLima sym ~= ([sym], Maybe Int)
BifocusedLima sym ~= ([sym], Maybe Int, Maybe Int)
SelectingLima sym ~= ([sym], Maybe Int, [Int])
```

Each such machine has a symbol list & a distinguished or main focus which can be used to navigate the symbol list. Operations can then be performed on the symbol list with respect to that main focus by running programs on it from variously nested DSLs.

For instance,

```
debugBFLimaPrgm $ bflimaListPartPrgm (bflimaInsertSym 'a')
```

will, starting from an initially blank `BifocusedLima Char` where the main and picked focus are unset, insert the symbol `'a'`, which also sets the main focus to 0. It then prints the updated state and the program output.

`stepBFLima` can be used with the program and `blankBFLima` for more general state updates, since a `BifocusedLima Char` can always have its state printed, but it doesn't show a program's output.

The Bifocused List Machine also has a "picked" focus for performing operations that involve more than one entry of the list at a time, and the Selecting List Machine has a selection of indices for the same purpose.

At present, `BFLimaPrgm` is the only programming language fully supported. So enjoy programming your Bifocused List Machine!



Things tried & repo structure
------

The development branch for the current version is `cmd-lvl-recsublang-sections-termless-parents`.

In the other branches, one can find other approaches to abstracting the DSL-interpreter pairing in Vinyl, but `term-lvl-recsublang-sections` & `cmd-lvl-recsublang-sections` ran into problems that need dependent types to solve, which seem to me to be the same problem with type errors more & less suggestive of needing dependent types respectively.

I consider `term-lvl-recsublang-sections` to be the ideal form of the DSL-interpreter pairing. It is the only form where the full pairing for a language with recursive sublanguages is generated as a co/record pairing. In this case, the term category itself contains named sections of terms of the sublanguages from which it is constructed. Input and output types are then assigned as the input and output types of its argument as a term in its own language. But since one has to lift the parent language constructors and not the arguments to reference the co/records, co/free types, & newtype wrappers, this leads to a situation where in order to extend commands and handlers from the recursive sublanguage to the parent, one would have to be able to compare the value-level term argument to its type-level lift that's used to talk about the recursive sublanguage data.

The `cmd-lvl-recsublang-sections` branch tries to accept the parent language terms must be nonrecursive atoms, but keep a term category for languages that have recursive sublanguages & a pervasive co/record approach, but breaks down at the instantiation of functors that recurse into the sublanguages' `fmap`s because newtype wrappers over the input & output type families alone can't be pattern matched in a way that distinguishes the recursive sublanguages - each possibility has to be guarded by its own constructor. Breaking into the type to use its own constructor as part of the match requires dependent types to match the result of `fmap`ping, in a failure of unification, so the distinguishing constructors have to be for the combined type. Having an `fmap` that will work for all possible types requires explicitly quantifying its type over the different specializations, which entails quantifying over a term category without being able to say each term should be lifted or specify a lift or use the term in the types being quantified. Hence the current approach, which uses a plain old co/record for collecting recursive sublanguage types into host nodes.

It's still unclear if many lines of boilerplate are eliminated by switching to Vinyl records, or if things were just made more complicated. So I should factor out the Vinyl library & check. Is the boilerplate nicer? Some of the boilerplate can be ignored by using proxies or singletons and calling `liftPrgm'` directly, but that means no static documentation of the command types, call interfaces of the language. With dependent types, there would definitely be less boilerplate.

So I suppose the benefit to this approach right now is in having a directed process for language construction with feedback (types of holes) about types of pieces required that doesn't do anything for the user they might want to do themselves except in transparent ways. Since it enforces constraints in types within the DSL-interpreter pairing's scope, a user can learn about or work on implementing certain subsystems in isolation of others. Since it follows an ontology meant for structuring manual implementation, the user can replace a given piece with their own work or special cases when following along with a study of that part of DSL-interpreter pairing.



Development goals
------

* (ported) Documentation
* (ported, meagre) Testing
* Modularization
* Generated boilerplate? Template Haskell? Abandon all hope?
* Parsing text off console
  * Pairing over the network type stuff
* Full languages for the other machines
* Reduction to minimal languages of `BifocusedLima` & `SelectingLima` of a language w/ copypaste & fixed binary operations, with different interpreters for the Selecting List Machine (SelectingLima, SelLima*) based on whether the selection is to be kept sorted.
* Hyperfocus - a focused list of focuses!

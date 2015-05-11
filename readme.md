
## Scope Graphs

This work is the product of a simple idea:

> What if the scope of a term is modeled as a partial order over
> variable decarlations and references, where x < y means that y is in
> the scope of x?

For instance, in the term:

    lam('x, 'y): lam('z): y

(writing variable declarations with a quote 'x)
'z is in scope of 'x and 'y, and y is in scope of 'x, 'y, and 'z,
giving the partial order generated by: `'x < 'z, 'y < 'z, 'z < y`.

These partial orders immediately gives rise to some notions of binding:

* A variable reference is _unbound_ when it is not in scope of some
  declaration of the same name.
* A variable reference is _bound to_ the _greatest_ declaration of the
  same name it is in scope of.
* A variable reference is _ambiguously bound_ if it is bound but the
  declarations of the same name it is in scope of have no greatest
  element.
* One variable declaration _shadows_ another when they have the same
  name and the first is in scope of the second.

A few lemmas (which will be proved elsewhere) will show that these
notions match pretty well with our intuition:

* Lemma: A variable reference can only be bound to a declaration it is
  in scope of.
* Lemma: Every variable reference is exclusively unbound, ambiguously
  bound, or bound.
* Lemma: Shadowing means what you expect -- if one declaration shadows
  another, then a reference in scope of the shadowing declaration
  cannot be bound to the shadowed declaration.


## Implementation in Haskell

These partial orders can be encoded in Haskell's type system. This is
done in `scope.hs`. It can be used to guarantee that well-typed
functions over terms must preserve the order of their variables in the
partial order. Since this partial order determines the binding
structure of the term, this ensures that all well-typed functions over
terms are hygienic.

Let me describe the most relevant types, and what they mean. First, a
value of type `Scope a` represents a node `a` in a scope partial
order. Concretely, it keeps track of which variables are in scope up
to this point. A special scope value `emptyScope` has type `Scope ()`
that denotes the empty scope.

### Variables

Given scopes, the functions `newDecl` and `newRefn` construct a new
variable declaration and reference:

    newDecl: String -> forall a. exists b. Scope a -> (Decl a b, Scope b)
    newRefn: String -> forall a. Scope a -> Either BindError (Refn a)

(The actual types in Haskell are slightly different for technical
reasons, but this is the essense of the matter.)  `newDecl "x"` takes
a scope (`Scope a`) containing some set of variable names, extends it
to produce a new scope (`Scope b`) that also has "x" in scope, and
returns both the new scope and a `Decl a b` object representing the
variable declaration. The existential quantifier forces `a` and `b` to
effectively be different types. Likewise, `newRefn "x"` takes a scope
object, checks that "x" is actually in scope in it, and returns a
`Refn a` object representing the new variable.

### Enviroments

The interesting bit happens when you try to _use_ `Decl` and `Refn`
objects. They are completely opaque (in particular, their names are
hidden!), besides two operations `bind` and `find`:

    bind :: Decl a b -> v -> Env v s a -> Env v s b
    find :: Refn a -> Env v s a -> v

These makes use of environments. Environments are like scopes, but
instead of merely keeping track of which variables are in scope, they
actually contain bindings to them. An environment of type `Env v s a`
binds variables to values of type `v`, has scope `a`, and has some
additional state `s` for convenience. `emptyEnv` constructs an empty
environment. After that, environments can only be extended with
`bind`, and variable references can only be lookup up using `find`.
Notice that `find` returns a value of type `v` and not, e.g. `Maybe
v`: it is guaranteed to succeed.

To give an example of this in action, consider constructing a variable
declaration and then a reference to it:

    mtScope = emptyScope
    (xScope, xDecl) = newDecl "x" mtScope
    xRefn = newRefn "x" xDecl

Now if you wanted to use `xRefn`, the only operation you can perform
on it is `find`. But calling `find xRefn emptyEnv` would produce a
type error, since the type variable in `xRefn` came from the
existentially quantified variable produced by `newDecl`. The only way
to actually call `find` is to first `bind` `xDecl`:

    find xRefn (bind xDecl 17 emptyEnv)


### Modules

Module scope is also supported. A module _export_ with name M and type
`Export a b` takes all of the variables in scope in `a`, binds them
under M, and makes *only* M be in scope in `b`. A module _import_ with
name M and type `Import a b` expects M to be in scope in `a`, and
splats all of its bindings into scope in `b`.

### Contexts

Some transformations over terms are nicely represented using
_contexts_, which are terms with holes in them. To be hygienic,
however, these contexts must have _different_ scopes for their own
variables and for the variables that might happen to appear in terms
placed in their holes. The type constructor `Pair a b` is used for
this purpose: it represents the scope of a context whose own scope is
`a`, and whose holes' scope is `b`.


### Correspondence with Scope Graphs

All of the guarantees about scope follow from the functions defined in
`scope.hs`. Once again, the type signatures for constructing variable
decarations and references are:

    newDecl: String -> forall a. exists b. Scope a -> (Decl a b, Scope b)
    newRefn: String -> forall a.           Scope a -> Either BindError (Scope b)

The type variables `a` and `b` here represent elements of the partial
order described above. More specifically, a value of type `Scope a`
proves that `a` is a valid position in some partial order. A value of
type `Decl a b` denotes a variable declaration whose position in the
partial order is `b`, and whose predecessor is `a`. Likewise, a value
of type `Refn a` denotes a variable reference whose predecessor is
`a`. In case a variable has two predecessors in the partial order, the
function `joinScope` joins them together:

    joinScope :: Scope a -> Scope b -> Scope (Join a b)

Thus the correspondence between the scope partial order presented
above, and the actual types in `scope.hs` is given by:

* If a value of type `Decl a b` exists, then `a < b`.
* If `a` (or `b`) above have the form `Join c d`, then
  `a < c` and `a < d`.


## Test Cases

This system is tested for a small language defined in `term.hs`. The
language has many interesting binding constructs. Notably, ASTs are
broken down into four types with different binding properties:

* Statements include variable and function definitions. Variable
  definitions are put into scope in later statements, and sequences of
  adjacent function definitions are all in scope of one another (as
  well as in scope of later statements), thus allowing mutually
  recursive functions. This is the same scope behavior as Pyret.
* Patterns allow arbitrarily-nested destructuring assignment.
* Case statements use patterns to perform case matching.
* Expressions do not introduce new binding, and this is guaranteed by
  their type signature (which has just one scope variable, instead of
  two).

Three functions are implemented on top of this language. All of these
functions respect the scope of the terms they act on: passing a wrong
environment anywhere results in a type error. These functions are:

* _`show`_: prints a term (using variable names `a`, `b`, etc., since the
  original variable names are inaccessible).
* _`eval`_: evaluates a term, using big-step semantics.
* _`desugar`_: Desugar a term. The type system guarantees this is
  hygienic.

Test cases for these functions are given in `test.hs`.

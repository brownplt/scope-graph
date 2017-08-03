# Scope Inference

This is the reference implementation for "Inferring Scope through Syntactic Sugar", ICFP'17.

## Installation

To install Rust, follow the
[official Rust installation instructions](https://www.rust-lang.org/en-US/install.html).

The installation script may suggest that you update your PATH
environment variable; do as suggested.

This has been tested on Rust 1.9 and 1.17, though later versions
should work as well.

## Usage

Input files (extension `.scope`) contain sugar definitions and
scoping rules for the base language. Scope inference then determines the
minimal set of scoping rules for the sugars such that desugaring
preserves scope---or fails if there are no such scoping rules.

To infer scope for an input file:
```cargo run filename.scope```

To read a .scope file through stdin:
```cargo run stdin```

Examples of language definitions (mainly from the paper) may be
found in `src/examples/`.

## Overview

Language definition files end in ".scope". Examples can be found in `src/examples/`.

Each language consists of a list of base language constructs,
which have arities and scoping rules,
followed by a list of surface constructs (i.e. sugars),
followed by a list of desugaring rules of the form `rule Term1 => Term2`.
The scoping rules take the form:

- `import i`: Provide lexical scope to child i.
              (You almost certainly want 'import i' for each 'i'.)
              In the diagrams in the paper, this is a *down* arrow.
- `export i`: Export child i's declarations.
              In diagrams, this is an *up* arrow.
- `bind i in j`: Make child i's declarations available in child j.
              In diagrams, this is an *across* arrow.
- `re-export`: Export your imports.
               (This is rarely if ever needed, but provided for completion.)

As an example, src/examples/single_arm_let.scope reads:

```text
language Test {
  (Lambda param body) {
    import param;
    import body;
    bind param in body;
  }
  (Apply func arg) {
    import func;
    import arg;
  }
  
  sugar (Let name defn body)
  
  rule (Let a b c) => (Apply (Lambda a c) b)
}
```

The statements (e.g. `import`, `bind`) in each rule are UNORDERED.

Variable declarations begin with `@` (e.g. `@x`), and variable
references begin with `$`. Global references begin with `global$`,
and copying a declaration as a reference (as mentioned at the
beginning of section 6 of the paper) is written as `as_refn$x`.

The output is a set of scoping rules for the surface language
(that is, for the sugars). They are shown in a nondeterministic
order.

## Artifact Evaluation Instructions

#### Step 1: Install Rust

Follow the the `Installation` instructions above.

#### Step 2: Run the tests

In the scope-inference directory, run `cargo test`.
They should all pass.
(This runs `src/test.rs`.)

This runs the test cases, but does not show the inferred scopes.
To see the inferred scopes and total inference time,
run `cargo run timing_test`. (This runs `timing_test()` in `src/main.rs`.)

Both of these commands infer scope for five languages:

- Single-arm let (example 1 from the paper)
- Multi-arm let (example 2 from the paper)
- Haskell List Comprehensions (section 6: evaluation)
- Pyret's sugars that bind values (section 6: evaluation)
- R5RS sugars that bind values (section 6: evaluation)

Here are the claims from the paper that can be verified against
this implementation.

- Section 2.1: single-arm let is the first test language.
  Run `cargo run src/examples/single_arm_let.scope`.
- Section 2.2: multi-arm let is the second test language.
  Run `cargo run src/examples/multi_arm_let.scope`.
- Section 5.2: the example of constraint generation given at the
end of this section is tested in `constraint_generation()` in `src/test.rs`.
(This test is run when invoking `cargo test`.)
- Section 6: the wallclock runtime is measured when running
`cargo run timing_test`.
- Section 6.1: this `for` sugar is from the Pyret language.
  Run `cargo run src/examples/pyret.scope`.
  (The output will include other sugars in addition to `for`.)
- Section 6.2: all of these sugars are from Haskell list
comprehensions.
  Run `cargo run src/examples/list_comprehension.scope`.
- Section 6.3: this `named-let` sugar is from R5RS scheme.
  Run `cargo run src/examples/r5rs.scope`
  What the paper calls `Let` and `Bind` is called `NamedLet` and
  `NamedLetBind` in the ouput.
  (The output will include other sugars in addition to these.)
- Section 6.4: you can see scope inference fail on the `do` sugar
by running `cargo run src/examples/do.scope`.

## Extra Features

The implementation now has experimental support for ellipses in
desugaring rules. To use them, put `...` as the last child of a
node in a desugaring rule. Examples can be found in
"src/examples/pyret_ellipses.scope" and "src/examples/r5rs_ellipses.scope".

The implementation has one more feature mentioned but not discussed in the paper: when
declaring a sugar, you can require that some of its variables have distinct names.
Usually this isn't necessary, because it can be inferred,
but it's needed for `letrec`. The syntax for this is, e.g.,
```text
      sugar (LetrecBind var init binds) {
        disjoint import var;
        disjoint bind var in binds;
      }
```

## Files

 - `src/parser/*`:       parser & lexer
 - `src/preorder.rs`:    Preorders
 - `src/term.rs`:        Terms & Rewrite rules
 - `src/rule.rs`:        Scope rules & languages (which contain scope rules & rewrite rules)
 - `src/infer.rs`:       Scope inference
 - `src/test.rs`:        The test cases (Let, Let*, Pyret)
 - `src/main.rs`:        Toplevel program; takes command line args

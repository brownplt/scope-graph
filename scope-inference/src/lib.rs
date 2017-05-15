//! # Scope Inference
//!
//! This is the reference implementation for "Inferring Scope through Syntactic Sugar", ICFP'17.

//! ## Artifact Evaluation Instructions
//! 
//! #### Step 1: Install Rust
//!
//! Follow the the `Installation` instructions below.
//!
//! #### Step 2: Run the tests
//!
//! In the scope-inference directory, run `cargo test`.
//! (This runs `src/test.rs`.)
//!
//! To see the inferred scopes and total inference time,
//! run `cargo run tests`. (This runs `timing_test()` in `src/main.rs`.)
//!
//! Both of these commands infer scope for five languages:
//!
//! - Single-arm let (example 1 from the paper)
//! - Multi-arm let (example 2 from the paper)
//! - Haskell List Comprehensions (section 6: evaluation)
//! - Pyret's sugars that bind values (section 6: evaluation)
//! - R5RS sugars that bind values (section 6: evaluation)
//! 
//! Here are the claims from the paper that can be verified against
//! this implementation.
//! 
//! - Section 2.1: single-arm let is the first test language.
//! - Section 2.2: multi-arm let is the second test language.
//! - Section 5.2: the example of constraint generation given at the
//! end of this section is tested in `constraint_generation()` in `src/test.rs`.
//! - Section 6: the wallclock runtime is measured when running `cargo
//! run tests`.
//! - Section 6.1-6.3: these sugars are part of the Pyret and R5RS
//! language test cases.
//! - Section 6.4: you can see scope inference fail on the `do` sugar
//! by running `cargo run src/examples/do.scope`.
//!
//! Claims about the scope inferred for a sugar can be verified either
//! by viewing the test case in `src/test.rs`, or by running `cargo
//! run tests` and checking the inferred scope for that sugar shown in the output.

//! ## Installation
//!
//! To install Rust, run:
//! ```curl -sSf https://static.rust-lang.org/rustup.sh | sh```
//!
//! The installation script may suggest that you update your PATH
//! environment variable; do as suggested.
//!
//! If you have any troubles, or wish to install Rust using a
//! different method, see the official
//! [Rust installation instructions](https://www.rust-lang.org/en-US/install.html).
//!
//! This has been tested on Rust 1.9 and 1.17, though later versions
//! should work as well.
//! 
//! ## Usage
//!
//! Input files (extension `.scope`) contain sugar definitions and
//! core language scoping rules. Scope inference then determines the
//! minimal set of scoping rules for the sugars such that desugaring
//! preserves scope---or fails if there are no such scoping rules.
//! 
//! To infer scope for an input file:
//! ```cargo run filename.scope```
//!
//! To read a .scope file through stdin:
//! ```cargo run stdin```
//!
//! Examples of language definitions (mainly from the paper) may be
//! found in `src/examples/`.

//! ## Overview
//! 
//! The language definition files end in ".scope". Examples can be found in `src/examples/`.
//! 
//! Each language consists of a list of core scoping constructs, which have arities and scoping rules,
//! followed by a list of surface constructs (i.e. sugars),
//! followed by a list of desugaring rules of the form `rule Term1 => Term2`.
//! The core langauge scoping rules take the form:
//! 
//! - `import i`: Provide lexical scope to child i.
//!               (You almost certainly want 'import i' for each 'i'.)
//! - `export i`: Export child i's declarations.
//! - `bind i in j`: Make child i's declarations available in child j.
//! - `re-export`: Export your imports.
//!                (This is rarely if ever needed, but provided for completion.)
//! 
//! As an example, src/examples/single_arm_let.scope reads:
//! 
//! ```text
//! language Test {
//!   (Lambda param body) {
//!     import param;
//!     import body;
//!     bind param in body;
//!   }
//!   (Apply func arg) {
//!     import func;
//!     import arg;
//!   }
//!   
//!   sugar (Let name defn body)
//!   
//!   rule (Let a b c) => (Apply (Lambda a c) b)
//! }
//! ```

//! ## Extra Features
//! 
//! The implementation has one feature mentioned but not discussed in the paper: when
//! declaring a sugar, you can require that some of its variables be
//! disjoint. Usually this isn't necessary, because it can be inferred,
//! but it's needed for `letrec`. The syntax for this is, e.g.,
//! ```text
//!       sugar (LetrecBind var init binds) {
//!         disjoint import var;
//!         disjoint bind var in binds;
//!       }
//! ```

//! ## Files
//! 
//!  - `src/parser/*`:       parser & lexer
//!  - `src/preorder.rs`:    Preorders
//!  - `src/term.rs`:        Terms & Rewrite rules
//!  - `src/rule.rs`:        Scope rules & languages (which contain scope rules & rewrite rules)
//!  - `src/infer.rs`:       Scope inference
//!  - `src/test.rs`:        The test cases (Let, Let*, Pyret)
//!  - `src/main.rs`:        Toplevel program; takes command line args
extern crate regex;
#[macro_use] extern crate lazy_static;

mod util;
mod preorder;
mod term;
mod resolve;
pub mod rule;
pub mod parser;
pub mod infer;
mod test;

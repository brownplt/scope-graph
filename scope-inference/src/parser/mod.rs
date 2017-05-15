mod source;
mod lexer;
mod parser;

use term::{RewriteRule};
use preorder::{Lt};
use rule::{Language};
use self::parser::Parser;

pub use self::source::SourceFile;

/// Parse a language definition.
///
/// A language definition consists of a list of core scoping constructs,
/// which have arities and scoping rules,
/// followed by a list of surface constructs (i.e. sugars),
/// followed by a list of desugaring rules of the form `rule Term1 => Term2`.
///
/// The core langauge scoping rules take the form:
///
/// *   `import i`    - Provide lexical scope to child i.
///                   (You almost certainly want `import i` for each i.)
/// *   `export i`    - Export child i's declarations.
/// *   `bind i in j` - Make child i's declarations available in child j.
/// *   `re-export`   - Export your imports.
///                   (This is rarely if ever needed, but provided for completion.)
///
/// For examples, see the `.scope` files in the `examples` directory.
pub fn parse_language<'s, Val>(src: &'s SourceFile) -> Language<Val> {
    Parser::from_source(src).parse_language().unwrap()
}

/// Parse a single rewrite rule, such as
/// `rule (Let a b c) => (Apply (Lambda a c) b)`.
pub fn parse_rewrite_rule<'s, Val>(src: &'s SourceFile) -> RewriteRule<Val> {
    let mut parser = Parser::from_source(src);
    let ans = parser.parse_rewrite_rule().unwrap();
    parser.parse_eof();
    ans
}

/// Parse a single fact, such as
/// `bind name in body;`.
pub fn parse_fact<'s>(src: &'s SourceFile, args: &Vec<String>) -> Lt {
    Parser::from_source(src).parse_fact(args).unwrap()
}

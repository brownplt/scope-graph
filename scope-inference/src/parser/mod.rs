mod source;
mod lexer;
mod parser;

use term::{RewriteRule};
use preorder::{Lt};
use rule::{Language};
use self::parser::Parser;

pub use self::source::SourceFile;



pub fn parse_rewrite_rule<'s, Val>(src: &'s SourceFile) -> RewriteRule<Val> {
    let mut parser = Parser::from_source(src);
    let ans = parser.parse_rewrite_rule().unwrap();
    parser.parse_eof();
    ans
}

pub fn parse_language<'s, Val>(src: &'s SourceFile) -> Language<Val> {
    Parser::from_source(src).parse_language().unwrap()
}

pub fn parse_fact<'s>(src: &'s SourceFile, args: &Vec<String>) -> Lt {
    Parser::from_source(src).parse_fact(args).unwrap()
}

mod source;
mod lexer;
mod parser;

use std::str::FromStr;
use std::fmt;
use std::hash::Hash;

use term::{RewriteRule};
use rule::{Language};
use self::parser::Parser;

pub use self::source::SourceFile;



pub fn parse_rewrite_rule<'s, Node, Val>(src: &'s SourceFile) -> RewriteRule<Node, Val>
    where Node: FromStr, Node::Err: fmt::Debug
{
    let mut parser = Parser::from_source(src);
    let ans = parser.parse_rewrite_rule().unwrap();
    parser.parse_eof();
    ans
}

/*
pub fn parse_term<'s, Node, Val>(src: &'s SourceFile) -> Term<Node, Val>
    where Node: FromStr, Node::Err: fmt::Debug
{
    Parser::from_source(src).parse_term().unwrap()
}
*/

pub fn parse_language<'s, Node, Val>(src: &'s SourceFile) -> Language<Node, Val>
    where Node: FromStr + Clone + Eq + Hash + fmt::Display, Node::Err: fmt::Debug
{
    Parser::from_source(src).parse_language().unwrap()
}

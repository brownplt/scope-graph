use std::iter::Peekable;
use std::str::FromStr;
use std::fmt;

use source::SourceFile;
use lexer::{Lexeme, Token, Lexer};
use term::{Term, Var, RewriteRule};
use rule::Elem::{Child, Imp, Exp};
use rule::{Fact, ScopeRule};



pub fn parse_rewrite_rule<'s, Node, Val>(src: &'s SourceFile) -> RewriteRule<Node, Val>
    where Node: FromStr, Node::Err: fmt::Debug
{
    let mut parser = Parser::from_source(src);
    let ans = parser.parse_rewrite_rule().unwrap();
    parser.parse_eof("Rewrite Rule");
    ans
}

pub fn parse_term<'s, Node, Val>(src: &'s SourceFile) -> Term<Node, Val>
    where Node: FromStr, Node::Err: fmt::Debug
{
    Parser::from_source(src).parse_term().unwrap()
}

type Stream<'s> = Peekable<Lexer<'s>>;

struct Parser<'s> {
    stream: Peekable<Lexer<'s>>
}

impl<'s> Parser<'s> {
    fn new(lexer: Lexer<'s>) -> Parser<'s> {
        Parser{
            stream: lexer.peekable()
        }
    }

    fn from_source(src: &'s SourceFile) -> Parser<'s> {
        let lexer = Lexer::new(src);
        Parser::new(lexer)
    }

    fn check<T>(&mut self, expected: &str, result: Result<T, ()>) -> T {
        match result {
            Err(()) => {
                match self.stream.next() {
                    None => {
                        panic!("Expected {}, but found EOF");
                    }
                    Some(lex) => {
                        let found = lex.span.as_str();
                        let info = lex.span.preview(80);
                        panic!("Expected {}, but found {}\n{}", expected, found, info);
                    }
                }
            }
            Ok(t) => t
        }
    }

    fn parse_eof(&mut self, expected: &str) {
       match self.stream.peek() {
           None => (),
           Some(lex) => {
               let found = lex.span.as_str();
               let info = lex.span.preview(80);
               panic!("Expected EOF, but found {}\n{}", found, info);
           }
       } 
    }

    fn parse_token(&mut self, tok: Token) -> Result<Lexeme<'s>, ()> {
        let correct_token = match self.stream.peek() {
            None => false,
            Some(lex) => lex.token == tok
        };
        if correct_token {
            let lex = self.stream.next().unwrap();
            Ok(lex)
        } else {
            Err(())
        }
    }

    fn parse_hole<Node, Val>(&mut self) -> Result<Term<Node, Val>, ()> {
        let lex = try!(self.parse_token(Token::Name));
        Ok(Term::Hole(format!("{}", lex.span)))
    }

    fn parse_node<Node>(&mut self) -> Result<Node, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        let node = try!(self.parse_token(Token::Name));
        Ok(Node::from_str(&format!("{}", node)).unwrap())
    }

    fn parse_stx<Node, Val>(&mut self) -> Result<Term<Node, Val>, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::LParen));
        let node = self.parse_node();
        let node = self.check("Node", node);
        let mut subterms = vec!();
        while let Ok(term) = self.parse_term() {
            subterms.push(term);
        }
        let _rp = self.parse_token(Token::RParen);
        self.check("Right Paren", _rp);
        Ok(Term::Stx(node, subterms))
    }

    fn parse_refn<Node, Val>(&mut self) -> Result<Term<Node, Val>, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        let lex = try!(self.parse_token(Token::Name));
        Ok(Term::Refn(Var::new(&format!("{}", lex))))
    }

    fn parse_decl<Node, Val>(&mut self) -> Result<Term<Node, Val>, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        let lex = try!(self.parse_token(Token::Name));
        Ok(Term::Decl(Var::new(&format!("{}", lex))))
    }

    fn parse_term<Node, Val>(&mut self) -> Result<Term<Node, Val>, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        Err(())
            .or_else(|_| self.parse_hole())
            .or_else(|_| self.parse_stx())
            .or_else(|_| self.parse_refn())
            .or_else(|_| self.parse_decl())
    }

    fn parse_rewrite_rule<Node, Val>(&mut self) -> Result<RewriteRule<Node, Val>, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::Rule));
        let lhs = self.parse_term();
        let lhs = self.check("Term", lhs);
        let arrow = self.parse_token(Token::Arrow);
        self.check("Arrow", arrow);
        let rhs = self.parse_term();
        let rhs = self.check("Term", rhs);
        Ok(RewriteRule::new(lhs, rhs))
    }

    fn parse_num(&mut self) -> Result<usize, ()>
    {
        let n = try!(self.parse_token(Token::Num));
        Ok(usize::from_str(n.span.as_str()).unwrap())
    }

    fn parse_fact_import<Node>(&mut self, node: Node) -> Result<Fact<Node>, ()>
        where Node: Copy + FromStr, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::Import));
        let i = self.parse_num();
        let i = self.check("Number", i);
        Ok(Fact::new(node, Child(i), Imp))
    }

    fn parse_fact_export<Node>(&mut self, node: Node) -> Result<Fact<Node>, ()>
        where Node: Copy + FromStr, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::Export));
        let i = self.parse_num();
        let i = self.check("Number", i);
        Ok(Fact::new(node, Exp, Child(i)))
    }

    fn parse_fact_sibling<Node>(&mut self, node: Node) -> Result<Fact<Node>, ()>
        where Node: Copy + FromStr, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::Bind));
        let i = self.parse_num();
        let i = self.check("Number", i);
        let _in = self.parse_token(Token::In);
        self.check("`in`", _in);
        let j = self.parse_num();
        let j = self.check("Number", j);
        Ok(Fact::new(node, Child(j), Child(i)))
    }

    fn parse_fact<Node>(&mut self, node: Node) -> Result<Fact<Node>, ()>
        where Node: Copy + FromStr, Node::Err: fmt::Debug
    {
        Err(())
            .or_else(|_| self.parse_fact_import(node))
            .or_else(|_| self.parse_fact_export(node))
            .or_else(|_| self.parse_fact_sibling(node))
    }

    fn parse_scope_rule<Node>(&mut self) -> Result<ScopeRule<Node>, ()>
        where Node: Copy + FromStr, Node::Err: fmt::Debug
    {
         panic!("NYI")
    }    
}

use std::iter::Peekable;
use std::str::FromStr;
use std::fmt;
use std::hash::Hash;

use parser::source::SourceFile;
use parser::lexer::{Lexeme, Token, Lexer};
use term::{Term, Var, RewriteRule};
use preorder::Elem::{Child, Imp, Exp};
use preorder::{Lt};
use rule::{ScopeRule, Language};



type Stream<'s> = Peekable<Lexer<'s>>;

pub struct Parser<'s> {
    stream: Peekable<Lexer<'s>>
}

impl<'s> Parser<'s> {
    fn new(lexer: Lexer<'s>) -> Parser<'s> {
        Parser{
            stream: lexer.peekable()
        }
    }

    pub fn from_source(src: &'s SourceFile) -> Parser<'s> {
        let lexer = Lexer::new(src);
        Parser::new(lexer)
    }

    fn check<T>(&mut self, expected: &str, result: Result<T, ()>) -> T {
        match result {
            Err(()) => {
                match self.stream.next() {
                    None => {
                        panic!("Expected {}, but found EOF", expected);
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

    pub fn parse_eof(&mut self) {
       match self.stream.peek() {
           None => (),
           Some(lex) => {
               let found = lex.span.as_str();
               let info = lex.span.preview(80);
               panic!("Found unexpected token {}\n{}", found, info);
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

    fn parse_name(&mut self) -> Result<String, ()>
    {
        let name = try!(self.parse_token(Token::Name));
        Ok(String::from(name.span.as_str()))
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
        self.check("End of rule", _rp);
        Ok(Term::Stx(node, subterms))
    }

    fn parse_refn<Node, Val>(&mut self) -> Result<Term<Node, Val>, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::RefnMark));
        let _lex = self.parse_token(Token::Name);
        let lex = self.check("Variable name", _lex);
        Ok(Term::Refn(Var::new(&format!("{}", lex))))
    }

    fn parse_decl<Node, Val>(&mut self) -> Result<Term<Node, Val>, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::DeclMark));
        let _lex = self.parse_token(Token::Name);
        let lex = self.check("Variable name", _lex);
        Ok(Term::Decl(Var::new(&format!("{}", lex))))
    }

    fn parse_global<Node, Val>(&mut self) -> Result<Term<Node, Val>, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::GlobalMark));
        let _lex = self.parse_token(Token::Name);
        let lex = self.check("Variable name", _lex);
        Ok(Term::Global(Var::new(&format!("{}", lex))))
    }

    pub fn parse_term<Node, Val>(&mut self) -> Result<Term<Node, Val>, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        Err(())
            .or_else(|_| self.parse_hole())
            .or_else(|_| self.parse_stx())
            .or_else(|_| self.parse_refn())
            .or_else(|_| self.parse_decl())
            .or_else(|_| self.parse_global())
    }

    pub fn parse_rewrite_rule<Node, Val>(&mut self) -> Result<RewriteRule<Node, Val>, ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::Rule));
        
        let lhs = self.parse_term();
        let lhs = self.check("Term (for rewrite rule LHS)", lhs);
        
        let arrow = self.parse_token(Token::Arrow);
        self.check("Arrow (for rewrite rule)", arrow);
        
        let rhs = self.parse_term();
        let rhs = self.check("Term (for rewrite rule RHS)", rhs);
        
        Ok(RewriteRule::new(lhs, rhs))
    }

    fn parse_num(&mut self) -> Result<usize, ()>
    {
        let n = try!(self.parse_token(Token::Num));
        Ok(usize::from_str(n.span.as_str()).unwrap())
    }
    
    fn parse_child_index(&mut self) -> usize
    {
        let i = self.parse_num();
        let i = self.check("Index of subterm", i);
        if i == 0 {
            panic!("Subterm index cannot be 0 (it is 1-indexed)")
        }
        i
    }

    fn parse_fact_import(&mut self) -> Result<Lt, ()>
    {
        try!(self.parse_token(Token::Import));
        let i = self.parse_child_index();
        Ok(Lt::new(Child(i), Imp))
    }

    fn parse_fact_export(&mut self) -> Result<Lt, ()>
    {
        try!(self.parse_token(Token::Export));
        let i = self.parse_child_index();
        Ok(Lt::new(Exp, Child(i)))
    }

    fn parse_fact_sibling(&mut self) -> Result<Lt, ()>
    {
        try!(self.parse_token(Token::Bind));
        
        let i = self.parse_child_index();
        
        let _in = self.parse_token(Token::In);
        self.check("`in`", _in);
        
        let j = self.parse_child_index();

        Ok(Lt::new(Child(j), Child(i)))
    }

    pub fn parse_fact(&mut self) -> Result<Lt, ()>
    {
        let fact = try!(Err(())
            .or_else(|_| self.parse_fact_import())
            .or_else(|_| self.parse_fact_export())
            .or_else(|_| self.parse_fact_sibling()));
        
        let _semi = self.parse_token(Token::Semicolon);
        self.check("Semicolon", _semi);
        
        Ok(fact)
    }
    
    fn parse_header<Node>(&mut self) -> Result<(Node, Vec<String>), ()>
        where Node: FromStr, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::LParen));

        let node = self.parse_node();
        let node = self.check("Node", node);

        let mut args = vec!();
        while let Ok(arg) = self.parse_name() {
            args.push(arg);
        }
        
        let _rp = self.parse_token(Token::RParen);
        self.check("Right paren", _rp);
        Ok((node, args))
    }

    fn parse_scope_rule<Node>(&mut self) -> Result<ScopeRule<Node>, ()>
        where Node: Clone + FromStr + fmt::Display, Node::Err: fmt::Debug
    {
        let (node, args) = try!(self.parse_header());
        
        let _lb = self.parse_token(Token::LBrace);
        self.check("Left brace", _lb);
        
        let mut facts = vec!();
        while let Ok(fact) = self.parse_fact() {
            facts.push(fact);
        }
        
        let _rb = self.parse_token(Token::RBrace);
        self.check("Left brace", _rb);
        
        Ok(ScopeRule::new_core(node, args, facts))
    }

    fn parse_sugar_decl<Node>(&mut self) -> Result<ScopeRule<Node>, ()>
        where Node: Clone + FromStr + fmt::Display, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::Sugar));
        let _header = self.parse_header();
        let (node, args) = self.check("Sugar declaration", _header);
        Ok(ScopeRule::new_surface(node, args))
    }

    pub fn parse_language<Node, Val>(&mut self) -> Result<Language<Node, Val>, ()>
        where Node: Clone + FromStr + Eq + Hash + fmt::Display, Node::Err: fmt::Debug
    {
        try!(self.parse_token(Token::Language));
        
        let name = self.parse_name();
        let name = self.check("Language name", name);
        
        let _lb = self.parse_token(Token::LBrace);
        self.check("Left brace", _lb);
        
        let mut core_scope = vec!();
        while let Ok(rule) = self.parse_scope_rule() {
            core_scope.push(rule);
        }
        let mut surf_scope = vec!();
        while let Ok(rule) = self.parse_sugar_decl() {
            surf_scope.push(rule);
        }
        let mut rewrite = vec!();
        while let Ok(rewrite_rule) = self.parse_rewrite_rule() {
            rewrite.push(rewrite_rule);
        }
        
        let _rb = self.parse_token(Token::RBrace);
        self.check("Left brace", _rb);
        
        Ok(Language::new(name, core_scope, surf_scope, rewrite))
    }
}

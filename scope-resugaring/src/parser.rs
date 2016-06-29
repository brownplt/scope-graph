use std::iter::Peekable;
use std::str::FromStr;
use std::fmt;
use std::ops::BitAnd;

use source::SourceFile;
use lexer::{Lexeme, Token, Lexer};
use term::{Term, Var, RewriteRule};

/*
struct Parser<'s, T> {
    parse: Box<Fn(&mut Peekable<Lexer<'s>>) -> Option<T>>
}
*/

trait Parser<'s> {
    type Ans;
    fn parse(&self, lexer: &mut Peekable<Lexer<'s>>) -> Option<Self::Ans>;

    fn seq<P>(self, other: P) -> Seq<Self, P> where Self: Sized, P: Parser<'s> {
        Seq{
            lhs: self,
            rhs: other
        }
    }
    
    fn opt<P>(self, other: P) -> Opt<Self, P> where Self: Sized, P: Parser<'s> {
        Opt{
            fst: self,
            snd: other
        }
    }
}

struct Seq<A, B> {
    lhs: A,
    rhs: B
}

impl<'s, A, B> Parser<'s> for Seq<A, B>
    where A: Parser<'s>, B: Parser<'s>
{
    type Ans = (A::Ans, B::Ans);
    fn parse(&self, lexer: &mut Peekable<Lexer<'s>>) -> Option<(A::Ans, B::Ans)> {
        match self.lhs.parse(lexer) {
            None => None,
            Some(a) => match self.rhs.parse(lexer) {
                None => None,
                Some(b) => Some((a, b))
            }
        }
    }
}

struct Opt<A, B> {
    fst: A,
    snd: B
}

impl<'s, A, B> Parser<'s> for Opt<A, B>
    where A: Parser<'s>, B: Parser<'s, Ans=A::Ans>
{
    type Ans = A::Ans;
    fn parse(&self, lexer: &mut Peekable<Lexer<'s>>) -> Option<A::Ans> {
        match self.fst.parse(lexer) {
            None => self.snd.parse(lexer),
            Some(a) => Some(a)
        }
    }
}

/*
fn seq<'s, A, B>(lhs: Parser<'s, A>, rhs: Parser<'s, B>) -> Parser<'s, (A, B)> {
    let parse = |lexer: &mut Peekable<Lexer<'s>>| {
        match (lhs.parse)(lexer) {
            None => None,
            Some(a) => match (rhs.parse)(lexer) {
                None => None,
                Some(b) => Some((a, b))
            }
        }
    };
    Parser{
        parse: Box::new(parse)
    }
}
*/


/*
pub fn parse<Node, Val>(source: &SourceFile) -> Vec<RewriteRule<Node, Val>> {
    panic!("NYI");
}

fn parse_term_opt<'s, Node, Val>(lexer: &mut Peekable<Lexer<'s>>)
                                 -> Option<Term<Node, Val>>
    where Node: FromStr, Node::Err: fmt::Debug
{
    let correct_token = match lexer.peek() {
        None => false,
        Some(lex) =>
            lex.token == Token::Name
            || lex.token == Token::LParen
            || lex.token == Token::DeclMark
            || lex.token == Token::RefnMark
    };
    if correct_token {
        let lex = lexer.next().unwrap();
        match lex.token {
            Token::Name => {
                Some(Term::Hole(format!("{}", lex.span)))
            }
            Token::LParen => {
                let node = parse_token(lexer, Token::Name);
                let node = Node::from_str(&format!("{}", node)).unwrap();
                let mut subterms = vec!();
                while let Some(term) = parse_term_opt(lexer) {
                    subterms.push(term);
                }
                parse_token(lexer, Token::RParen);
                Some(Term::Stx(node, subterms))
            }
            Token::DeclMark => {
                let var = parse_token(lexer, Token::Name);
                Some(Term::Decl(Var::new(&format!("{}", var))))
            }
            Token::RefnMark => {
                let var = parse_token(lexer, Token::Name);
                Some(Term::Refn(Var::new(&format!("{}", var))))
            }
            _ => panic!("Internal Error: parser")
        }
    } else {
        None
    }
}

fn parse_term<'s, Node, Val>(lexer: &mut Peekable<Lexer<'s>>)
                             -> Term<Node, Val>
    where Node: FromStr, Node::Err: fmt::Debug
{
    let term = parse_term_opt(lexer);
    expect(lexer, term, "Term")
}

fn parse_rewrite_rule<'s, Node, Val>(lexer: &mut Peekable<Lexer<'s>>)
                             -> Option<RewriteRule<Node, Val>>
    where Node: FromStr, Node::Err: fmt::Debug
{
    if parse_token_opt(lexer, Token::Rule).is_none() {
        return None
    }
    let lhs = parse_term(lexer);
    parse_token(lexer, Token::Arrow);
    let rhs = parse_term(lexer);
    Some(RewriteRule::new(lhs, rhs))
}

fn parse_token_opt<'s>(lexer: &mut Peekable<Lexer<'s>>, token: Token)
                       -> Option<Lexeme<'s>> {
    let correct_token = match lexer.peek() {
        None => false,
        Some(lex) => lex.token == token
    };
    if correct_token {
        let lex = lexer.next().unwrap();
        Some(lex)
    } else {
        None
    }
}

fn expect<'s, T>(lexer: &mut Peekable<Lexer<'s>>, opt: Option<T>, expected: &str) -> T {
    match opt {
        None => {
            match lexer.next() {
                None => panic!("Parser: Expected {}, but found EOF", expected),
                Some(lex) => panic!("Parser: Expected {}, but found {}", expected, lex.span)
            }
        }
        Some(val) => val
    }
}

fn parse_token<'s>(lexer: &mut Peekable<Lexer<'s>>, token: Token)
                   -> Lexeme<'s> {
    match lexer.next() {
        None => panic!("Parser: Expected {}, but found EOF", token),
        Some(lex) => {
            if lex.token == token {
                lex
            } else {
                panic!("Parser: Expected {}, but found {}", token, lex.span);
            }
        }
    }
}



//    fn new(left: Term<Node, Val>, right: Term<Node, Val>) -> RewriteRule<Node, Val> {
*/

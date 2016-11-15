use std::fmt;

use regex::Regex;
use parser::source::{Pos, Span, SourceFile};

use self::Token::*;


#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Token {
    // Language
    Language,
    // Punctuation
    Semicolon,
    LBrace,
    RBrace,
    // Scoping Rules
    Sugar,
    Colon,
    Bind,
    In,
    Import,
    Export,
    // Desugaring Rules
    Rule,
    Arrow,
    // Terms
    LParen,
    RParen,
    DeclMark,
    RefnMark,
    GlobalMark,
    Num,
    Name
}


fn make_matcher(token: Token, regex: &str) -> (Token, Regex) {
    (token, Regex::new(&(String::from("^") + regex)).unwrap())
}

lazy_static! {
    static ref MATCHERS: [(Token, Regex); 19] = [
        make_matcher(Language, "language\\b"),
        make_matcher(Semicolon, ";"),
        make_matcher(LBrace  , "\\{"),
        make_matcher(RBrace  , "\\}"),
        make_matcher(Sugar   , "sugar"),
        make_matcher(Colon   , ":"),
        make_matcher(LParen  , "\\("),
        make_matcher(RParen  , "\\)"),
        make_matcher(Rule    , "rule"),
        make_matcher(Arrow   , "=>"),
        make_matcher(Bind    , "bind\\b"),
        make_matcher(In      , "in\\b"),
        make_matcher(Import  , "import\\b"),
        make_matcher(Export  , "export\\b"),
        make_matcher(DeclMark, "@"),
        make_matcher(RefnMark, "\\$"),
        make_matcher(GlobalMark, "global$"),
        make_matcher(Num     , "[0-9]+"),
        make_matcher(Name    , "[_a-zA-Z][a-zA-Z_0-9-]*")
        ];
    static ref WS_MATCHER: Regex = Regex::new("^([ \t\r\n]|\\(\\*[^\\*]*\\*\\))*").unwrap();
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Language => write!(f, "language"),
            Semicolon => write!(f, ";"),
            LBrace   => write!(f, "{{"),
            RBrace   => write!(f, "}}"),
            Sugar    => write!(f, "sugar"),
            Colon    => write!(f, ":"),
            LParen   => write!(f, "("),
            RParen   => write!(f, ")"),
            Rule     => write!(f, "rule"),
            Arrow    => write!(f, "=>"),
            Bind     => write!(f, "bind"),
            In       => write!(f, "in"),
            Import   => write!(f, "import"),
            Export   => write!(f, "export"),
            DeclMark => write!(f, "@"),
            RefnMark => write!(f, "$"),
            GlobalMark => write!(f, "global$"),
            Num      => write!(f, "[NUM]"),
            Name     => write!(f, "[NAME]")
        }
    }
}

pub struct Lexeme<'s> {
    pub token: Token,
    pub span: Span<'s>
}
impl<'s> fmt::Display for Lexeme<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.span.fmt(f)
    }
}

pub struct Lexer<'s> {
    source: &'s SourceFile,
    ptr: &'s str,
    pos: Pos
}

impl<'s> Lexer<'s> {
    pub fn new(source: &'s SourceFile) -> Lexer<'s> {
        let mut lexer = Lexer{
            source: source,
            ptr: &source.text,
            pos: Pos::new(0)
        };
        lexer.trim_ws();
        lexer
    }

    fn at_eof(&self) -> bool {
        self.ptr.is_empty()
    }

    fn match_span(&self, len: usize) -> Span<'s> {
        Span::new(self.source, self.pos, self.pos + len)
    }

    fn match_regex(&self, regex: &Regex) -> Option<Span<'s>> {
        regex.find(self.ptr).map(|(i, j)| {
            if i != 0 {
                panic!("Internal error: regex match not at start of str.")
            }
            self.match_span(j)
        })
    }

    fn trim_ws(&mut self) {
        match self.match_regex(&WS_MATCHER) {
            None => (),
            Some(span) => self.consume(span)
        }
    }

    fn consume(&mut self, span: Span) {
        let len = span.len();
        self.ptr = &self.ptr[len ..];
        self.pos = self.pos + len;
    }
}

impl<'s> Iterator for Lexer<'s> {
    type Item = Lexeme<'s>;
    fn next(&mut self) -> Option<Lexeme<'s>> {
        if self.at_eof() {
            return None;
        }
        for &(ref token, ref regex) in MATCHERS.iter() {
            match self.match_regex(regex) {
                None => (),
                Some(span) => {
                    self.consume(span);
                    self.trim_ws();
                    return Some(Lexeme{ token: *token, span: span });
                }
            }
        }
        let loc = self.source.pos_to_loc(self.pos);
        panic!("Lexer: Could not recognize next token, at {}", loc);
    }
}

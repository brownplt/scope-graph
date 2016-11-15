use std::fmt;
use std::ops::Index;
use std::collections::HashMap;

use self::Term::*;


pub type Name = String;
pub type Node = String;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Var {
    pub name: Name,
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Var {
    pub fn new(name: &str) -> Var {
        let name = String::from(name);
        Var{
            name: name,
        }
    }
}


pub enum Term<Val> {
    Decl(Var),
    Refn(Var),
    Global(Var),
    Value(Val),
    Stx(Node, Vec<Term<Val>>),
    Hole(Name)
}

impl<Val> fmt::Display for Term<Val> where Val : fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Decl(ref var) => write!(f, "@{}", var),
            &Refn(ref var) => write!(f, "${}", var),
            &Global(ref var) => write!(f, "global${}", var),
            &Value(ref val) => val.fmt(f),
            &Stx(ref node, ref subterms) => {
                try!(write!(f, "("));
                try!(write!(f, "{}", node));
                for subterm in subterms.iter() {
                    try!(write!(f, " {}", subterm));
                }
                write!(f, ")")
            }
            &Hole(ref hole) => write!(f, "{}", hole)
        }
    }
}

impl<Val> Term<Val> {
    pub fn child(&self, i: usize) -> &Term<Val> where Val : fmt::Display {
        match self {
            &Stx(_, ref subterms) => {
                match subterms.get(i - 1) {
                    None => panic!("Internal error! Term child index out of bounds: {}", i),
                    Some(term) => term
                }
            }
            _ => panic!("Internal error! Term has no children {}", self)
        }
    }

    pub fn is_hole(&self) -> bool {
        match self {
            &Hole(_) => true,
            _        => false
        }
    }

    pub fn vars(&self) -> Vec<Path> {
        fn recur<Val>(term: &Term<Val>, path: &mut Vec<usize>, vars: &mut Vec<Path>) {
            match term {
                &Hole(_) => (),
                &Decl(_)   => vars.push(path.clone()),
                &Refn(_)   => vars.push(path.clone()),
                &Global(_) => (), // Does not partipate in hygiene (cannot be bound by a decl)
                &Value(_)  => (),
                &Stx(_, ref subterms) => {
                    for (i, subterm) in subterms.iter().enumerate() {
                        path.push(i + 1);
                        recur(subterm, path, vars);
                        path.pop();
                    }
                }
            }
        }
        let mut vars = vec!();
        recur(self, &mut vec!(), &mut vars);
        vars
    }

    pub fn holes(&self) -> HashMap<Name, Path> {
        fn recur<Val>(term: &Term<Val>, path: &mut Vec<usize>, holes: &mut HashMap<Name, Path>) {
            match term {
                &Decl(_)  => (),
                &Refn(_)  => (),
                &Global(_)=> (),
                &Value(_) => (),
                &Stx(_, ref subterms) => {
                    for (i, subterm) in subterms.iter().enumerate() {
                        path.push(i + 1);
                        recur(subterm, path, holes);
                        path.pop();
                    }
                }
                &Hole(ref hole) => {
                    if holes.contains_key(hole) {
                        panic!("Rewrite rule contains duplicate hole: {}", hole);
                    }
                    holes.insert(hole.clone(), path.clone());
                }
            }
        }
        let mut holes = HashMap::new();
        recur(self, &mut vec!(), &mut holes);
        holes
    }
}

pub type Path = Vec<usize>;

impl<'a, Val> Index<&'a Path> for Term<Val> where Val : fmt::Display {
    type Output = Term<Val>;
    fn index(&self, path: &'a Path) -> &Term<Val> {
        let mut t = self;
        for &i in path.iter() {
            t = t.child(i);
        }
        t
    }
}

pub struct RewriteRule<Val> {
    pub left: Term<Val>,
    pub right: Term<Val>,
    pub holes: HashMap<Name, (Path, Path)>
}

impl<Val> RewriteRule<Val> {
    pub fn new(left: Term<Val>, right: Term<Val>) -> RewriteRule<Val> {
        if left.is_hole() {
            panic!("The LHS of a rewrite rule cannot be just a hole.");
        }
        if left.is_hole() || right.is_hole() {
            panic!("The RHS of a rewrite rule cannot be just a hole.");
        }
        let left_holes = left.holes();
        let mut right_holes = right.holes();
        for hole in right_holes.keys() {
            if !left_holes.contains_key(hole) {
                panic!("Rewrite rule has undefined hole: {}", hole);
            }
        }
        let mut holes = HashMap::new();
        for (hole, lpath) in left_holes.into_iter() {
            match right_holes.remove(&hole) {
                Some(rpath) => {
                    holes.insert(hole, (lpath, rpath));
                }
                None => {}
            }
        }
        holes.insert(String::from(""), (vec!(), vec!()));
        RewriteRule{
            left: left,
            right: right,
            holes: holes
        }
    }
}

impl<Val> fmt::Display for RewriteRule<Val> where Val : fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} => {}", self.left, self.right)
    }
}

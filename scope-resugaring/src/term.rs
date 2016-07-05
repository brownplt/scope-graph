use std::fmt;
use std::collections::HashMap;

use self::Term::*;
use self::Path::*;


pub type Name = String;

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


pub enum Term<Node, Val> {
    Decl(Var),
    Refn(Var),
    Value(Val),
    Stx(Node, Vec<Term<Node, Val>>),
    Hole(Name)
}

impl<Node, Val> fmt::Display for Term<Node, Val>
    where Node: fmt::Display, Val: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Decl(ref var) => var.fmt(f),
            &Refn(ref var) => var.fmt(f),
            &Value(ref val) => val.fmt(f),
            &Stx(ref node, ref subterms) => {
                try!(write!(f, "("));
                try!(write!(f, "{}", node));
                for subterm in subterms.iter() {
                    try!(write!(f, " {}", subterm));
                }
                write!(f, ")")
            }
            &Hole(ref hole) => write!(f, "@{}", hole)
        }
    }
}

impl<Node, Val> Term<Node, Val> {
    pub fn child(&self, i: usize) -> &Term<Node, Val>
        where Node: fmt::Display, Val: fmt::Display
    {
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

    fn holes(&self) -> HashMap<Name, Path> {
        fn recur<Node, Val>(term: &Term<Node, Val>, path: &mut Vec<usize>, holes: &mut HashMap<Name, Path>) {
            match term {
                &Decl(_)  => (),
                &Refn(_)  => (),
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
                    holes.insert(hole.clone(), PathToHole(path.clone()));
                }
            }
        }
        let mut holes = HashMap::new();
        recur(self, &mut vec!(), &mut holes);
        holes
    }
}

pub enum Path {
    PathToRoot,
    PathToHole(Vec<usize>)
}

impl Path {
    pub fn is_empty_path(&self) -> bool {
        match self {
            &PathToRoot => false,
            &PathToHole(ref path) => path.is_empty()
        }
    }

    pub fn is_root_path(&self) -> bool {
        match self {
            &PathToRoot => true,
            &PathToHole(_) => false
        }
    }
}

pub struct RewriteRule<Node, Val> {
    pub left: Term<Node, Val>,
    pub right: Term<Node, Val>,
    pub holes: HashMap<Name, (Path, Path)>
}

impl<Node, Val> RewriteRule<Node, Val> {
    pub fn new(left: Term<Node, Val>, right: Term<Node, Val>) -> RewriteRule<Node, Val> {
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
        holes.insert(String::from(""), (PathToRoot, PathToRoot));
        RewriteRule{
            left: left,
            right: right,
            holes: holes
        }
    }
}

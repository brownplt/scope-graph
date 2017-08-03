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


// Represents both terms (described in section 3.1) and contexts (section 5.1)
#[derive(Clone)]
pub enum Term<Val> {
    Decl(Var),
    Refn(Var),
    Global(Var),
    Value(Val),
    Stx(Node, Vec<Term<Val>>),
    Hole(Name),
    HoleToRefn(Name),
    Ellipsis
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
            &Hole(ref hole) => write!(f, "{}", hole),
            &HoleToRefn(ref hole) => write!(f, "as_refn${}", hole),
            &Ellipsis => write!(f, "...")
        }
    }
}

impl<Val> Term<Val> {
    // Find the `i`th child of this term (assumes that `i` is in range).
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

    // Is this context simply a hole?
    pub fn is_hole(&self) -> bool {
        match self {
            &Hole(_) => true,
            _        => false
        }
    }

    // Gives the source locations of all variables in a term or context
    pub fn vars(&self) -> Vec<Path> {
        fn recur<Val>(term: &Term<Val>, path: &mut Vec<usize>, vars: &mut Vec<Path>) {
            match term {
                &Hole(_) => (),
                &Decl(_)   => vars.push(path.clone()),
                &Refn(_)   => vars.push(path.clone()),
                &Global(_) => (), // Does not partipate in hygiene (cannot be bound by a decl)
                &HoleToRefn(_) => (),
                &Value(_)  => (),
                &Ellipsis  => (),
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

    // Gives the name and source location of each hole in a context
    pub fn holes(&self) -> HashMap<Name, Path> {
        self.holes_info().into_iter().map(|(hole, info)| (hole, info.0)).collect()
    }
    
    // Gives the name and source location and ellipses depth of each hole in a context
    fn holes_info(&self) -> HashMap<Name, (Path, usize)> {
        fn recur<Val>(term: &Term<Val>,
                      path: &mut Vec<usize>,
                      depth: usize,
                      holes: &mut HashMap<Name, (Path, usize)>) {
            match term {
                &Decl(_)  => (),
                &Refn(_)  => (),
                &Global(_)=> (),
                &Value(_) => (),
                &Ellipsis => (),
                &Stx(_, ref subterms) => {
                    let depth = match subterms.last() {
                        Some(&Ellipsis) => depth + 1,
                        _               => depth
                    };
                    for (i, subterm) in subterms.iter().enumerate() {
                        path.push(i + 1);
                        recur(subterm, path, depth, holes);
                        path.pop();
                    }
                }
                &HoleToRefn(_) => (),
                &Hole(ref hole) => {
                    if holes.contains_key(hole) {
                        panic!("Rewrite rule contains duplicate hole: {}", hole);
                    }
                    holes.insert(hole.clone(), (path.clone(), depth));
                }
            }
        }
        let mut holes = HashMap::new();
        recur(self, &mut vec!(), 0, &mut holes);
        holes
    }

    // Gives the name and source location of each `as_refn` hole in a context
    pub fn hole_as_refns(&self) -> HashMap<Name, Path> {
        fn recur<Val>(term: &Term<Val>, path: &mut Vec<usize>, holes: &mut HashMap<Name, Path>) {
            match term {
                &Decl(_)  => (),
                &Refn(_)  => (),
                &Global(_)=> (),
                &Value(_) => (),
                &Hole(_)  => (),
                &Ellipsis => (),
                &Stx(_, ref subterms) => {
                    for (i, subterm) in subterms.iter().enumerate() {
                        path.push(i + 1);
                        recur(subterm, path, holes);
                        path.pop();
                    }
                }
                &HoleToRefn(ref hole) => {
                    holes.insert(hole.clone(), path.clone());
                }
            }
        }
        let mut holes = HashMap::new();
        recur(self, &mut vec!(), &mut holes);
        holes
    }

    pub fn expand(&self) -> Term<Val> where Val : Clone {
        match self {
            &Stx(ref node, ref subterms) => {
                Stx(node.clone(),
                    subterms.iter().map(|subterm| {
                        match subterm {
                            &Ellipsis => {
                                self.ellipsis_copy()
                            },
                            _ => subterm.expand()
                        }
                    }).collect())
            }
            _ => self.clone()
        }
    }

    fn ellipsis_copy(&self) -> Term<Val> where Val : Clone {
        match self {
            &Hole(ref hole) =>
                Hole(hole.to_string() + "*"),
            &HoleToRefn(ref hole) =>
                HoleToRefn(hole.to_string() + "*"),
            &Ellipsis => Stx("End".to_string(), vec!()),
            &Stx(ref node, ref subterms) => {
                Stx(node.clone(),
                    subterms.iter().map(|subterm| {
                        subterm.ellipsis_copy()
                    }).collect())
            }
            &Decl(_)  => self.clone(),
            &Refn(_)  => self.clone(),
            &Global(_)=> self.clone(),
            &Value(_) => self.clone(),
        }
    }
}

// A source location
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

// A desugaring rule that says to rewrite context `left` to context `right`.
// (`holes` is cached info about the contexts' holes.)
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
        let left_holes = left.holes_info();
        let mut right_holes = right.holes_info();
        for hole in right_holes.keys() {
            if !left_holes.contains_key(hole) {
                panic!("Rewrite rule has undefined hole: {}", hole);
            }
        }
        let mut holes = HashMap::new();
        for (hole, (lpath, ldepth)) in left_holes.into_iter() {
            match right_holes.remove(&hole) {
                Some((rpath, rdepth)) => {
                    if ldepth != rdepth {
                        panic!("Hole `{}` used both under {} ellipses and under {} ellipses. Holes must be used at consistent ellipsis depth.", hole, ldepth, rdepth);
                    }
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

    pub fn expand(&self) -> RewriteRule<Val> where Val : Clone + fmt::Display {
        RewriteRule::new(self.left.expand(), self.right.expand())
    }
}

impl<Val> fmt::Display for RewriteRule<Val> where Val : fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} => {}", self.left, self.right)
    }
}

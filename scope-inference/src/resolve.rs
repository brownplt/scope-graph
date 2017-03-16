use std::collections::{HashSet, HashMap};
use std::fmt;

use rule::{ScopeRules};
use term::{Name, Var, Term, Path};
use term::Term::*;
use preorder::Elem::*;
use infer::gen_conj;


#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Elem {
    Imp,
    Exp,
    Decl(Var, Path),
    Refn(Var, Path),
    Hole(Name)
}

impl fmt::Display for Elem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Elem::Imp => write!(f, "{}", Imp),
            &Elem::Exp => write!(f, "{}", Exp),
            &Elem::Decl(ref v, _) => v.fmt(f),
            &Elem::Refn(ref v, _) => v.fmt(f),
            &Elem::Hole(ref n) => n.fmt(f)
        }
    }
}

impl Elem {
    fn path(&self) -> &Path {
        match self {
            &Elem::Decl(_, ref path) => path,
            &Elem::Refn(_, ref path) => path,
            _ => panic!("Internal Error: Resolve::Elem::path expected variable")
        }
    }

    fn name(&self) -> &Var {
        match self {
            &Elem::Decl(ref name, _) => name,
            &Elem::Refn(ref name, _) => name,
            _ => panic!("Internal Error: Resolve::Elem::name expected variable")
        }
    }
}

enum Side { Left, Right }
use self::Side::*;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Lt {
    pub left: Elem,
    pub right: Elem
}

impl Lt {
    fn new(left: Elem, right: Elem) -> Lt {
        Lt{
            left: left,
            right: right
        }
    }
}

fn min(set: Vec<Elem>, order: &HashSet<Lt>) -> Vec<Elem> {
    let mut mins = vec!();
    for (i, elem) in set.iter().enumerate() {
        let mut small = true;
        for (j, other) in set.iter().enumerate() {
            if i != j && order.contains(&Lt::new(other.clone(), elem.clone())) {
                small = false;
            }
        }
        if small {
            mins.push(elem.clone());
        }
    }
    mins
}

pub fn resolve_bindings<Val>(scope: &ScopeRules, term: &Term<Val>)
                            -> HashMap<Path, (Var, Vec<Path>)>
    where Val : fmt::Display
{
    let scope = resolve_scope(scope, term);

    let mut decls = vec!();
    let mut refns = vec!();
    for path in term.vars().into_iter() {
        let var = &term[&path];
        match var {
            &Decl(ref name) => decls.push(Elem::Decl(name.clone(), path)),
            &Refn(ref name) => refns.push(Elem::Refn(name.clone(), path)),
            _ => panic!("Internal Error: Resolve::resolve_bindings - expected variable")
        }
    }

    let mut bindings: HashMap<Path, (Var, Vec<Path>)> = HashMap::new();
    for refn in refns.iter() {
        let mut possible_binders = vec!();
        for decl in decls.iter() {
            if refn.name() == decl.name()
                && scope.contains(&Lt::new(refn.clone(), decl.clone())) {
                    possible_binders.push(decl.clone());
                }
        }
        let mut binders = vec!();
        for binder in min(possible_binders, &scope).into_iter() {
            binders.push(binder.path().clone());
        }
        bindings.insert(refn.path().clone(), (refn.name().clone(), binders));
    }
    bindings
}

pub fn resolve_hole_order<Val>(scope: &ScopeRules, term: &Term<Val>)
                               -> HashSet<Lt>
    where Val : fmt::Display
{
    let mut order = HashSet::new();
    let mut holes = term.holes();
    holes.insert("".to_string(), vec!());

    for (ref hole1, ref path1) in holes.iter() {
        for (ref hole2, ref path2) in holes.iter() {
            if resolve_lt(scope, term, path1, path2) {
                order.insert(Lt::new(hole_to_elem(hole1, Left),
                                     hole_to_elem(hole2, Right)));
            }
        }
    }
    order
}

fn resolve_scope<Val>(scope: &ScopeRules, term: &Term<Val>)
                          -> HashSet<Lt>
    where Val : fmt::Display
{
    let mut order = HashSet::new();
    let mut vars = term.vars();
    vars.push(vec!());

    for x in vars.iter() {
        for y in vars.iter() {
            if resolve_lt(scope, term, x, y) {
                order.insert(Lt::new(var_to_elem(&term[x], x, Left),
                                     var_to_elem(&term[y], y, Right)));
            }
        }
    }
    order
}

// Determine weather one variable (or hole) in a term is less than other,
// given a set of scoping rules.
pub fn resolve_lt<Val>(scope: &ScopeRules, term: &Term<Val>, var1: &[usize], var2: &[usize]) -> bool
    where Val : fmt::Display
{
    let conj = gen_conj(term, var1, var2);
    for ref fact in conj.iter() {
        if !scope.satisfied(fact) {
            return false;
        }
    }
    true
}

fn hole_to_elem(hole: &Name, side: Side) -> Elem {
    match (&hole == &"", side) {
        (false, _) => Elem::Hole(hole.to_string()),
        (true, Left) => Elem::Exp,
        (true, Right) => Elem::Imp
    }
}

fn var_to_elem<Val>(var_term: &Term<Val>, path: &Path, side: Side) -> Elem {
    match (path == &[], side) {
        (true, Left) => Elem::Exp,
        (true, Right) => Elem::Imp,
        (false, _) => {
            match var_term {
                &Decl(ref var) => Elem::Decl(var.clone(), path.clone()),
                &Refn(ref var) => Elem::Refn(var.clone(), path.clone()),
                _ => panic!("Internal error: resolve::var_to_elem - invalid variable")
            }
        }
    }
}

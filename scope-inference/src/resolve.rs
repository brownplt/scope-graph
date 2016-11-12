use std::collections::{HashSet, HashMap};
use std::ops::Index;
use std::hash::Hash;
use std::fmt;

use rule::{ScopeRule, ScopeRules};
use term::{Name, Node, Var, Term, Path, RewriteRule};
use term::Term::*;
use preorder::Elem::*;


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

pub fn resolve_binding<Val>(scope: &ScopeRules, term: &Term<Val>)
                            -> HashMap<Path, (Var, Vec<Path>)> {
    let scope = resolve_scope(scope, term);
    let mut shadows: HashSet<(Path, Path)> = HashSet::new();
    let mut in_scope: HashSet<(Path, Path)> = HashSet::new();
    let mut decl_names: HashMap<Path, Var> = HashMap::new();
    let mut refn_names: HashMap<Path, Var> = HashMap::new();
    let mut bound: HashMap<Path, (Var, Vec<Path>)> = HashMap::new();

    for lt in scope.into_iter() {
        match &lt.left {
            &Elem::Decl(ref name, ref path) => {
                decl_names.insert(path.clone(), name.clone());
            },
            &Elem::Refn(ref name, ref path) => {
                refn_names.insert(path.clone(), name.clone());
            },
            _ => ()
        }
        match &lt.right {
            &Elem::Decl(ref name, ref path) => {
                decl_names.insert(path.clone(), name.clone());
            },
            &Elem::Refn(ref name, ref path) => {
                refn_names.insert(path.clone(), name.clone());
            },
            _ => ()
        }
        match (lt.left, lt.right) {
            (Elem::Decl(name_a, a), Elem::Decl(name_b, b)) => {
                if name_a == name_b {
                    shadows.insert((a, b));
                }
            }
            (Elem::Refn(name_a, a), Elem::Decl(name_b, b)) => {
                if name_a == name_b {
                    in_scope.insert((a, b));
                }
            }
            _ => ()
        }
    }

    for refn in refn_names.keys() {
        let mut binders: Vec<Path> = vec!();
        for decl in decl_names.keys() {
            if in_scope.contains(&(refn.clone(), decl.clone())) {
                let mut shadowed = false;
                for decl2 in decl_names.keys() {
                    if in_scope.contains(&(refn.clone(), decl2.clone())) &&
                        shadows.contains(&(decl2.clone(), decl.clone()))
                    {
                        shadowed = true;
                    }
                }
                if !shadowed {
                    binders.push(decl.clone());
                }
            }
        }
        bound.insert(refn.clone(), (refn_names[refn].clone(), binders));
    }
    bound
}

pub fn resolve_hole_order<Val>(scope: &ScopeRules, term: &Term<Val>)
                               -> HashSet<Lt> {
    let mut set = HashSet::new();
    for lt in resolve_scope(scope, term).into_iter() {
        match (&lt.left, &lt.right) {
            (&Elem::Hole(_), &Elem::Imp) => {
                set.insert(lt);
            }
            (&Elem::Exp, &Elem::Hole(_)) => {
                set.insert(lt);
            }
            (&Elem::Hole(_), &Elem::Hole(_)) => {
                set.insert(lt);
            }
            _ => ()
        }
    }
    set
}

fn resolve_scope<Val>(scope: &ScopeRules, term: &Term<Val>)
                          -> HashSet<Lt> {
    let mut order = HashSet::new();
    let mut resolved = resolve(scope, term, &vec!());
    if resolved.refl {
        order.insert(Lt::new(Elem::Exp, Elem::Imp));
    }
    for a in resolved.imps.into_iter() {
        order.insert(Lt::new(a, Elem::Imp));
    }
    for b in resolved.exps.into_iter() {
        order.insert(Lt::new(Elem::Exp, b));
    }
    for (a, b) in resolved.order.into_iter() {
        order.insert(Lt::new(a, b));
    }
    order
}

struct Resolved {
    imps: HashSet<Elem>,
    exps: HashSet<Elem>,
    order: HashSet<(Elem, Elem)>,
    refl: bool
}

fn resolve<Val>(scope: &ScopeRules, term: &Term<Val>, path: &Path)
                -> Resolved {
    let mut ans = Resolved{
        imps: HashSet::new(),
        exps: HashSet::new(),
        order: HashSet::new(),
        refl: false
    };
    match term {
        &Decl(ref v) => {
            let t = Elem::Decl(v.clone(), path.clone());
            ans.imps.insert(t.clone());
            ans.exps.insert(t);
        }
        &Refn(ref v) => {
            let t = Elem::Refn(v.clone(), path.clone());
            ans.imps.insert(t.clone());
            ans.exps.insert(t);
        }
        &Hole(ref n) => {
            let t = Elem::Hole(n.clone());
            ans.imps.insert(t.clone());
            ans.exps.insert(t);
        }
        &Global(_) => (),
        &Value(_) => (),
        &Stx(ref node, ref subterms) => {
            let ref rule = scope[node.as_str()];
            let mut resolveds: Vec<Resolved> = vec!();
            for (i, term) in subterms.iter().enumerate() {
                let mut path = path.clone();
                path.push(i);
                resolveds.push(resolve(scope, term, &path));
            }
            for fact in rule.iter() {
                match (fact.left, fact.right) {
                    (Child(i), Imp) => {
                        for a in resolveds[i - 1].imps.iter() {
                            ans.imps.insert(a.clone());
                        }
                    }
                    (Exp, Child(j)) => {
                        for b in resolveds[j - 1].exps.iter() {
                            ans.exps.insert(b.clone());
                        }
                    }
                    (Child(i), Child(j)) => {
                        for a in resolveds[i - 1].imps.iter() {
                            for b in resolveds[j - 1].exps.iter() {
                                ans.order.insert((a.clone(), b.clone()));
                            }
                        }
                    }
                    (Exp, Imp) => {
                        ans.refl = true;
                    }
                    _ => panic!("Internal error: Invalid scope rule found during scope resolution")
                }
            }
            for resolved in resolveds.into_iter() {
                for (a, b) in resolved.order.into_iter() {
                    ans.order.insert((a, b));
                }
            }
        }
    }
    ans
}


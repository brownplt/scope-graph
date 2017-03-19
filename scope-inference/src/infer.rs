use std::fmt;
use std::collections::HashSet;
use std::collections::HashMap;

use util::display_sep;
use preorder::Elem::{Imp, Exp, Child};
use rule::{Fact, Conj, ScopeRules, Language};
use term::{RewriteRule, Term, Name};
use term::Term::*;
use resolve;
use resolve::{resolve_hole_order, resolve_bindings, resolve_lt, resolve_disj};



#[derive(Clone)]
pub struct Constraint {
    left: Conj,
    right: Conj
}

impl Constraint {
    fn new(left: Conj, right: Conj) -> Constraint {
        Constraint{
            left: left,
            right: right
        }
    }
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(display_sep(f, " & ", self.left.iter()));
        try!(write!(f, "   iff   "));
        display_sep(f, " & ", self.right.iter())
    }
}

pub fn gen_constrs<Val>(rule: &RewriteRule<Val>) -> Vec<Constraint>
    where Val : fmt::Display
{
    let mut constraints = vec!();
    let mut holes: Vec<&String> = rule.holes.keys().collect();
    holes.sort(); // Put in order for easy testing.
    for hole_1 in holes.iter() {
        for hole_2 in holes.iter() {
            let (ref lpath_1, ref rpath_1) = rule.holes[hole_1.as_str()];
            let (ref lpath_2, ref rpath_2) = rule.holes[hole_2.as_str()];
            constraints.push(Constraint::new(
                gen_conj(&rule.left,  lpath_1, lpath_2),
                gen_conj(&rule.right, rpath_1, rpath_2)));
        }
    }
    constraints
}

pub fn gen_conj<Val>(term: &Term<Val>, a: &[usize], b: &[usize]) -> Conj
    where Val : fmt::Display
{
    // true: downarrow, false: uparrow
    fn gen<Val>(term: &Term<Val>, a: &[usize], b: &[usize], conj: &mut Vec<Fact>)
        where Val : fmt::Display
    {
        match term {
            &Stx(ref node, _) => {
                match (a.first(), b.first()) {
                    (None, None) => {
                        // S-Self
                        conj.push(Fact::new(node.clone(), Exp, Imp));
                    }
                    (None, Some(&b0)) => {
                        // SA-Child
                        conj.push(Fact::new(node.clone(), Exp, Child(b0)));
                        gen(term.child(b0), &[], &b[1..], conj);
                    }
                    (Some(&a0), None) => {
                        // SA-Parent
                        conj.push(Fact::new(node.clone(), Child(a0), Imp));
                        gen(term.child(a0), &a[1..], &[], conj);
                    }
                    (Some(&a0), Some(&b0)) => {
                        if a0 == b0 && !term.child(a0).is_hole() {
                            // S-Lift
                            gen(term.child(a0), &a[1..], &b[1..], conj);
                        } else {
                            // SA-Sibling
                            conj.push(Fact::new(node.clone(), Child(a0), Child(b0)));
                            gen(term.child(a0), &a[1..], &[], conj);
                            gen(term.child(b0), &[], &b[1..], conj);
                        }
                    }
                }
            },
            &Hole(_) => {
                if !(a.is_empty() && b.is_empty()) {
                    panic!("Internal error! Generate conjunction: bad path to hole {:?} {:?}",
                           a, b);
                }
                // Assuming (Exp <. Imp) for all terms t
                // by Scope Rule axiom 4 (section 4.4)
            }
            _ => ()
        }
    }
    let mut conj = vec!();
    gen(term, a, b, &mut conj);
    conj
}


fn solve(core_scope: &ScopeRules,
               surf_scope: &mut ScopeRules,
               cs: Vec<Constraint>) {

    #[derive(Debug)]
    struct FactPosn {
        index: usize, // Index of constraint
        side: Side    // LHS vs. RHS of constraint
    }

    #[derive(Debug)]
    enum Side { Left, Right }


    struct Equation {
        left: HashSet<Fact>,
        right: HashSet<Fact>
    }


    // Setup efficient representation of constraints.
    // fact_posns: gives the constraints that a fact appears in
    // equations:  the constraints (with conjunctions repr as sets for efficiency)
    let mut fact_posns: HashMap<Fact, Vec<FactPosn>> = HashMap::new();
    let mut equations: Vec<Equation> = vec!();
    for (i, c) in cs.into_iter().enumerate() {
        let left_facts  =  c.left.into_iter().map(|fact| { (fact, Side::Left)  });
        let right_facts = c.right.into_iter().map(|fact| { (fact, Side::Right) });
        let mut equation = Equation{ left: HashSet::new(), right: HashSet::new() };
        for (fact, side) in left_facts.chain(right_facts) {
            match side {
                Side::Left  => {
                    equation.left.insert(fact.clone());
                }
                Side::Right => {
                    equation.right.insert(fact.clone());
                }
            }
            let posn = FactPosn{
                index: i,
                side: side
            };
            match fact_posns.remove(&fact) {
                None => {
                    fact_posns.insert(fact, vec!(posn));
                }
                Some(mut posns) => {
                    posns.push(posn);
                    fact_posns.insert(fact, posns);
                }
            }
        }
        equations.push(equation);
    }

    // Initialize Sigma_surf = Sigma_core (frontier is implicitly part of Sigma_surf)
    let mut frontier: Vec<Fact> = vec!();
    for rule in core_scope.rules.values() {
        for fact in rule.iter() {
            frontier.push(fact);
        }
    }

    // Add facts from constraints that have a side that's *initially* empty
    for eqn in equations.iter_mut() {
        if eqn.left.is_empty() {
            for fact in eqn.right.drain() {
                frontier.push(fact);
            }
        }
        if eqn.right.is_empty() {
            for fact in eqn.left.drain() {
                frontier.push(fact);
            }
        }
    }
    
    while let Some(fact) = frontier.pop() {
        // Maintain transitive closure
        for trans_closure_fact in surf_scope.insert(fact.clone()) {
            frontier.push(trans_closure_fact);
        }
        // If a fact in a constraint is in Sigma_surf
        match fact_posns.remove(&fact) {
            None => (),
            Some(posns) => {
                for posn in posns.into_iter() {
                    match posn.side {
                        Side::Left => {
                            // Delete it from the constraint
                            equations[posn.index].left.remove(&fact);
                            // If one side of a constraint is empty
                            if equations[posn.index].left.is_empty() {
                                // Add the other side to Sigma_surf
                                for fact in equations[posn.index].right.drain() {
                                    frontier.push(fact);
                                }
                            }
                        }
                        Side::Right => {
                            // Delete it from the constraint
                            equations[posn.index].right.remove(&fact);
                            // If one side of a constraint is empty
                            if equations[posn.index].right.is_empty() {
                                // Add the other side to Sigma_surf
                                for fact in equations[posn.index].left.drain() {
                                    frontier.push(fact);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    let core_scope_complement = core_scope.complement();
    // If any fact in Sigma_surf is in the complement of Sigma_core
    for rule in surf_scope.rules.values() {
        for fact in rule.iter() {
            if core_scope_complement.contains(&fact) {
                // ERROR
                panic!("\n\nScope inference failed. Inferred scope:\n\n{}\nInferred invalid fact: {}\n\n",
                       surf_scope,
                       fact);
            }
        }
    }
}

fn check_scope<Val>(scope: &ScopeRules,
                    rules: &Vec<RewriteRule<Val>>)
    where Val : fmt::Display
{
    for rule in rules.iter() {
        // Check that variables in holes will always remain bound.
        let lhs_order = resolve_hole_order(scope, &rule.left);
        let rhs_order = resolve_hole_order(scope, &rule.right);
        let rhs_holes: HashSet<Name> = rule.right.holes().into_iter()
            .map(|(name, _)| name)
            .collect();
        for lt in lhs_order {
            match &lt.left {
                &resolve::Elem::Hole(ref lt_name) => {
                    if rhs_holes.contains(lt_name)
                        && !rhs_order.contains(&lt)
                    {
                        panic!("Variables in {} and bound by {} may become unbound, in the rule:\n{}",
                               lt.left, lt.right, rule);
                    }
                }
                _ => ()
            }
        }
        // Check that introduced variables are well bound in the inferred scope.
        let bindings = resolve_bindings(scope, &rule.right);
        for (_, (refn, decls)) in bindings.into_iter() {
            if decls.len() == 0 {
                panic!("The variable reference {} is unbound in the right hand side of the rule:\n{}",
                       refn, rule);
            } else if decls.len() > 1 {
                panic!("The variable reference {} is ambiguously bound in the right hand side of the rule:\n{}",
                       refn, rule);
            }
        }
        // Check that introduced variables have distinct names when required to.
        let vars = rule.right.vars();
        for x in vars.iter() {
            for y in vars.iter() {
                if x != y && resolve_disj(scope, &rule.right, x, y) {
                    if let (&Decl(ref a), &Decl(ref b)) = (&rule.right[x], &rule.right[y]) {
                        if a == b {
                            panic!("The variable declarations {} are required to have distinct names in the right hand side of the rule:\n{}",
                                   rule.right[x], rule);
                        }
                    }
                }
            }
        }

        // Check that `as_refn$x` holes are always in scope of their hole.
        let holes = rule.right.holes();
        let hole_as_refns = rule.right.hole_as_refns();
        for (hole1, ref path1) in hole_as_refns.iter() {
            let mut is_bound = false;
            for (hole2, ref path2) in holes.iter() {
                if hole2 == hole1 && resolve_lt(scope, &rule.right, path1, path2) {
                    is_bound = true;
                }
            }
            if !is_bound {
                let r: Term<Val> = HoleToRefn(hole1.clone());
                panic!("The variable reference {} is unbound in the right hand side of the rule:\n{}",
                       r, rule);
            }
        }
    }
}

pub fn infer_scope<Val>(language: &mut Language<Val>)
    where Val : fmt::Display
{
    let mut constraints = vec!();
    for rule in language.rewrite_rules.iter() {
        for constraint in gen_constrs(rule).into_iter() {
            constraints.push(constraint.clone());
        }
    }
    solve(&language.core_scope, &mut language.surf_scope, constraints);
    check_scope(&language.surf_scope, &language.rewrite_rules);
}


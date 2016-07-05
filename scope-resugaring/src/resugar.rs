use std::fmt;
use std::collections::HashSet;
use std::collections::HashMap;
use std::hash::Hash;

use util::display_sep;
use preorder::Elem::{Imp, Exp, Child};
use rule::{Fact, ScopeRules, Language};
use term::{RewriteRule, Term};
use term::Term::*;



type Conj<Node> = Vec<Fact<Node>>;

#[derive(Clone)]
pub struct Constraint<Node> {
    left: Conj<Node>,
    right: Conj<Node>
}

impl<Node> Constraint<Node> {
    fn new(left: Conj<Node>, right: Conj<Node>) -> Constraint<Node> {
        Constraint{
            left: left,
            right: right
        }
    }
}

impl<Node> fmt::Display for Constraint<Node> where Node: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(display_sep(f, " & ", self.left.iter()));
        try!(write!(f, "   iff   "));
        display_sep(f, " & ", self.right.iter())
    }
}

pub fn gen_constrs<Node, Val>(rule: &RewriteRule<Node, Val>) -> Vec<Constraint<Node>>
    where Node: Clone + fmt::Display, Val: fmt::Display
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

fn gen_conj<Node, Val>(term: &Term<Node, Val>, a: &[usize], b: &[usize]) -> Conj<Node>
    where Node: Clone + fmt::Display, Val: fmt::Display
{
    // true: downarrow, false: uparrow
    fn gen<Node, Val>(term: &Term<Node, Val>, a: &[usize], b: &[usize], conj: &mut Vec<Fact<Node>>)
        where Node: Clone + fmt::Display, Val: fmt::Display
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
            _ => panic!("Internal error! Generate conjunction: bad path")
        }
    }
    let mut conj = vec!();
    gen(term, a, b, &mut conj);
    conj
}


fn solve<Node>(cs: Vec<Constraint<Node>>,
               core_scope: &ScopeRules<Node>,
               surf_scope: &mut ScopeRules<Node>)
    where Node: PartialEq + Clone + Eq + Hash + fmt::Display
{

    #[derive(Debug)]
    struct FactPosn {
        index: usize, // Index of constraint
        side: Side    // LHS vs. RHS of constraint
    }

    #[derive(Debug)]
    enum Side { Left, Right }


    struct Equation<Node> {
        left: HashSet<Fact<Node>>,
        right: HashSet<Fact<Node>>
    }


    // Setup efficient representation of constraints.
    // fact_posns: gives the constraints that a fact appears in
    // equations:  the constraints (with conjunctions repr as sets for efficiency)
    let mut fact_posns: HashMap<Fact<Node>, Vec<FactPosn>> = HashMap::new();
    let mut equations: Vec<Equation<Node>> = vec!();
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
    let mut frontier: Vec<Fact<Node>> = vec!();
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
                panic!("\n\nScope inference failed. Inferred scope:\n\n{}\n\nScope inference failed. Invalid fact: {}",
                       surf_scope,
                       fact);
            }
        }
    }
}

pub fn resugar_scope<Node, Val>(language: &mut Language<Node, Val>)
    where Node: Clone + fmt::Display + Eq + Hash, Val: fmt::Display
{
    let mut constraints = vec!();
    for rule in language.rewrite_rules.iter() {
        for constraint in gen_constrs(rule).into_iter() {
            constraints.push(constraint.clone());
        }
    }
    solve(constraints, &language.core_scope, &mut language.surf_scope)
}

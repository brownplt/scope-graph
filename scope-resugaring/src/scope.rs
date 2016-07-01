use std::fmt;
use std::collections::HashSet;
use std::collections::HashMap;
use std::hash::Hash;

use util::debug_sep;
use rule::{Fact, ScopeRules};
use rule::Elem::{Imp, Exp, Child};
use term::{RewriteRule, Term};
use term::Term::*;


type Conj<Node> = Vec<Fact<Node>>;

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
        try!(debug_sep(f, " & ", self.left.iter()));
        try!(write!(f, "   iff   "));
        debug_sep(f, " & ", self.right.iter())
    }
}

pub fn gen_constrs<Node, Val>(rule: &RewriteRule<Node, Val>) -> Vec<Constraint<Node>>
    where Node: Copy + fmt::Display, Val: fmt::Display
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
    where Node: Copy + fmt::Display, Val: fmt::Display
{
    fn gen<Node, Val>(term: &Term<Node, Val>, a: &[usize], b: &[usize], conj: &mut Vec<Fact<Node>>)
        where Node: Copy + fmt::Display, Val: fmt::Display
    {
        match term {
            &Stx(ref node, _) => {
                match (a.first(), b.first()) {
                    (None, None) => {
                        // S-Self
                        conj.push(Fact::new(*node, Exp, Imp));
                    }
                    (None, Some(&b0)) => {
                        // SA-Child
                        conj.push(Fact::new(*node, Exp, Child(b0)));
                        gen(term.child(b0), &[], &b[1..], conj);
                    }
                    (Some(&a0), None) => {
                        // SA-Parent
                        conj.push(Fact::new(*node, Child(a0), Imp));
                        gen(term.child(a0), &a[1..], &[], conj);
                    }
                    (Some(&a0), Some(&b0)) => {
                        if a0 == b0 && !term.child(a0).is_hole() {
                            // S-Lift
                            gen(term.child(a0), &a[1..], &b[1..], conj);
                        } else {
                            // SA-Sibling
                            conj.push(Fact::new(*node, Child(a0), Child(b0)));
                            gen(term.child(a0), &a[1..], &[], conj);
                            gen(term.child(b0), &[], &b[1..], conj);
                        }
                    }
                }
            },
            &Hole(_) => {
                if !a.is_empty() || !b.is_empty() {
                    panic!("Internal error! Generate conjunction: bad path to hole")
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


fn solve<Node>(core_scope: &ScopeRules<Node>, cs: Vec<Constraint<Node>>) -> ScopeRules<Node>
    where Node: PartialEq + Copy + Eq + Hash + fmt::Display
{

    struct FactPosn {
        index: usize, // Index of constraint
         side: Side    // LHS vs. RHS of constraint
    }

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
                    equation.left.insert(fact);
                }
                Side::Right => {
                    equation.right.insert(fact);
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
    let mut surface_scope = ScopeRules::new();
    let mut frontier: Vec<Fact<Node>> = vec!();
    for rule in core_scope.rules.iter() {
        for fact in rule.iter() {
            frontier.push(fact);
        }
    }
    
    while let Some(fact) = frontier.pop() {
        // Maintain transitive closure
        for trans_closure_fact in surface_scope.insert(fact) {
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
                            if equations[posn.index].left.is_empty() {
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
    for rule in surface_scope.rules.iter() {
        for fact in rule.iter() {
            if core_scope_complement.contains(&fact) {
                // ERROR
                panic!("Scope inference failed, with fact {}", fact);
            }
        }
    }

    surface_scope
}


#[cfg(test)]
mod tests {
    use std::fmt;
    use std::str;
    use std::time::SystemTime;

    use super::*;
    use term::{Term, RewriteRule};
    use term::Term::*;

    use source::SourceFile;
    use lexer::Lexer;
    use parser::{parse_rewrite_rule};

    use self::Node::*;

    #[derive(Clone, Copy)]
    enum Node { Let, Apply, Lambda }

    impl fmt::Display for Node {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match *self {
                Let => write!(f, "Let"),
                Apply => write!(f, "Apply"),
                Lambda => write!(f, "Lambda")
            }
        }
    }

    impl str::FromStr for Node {
        type Err = String;
        fn from_str(s: &str) -> Result<Node, String> {
            match s {
                "Let"    => Ok(Let),
                "Apply"  => Ok(Apply),
                "Lambda" => Ok(Lambda),
                _ => Err(String::from("Unknown Node"))
            }
        }
    }

    fn hole(name: &str) -> Term<Node, usize> {
        Hole(String::from(name))
    }

    #[test]
    fn constraint_solving() {
        let rule_1 = {
            let lhs = Stx(Let, vec!(hole("a"), hole("b"), hole("c")));
            let rhs = Stx(Apply, vec!(Stx(Lambda, vec!(hole("a"), hole("c"))), hole("b")));
            RewriteRule::new(lhs, rhs)
        };

        let core_lang = {
            
        };
    }

    #[test]
    fn constraint_generation() {
        let rule_1: RewriteRule<Node, usize> =
            parse_rewrite_rule(&SourceFile::from_str(
                "rule (Let a b c) => (Apply Lambda a c) b)" ));

        /*
        // To show elapsed time:
        let now = SystemTime::now();
        let actual_constraints: Vec<Constraint<Node>> = gen_constrs(&rule_1);
        println!("{:?}", now.elapsed());
        panic!();
        */

        let actual_constraints: Vec<String> = gen_constrs(&rule_1).iter()
            .map(|c| { format!("{}", c) })
            .collect();

        let expected_constraints = [
            "Let: ⊥ ⋖ ⊤   iff   Apply: ⊥ ⋖ ⊤",
            "Let: ⊥ ⋖ 1   iff   Apply: ⊥ ⋖ 1 & Lambda: ⊥ ⋖ 1",
            "Let: ⊥ ⋖ 2   iff   Apply: ⊥ ⋖ 2",
            "Let: ⊥ ⋖ 3   iff   Apply: ⊥ ⋖ 1 & Lambda: ⊥ ⋖ 2",
            "Let: 1 ⋖ ⊤   iff   Apply: 1 ⋖ ⊤ & Lambda: 1 ⋖ ⊤",
            "Let: 1 ⋖ 1   iff   Lambda: 1 ⋖ 1",
            "Let: 1 ⋖ 2   iff   Apply: 1 ⋖ 2 & Lambda: 1 ⋖ ⊤",
            "Let: 1 ⋖ 3   iff   Lambda: 1 ⋖ 2",
            "Let: 2 ⋖ ⊤   iff   Apply: 2 ⋖ ⊤",
            "Let: 2 ⋖ 1   iff   Apply: 2 ⋖ 1 & Lambda: ⊥ ⋖ 1",
            "Let: 2 ⋖ 2   iff   Apply: 2 ⋖ 2",
            "Let: 2 ⋖ 3   iff   Apply: 2 ⋖ 1 & Lambda: ⊥ ⋖ 2",
            "Let: 3 ⋖ ⊤   iff   Apply: 1 ⋖ ⊤ & Lambda: 2 ⋖ ⊤",
            "Let: 3 ⋖ 1   iff   Lambda: 2 ⋖ 1",
            "Let: 3 ⋖ 2   iff   Apply: 1 ⋖ 2 & Lambda: 2 ⋖ ⊤",
            "Let: 3 ⋖ 3   iff   Lambda: 2 ⋖ 2"];
        
        assert_eq!(actual_constraints.as_slice(), expected_constraints);
    }
}

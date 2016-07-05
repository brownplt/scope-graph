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
            println!("{}", Constraint::new(
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
            println!("Solve/init: {}", fact);
            frontier.push(fact);
        }
    }

    // Add facts from constraints that have a side that's *initially* empty
    for eqn in equations.iter_mut() {
        if eqn.left.is_empty() {
            for fact in eqn.right.drain() {
                println!("Solve/init*: {}", fact);
                frontier.push(fact);
            }
        }
        if eqn.right.is_empty() {
            for fact in eqn.left.drain() {
                println!("Solve/init*: {}", fact);
                frontier.push(fact);
            }
        }
    }
    
    while let Some(fact) = frontier.pop() {
        // Maintain transitive closure
        for trans_closure_fact in surf_scope.insert(fact.clone()) {
            println!("Solve/trans: {} from {}", trans_closure_fact, fact);
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
                                    println!("Solve/infer: {}", fact);
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
                                    println!("Solve/infer: {}", fact);
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



#[cfg(test)]
mod tests {
    use std::fmt;
    use std::str;
    use std::collections::HashMap;
    use std::sync::Mutex;
    use std::time::SystemTime;

    use super::*;
    use term::{RewriteRule};
    use rule::{Fact, Language};
    use preorder::Elem::{Imp, Exp, Child};
    use parser::SourceFile;
    use parser::{parse_rewrite_rule, parse_language};

    use self::Node::*;

    struct InternTable {
        count: usize,
        str_to_index: HashMap<String, usize>,
        index_to_str: HashMap<usize, String>
    }

    impl InternTable {
        fn intern(&mut self, s: &str) -> usize {
            if self.str_to_index.contains_key(s) {
                self.str_to_index[s]
            } else {
                let i = self.count;
                self.count += 1;
                self.str_to_index.insert(String::from(s), i);
                self.index_to_str.insert(i, String::from(s));
                i
            }
        }

        fn lookup(&self, index: usize) -> &str {
            &self.index_to_str[&index]
        }
    }

    type Node = String;

    #[test]
    fn constraint_generation() {
        let rule_1: RewriteRule<Node, usize> =
            parse_rewrite_rule(&SourceFile::from_str(
                "rule (Let a b c) => (Apply (Lambda a c) b)" ));

        // // To show elapsed time:
        // let now = SystemTime::now();
        // let actual_constraints: Vec<Constraint<Node>> = gen_constrs(&rule_1);
        // println!("{:?}", now.elapsed());
        // panic!();

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

    #[test]
    fn constraint_solving() {

        let mut lang_1: Language<Node, usize> =
            parse_language(&SourceFile::open("src/example_1.scope").unwrap());
        let mut lang_2: Language<Node, usize> =
            parse_language(&SourceFile::open("src/example_2.scope").unwrap());
        let mut lang_3: Language<Node, usize> =
            parse_language(&SourceFile::open("src/pyret.scope").unwrap());

        resugar_scope(&mut lang_1);
        resugar_scope(&mut lang_2);
        resugar_scope(&mut lang_3);


        // Example 1 from the paper (section 2.1: Single-arm Let)

        let ref let_rule = lang_1.surf_scope.rules["Let"];
        let let_facts: Vec<Fact<Node>> = let_rule.iter().collect();
        assert_eq!(let_facts.len(), 5);
        assert!(let_rule.lt(Exp, Imp));
        assert!(let_rule.lt(Child(1), Imp));
        assert!(let_rule.lt(Child(2), Imp));
        assert!(let_rule.lt(Child(2), Imp));
        assert!(let_rule.lt(Child(3), Child(1)));
        
        println!("\n{}", lang_1.surf_scope);


        // Example 1 from the paper (section 2.1: Multi-arm Let*)

        let ref let_rule = lang_2.surf_scope.rules["Let"];
        let let_facts: Vec<Fact<Node>> = let_rule.iter().collect();
        assert_eq!(let_facts.len(), 4);
        assert!(let_rule.lt(Exp, Imp));
        assert!(let_rule.lt(Child(1), Imp));
        assert!(let_rule.lt(Child(2), Imp));
        assert!(let_rule.lt(Child(2), Child(1)));

        let ref bind_rule = lang_2.surf_scope.rules["Bind"];
        let bind_facts: Vec<Fact<Node>> = bind_rule.iter().collect();
        assert_eq!(bind_facts.len(), 7);
        assert!(bind_rule.lt(Exp, Imp));
        assert!(bind_rule.lt(Child(1), Imp));
        assert!(bind_rule.lt(Child(2), Imp));
        assert!(bind_rule.lt(Child(3), Imp));
        assert!(bind_rule.lt(Child(3), Child(1)));
        assert!(bind_rule.lt(Exp, Child(1)));
        assert!(bind_rule.lt(Exp, Child(3)));
        
        println!("\n{}", lang_2.surf_scope);



        // Pyret language - for loop

        println!("\n{}", lang_3.surf_scope);
        let ref for_rule = lang_3.surf_scope.rules["For"];
        let for_facts: Vec<Fact<Node>> = for_rule.iter().collect();
        assert_eq!(for_facts.len(), 6);
        // (For loop)
        // child 1: iterating function
        // child 2: binding list
        // child 3: type annotation
        // child 4: for loop body
        assert!(for_rule.lt(Exp, Imp));
        assert!(for_rule.lt(Child(1), Imp));
        assert!(for_rule.lt(Child(2), Imp));
        assert!(for_rule.lt(Child(3), Imp));
        assert!(for_rule.lt(Child(4), Imp));
        assert!(for_rule.lt(Child(4), Child(2)));

        let ref bind_rule = lang_3.surf_scope.rules["ForBind"];
        let bind_facts: Vec<Fact<Node>> = bind_rule.iter().collect();
        assert_eq!(bind_facts.len(), 6);
        // (For loop binding)
        // child 1: parameter
        // child 2: value
        // child 3: rest of bindings
        assert!(bind_rule.lt(Exp, Imp));
        assert!(bind_rule.lt(Child(1), Imp));
        assert!(bind_rule.lt(Child(2), Imp));
        assert!(bind_rule.lt(Child(3), Imp));
        assert!(bind_rule.lt(Exp, Child(1)));
        assert!(bind_rule.lt(Exp, Child(3)));

        let ref fun_rule = lang_3.surf_scope.rules["Fun"];
        let fun_facts: Vec<Fact<Node>> = fun_rule.iter().collect();
        assert_eq!(fun_facts.len(), 13);
        // (Function definition)
        // child 1: function name
        // child 2: parameters
        // child 3: return type annotation
        // child 4: function body
        // child 5: rest of program
        assert!(fun_rule.lt(Exp, Imp));
        assert!(fun_rule.lt(Child(1), Imp));
        assert!(fun_rule.lt(Child(2), Imp));
        assert!(fun_rule.lt(Child(3), Imp));
        assert!(fun_rule.lt(Child(4), Imp));
        assert!(fun_rule.lt(Child(5), Imp));
        assert!(fun_rule.lt(Exp, Child(1)));
        assert!(fun_rule.lt(Exp, Child(5)));
        assert!(fun_rule.lt(Child(5), Child(1)));
        assert!(fun_rule.lt(Child(2), Child(1)));
        assert!(fun_rule.lt(Child(4), Child(2)));
        assert!(fun_rule.lt(Child(4), Child(1)));
        assert!(fun_rule.lt(Child(1), Child(1)));

        let ref let_rule = lang_3.surf_scope.rules["Let"];
        let let_facts: Vec<Fact<Node>> = let_rule.iter().collect();
        assert_eq!(let_facts.len(), 6);
        // (Let statement)
        // child 1: name
        // child 2: type annotation
        // child 3: value
        // child 4: rest of program
        assert!(let_rule.lt(Exp, Imp));
        assert!(let_rule.lt(Child(1), Imp));
        assert!(let_rule.lt(Child(2), Imp));
        assert!(let_rule.lt(Child(3), Imp));
        assert!(let_rule.lt(Child(4), Imp));
        assert!(let_rule.lt(Child(4), Child(1)));
    }

}

use std::fmt;
use std::collections::{HashSet, HashMap};
use std::hash::Hash;

use preorder::{Elem, Lt, Preorder};
use preorder::Elem::{Imp, Exp, Child};
use term::{Term, RewriteRule};


// Section 4.4
pub struct ScopeRule<Node> {
    node: Node,
    order: Preorder
}

impl<Node> fmt::Display for ScopeRule<Node>
    where Node: fmt::Display + Copy 
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{} {} {{\n", self.node, self.arity()));
        for fact in self.iter() {
            try!(write!(f, "    {}\n", fact))
        }
        write!(f, "}}\n")
    }
}

impl<Node> ScopeRule<Node> {
    pub fn new(node: Node, arity: usize, facts: Vec<Lt>) -> ScopeRule<Node>
        where Node: fmt::Display + Copy
    {
        // Scope Rule Axiom 1/4 (transitivity): guaranteed by Preorder.
        let mut order = Preorder::new_non_reflexive(arity + 2);
        for fact in facts.into_iter() {
            // Scope Rule Axiom 2/4
            if fact.right == Exp {
                panic!("Cannot import bindings from {}", Exp)
            }
            // Scope Rule Axiom 3/4
            if fact.left == Imp {
                panic!("Cannot export bindings from {}", Imp)
            }
            if let Child(i) = fact.left {
                if i > arity {
                    panic!("Child {} is out of bounds; this rule has arity {}", fact.left, arity);
                }
            }
            if let Child(j) = fact.right {
                if j > arity {
                    panic!("Child {} is out of bounds; this rule has arity {}", fact.right, arity);
                }
            }
            order.insert(fact);
        }
        // Scope Rule Axiom 4/4
        order.insert(Lt::new(Exp, Imp));
        ScopeRule{
            node: node,
            order: order
        }
    }

    pub fn iter(&self) -> Iter<Node>
        where Node: Copy
    {
        let pairs = self.order.facts();
        Iter{
            node: self.node,
            pairs: pairs
        }
    }

    pub fn arity(&self) -> usize {
        self.order.size - 2
    }

    pub fn lt(&self, left: Elem, right: Elem) -> bool {
        self.contains(Lt::new(left, right))
    }

    pub fn contains(&self, fact: Lt) -> bool {
        self.order.contains(fact)
    }
}

pub struct Iter<Node> {
    node: Node,
    pairs: Vec<Lt>
}

impl<Node> Iterator for Iter<Node> where Node: Copy {
    type Item = Fact<Node>;
    fn next(&mut self) -> Option<Fact<Node>> {
        match self.pairs.pop() {
            None => None,
            Some(lt) => Some(Fact::new(self.node, lt.left, lt.right))
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fact<Node> {
    node: Node,
    left: Elem,
    right: Elem
}

impl<Node> fmt::Display for Fact<Node>
    where Node: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {} ⋖ {}", self.node, self.left, self.right)
    }
}

impl<Node> Fact<Node> {
    pub fn new(node: Node, left: Elem, right: Elem) -> Fact<Node> {
        Fact{
            node: node,
            left: left,
            right: right
        }
    }
}

pub struct ScopeRules<Node> {
    pub rules: HashMap<Node, ScopeRule<Node>>
}

impl<Node> fmt::Display for ScopeRules<Node>
    where Node: fmt::Display + Copy + Eq + Hash
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for rule in self.rules.values() {
            try!(write!(f, "{}", rule));
        }
        Ok(())
    }
}

impl<Node> ScopeRules<Node> {
    pub fn new() -> ScopeRules<Node> where Node: Eq + Hash {
        ScopeRules{
            rules: HashMap::new()
        }
    }

    pub fn from_vec(rules: Vec<ScopeRule<Node>>) -> ScopeRules<Node>
        where Node: Eq + Hash + Copy
    {
        let mut map = HashMap::new();
        for rule in rules.into_iter() {
            map.insert(rule.node, rule);
        }
        ScopeRules{
            rules: map
        }
    }

    pub fn insert(&mut self, fact: Fact<Node>) -> Vec<Fact<Node>>
        where Node: Copy + Eq + Hash
    {
        let lt = Lt::new(fact.left, fact.right);
        let ref mut rule = self.rules.get_mut(&fact.node).unwrap();
        rule.order.insert(lt).iter().map(|lt| {
            Fact::new(fact.node, lt.left, lt.right)
        }).collect()
    }

    pub fn complement(&self) -> HashSet<Fact<Node>>
        where Node: Copy + Eq + Hash
    {
        let mut complement = HashSet::new();
        for rule in self.rules.values() {
            for lt in rule.order.complement().into_iter() {
                complement.insert(Fact::new(rule.node, lt.left, lt.right));
            }
        }
        complement
    }
}



pub struct Language<Node, Val> {
    pub name: String,
    pub core_scope: ScopeRules<Node>,
    pub surf_scope: ScopeRules<Node>,
    pub rewrite_rules: Vec<RewriteRule<Node, Val>>
}

impl<Node, Val> Language<Node, Val> {
    pub fn new(name: String,
           core_scope: Vec<ScopeRule<Node>>,
           rewrite_rules: Vec<RewriteRule<Node, Val>>)
               -> Language<Node, Val>
        where Node: Copy + Eq + Hash + fmt::Display + 
    {
        let mut surf_scope = vec!();
        fn gather_arities<Node, Val>(term: &Term<Node, Val>,
                                     surf_scope: &mut Vec<ScopeRule<Node>>)
            where Node: Copy + fmt::Display
        {
            match term {
                &Term::Stx(node, ref subterms) => {
                    let arity = subterms.len();
                    surf_scope.push(ScopeRule::new(node, arity, vec!()));
                    for term in subterms.iter() {
                        gather_arities(term, surf_scope)
                    }
                }
                _ => ()
            }
        }
        for rule in rewrite_rules.iter() {
            gather_arities(&rule.left, &mut surf_scope);
            gather_arities(&rule.right, &mut surf_scope);
        }
        
        Language{
            name: name,
            core_scope: ScopeRules::from_vec(core_scope),
            surf_scope: ScopeRules::from_vec(surf_scope),
            rewrite_rules: rewrite_rules
        }
    }
}

use std::fmt;
use std::collections::{HashSet, HashMap};
use std::hash::Hash;

use preorder::{Elem, Lt, Preorder};
use preorder::Elem::{Imp, Exp, Child};
use term::{Term, RewriteRule};


// Section 4.4
#[derive(Clone)]
pub struct ScopeRule<Node> {
    node: Node,
    args: Option<Vec<String>>,
    kind: Kind,
    order: Preorder
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Kind { Core, Surface }

impl<Node> fmt::Display for ScopeRule<Node>
    where Node: fmt::Display + Clone 
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "({}", self.node));
        match self.args {
            Some(ref args) =>
                for arg in args.iter() {
                    try!(write!(f, " {}", arg));
                },
            None =>
                for _ in 0..self.arity() {
                    try!(write!(f, " _"));
                }
        }
        try!(write!(f, ") {{\n"));
        for fact in self.iter() {
            try!(write!(f, "    {}\n", fact))
        }
        write!(f, "}}\n\n")
    }
}

impl<Node> ScopeRule<Node> {
    pub fn new_core(node: Node, args: Vec<String>, facts: Vec<Lt>) -> ScopeRule<Node>
        where Node: Clone
    {
        ScopeRule::make(node, Ok(args), facts, Kind::Core)
    }

    pub fn new_surface(node: Node, args: Vec<String>) -> ScopeRule<Node>
        where Node: Clone
    {
        ScopeRule::make(node, Ok(args), vec!(), Kind::Surface)
    }

    fn new_implicit(node: Node, arity: usize) -> ScopeRule<Node>
        where Node: Clone
    {
        ScopeRule::make(node, Err(arity), vec!(), Kind::Surface)
    }
    
    fn make(node: Node, args: Result<Vec<String>, usize>, facts: Vec<Lt>, kind: Kind)
            -> ScopeRule<Node>
        where Node: Clone
    {
        let arity = match args {
            Err(arity) => arity,
            Ok(ref args) => args.len()
        };
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
            args: args.ok(),
            order: order,
            kind: kind
        }
    }

    pub fn iter(&self) -> Iter<Node>
        where Node: Clone
    {
        let pairs = self.order.facts();
        Iter{
            node: self.node.clone(),
            pairs: pairs
        }
    }

    pub fn arity(&self) -> usize {
        self.order.size - 2
    }

    pub fn lt(&self, left: Elem, right: Elem) -> bool {
        let lt = Lt::new(left, right);
        self.order.contains(lt)
    }

    pub fn implicit(&self) -> bool {
        self.args.is_none()
    }
}

pub struct Iter<Node> {
    node: Node,
    pairs: Vec<Lt>
}

impl<Node> Iterator for Iter<Node> where Node: Clone {
    type Item = Fact<Node>;
    fn next(&mut self) -> Option<Fact<Node>> {
        match self.pairs.pop() {
            None => None,
            Some(lt) => Some(Fact::new(self.node.clone(), lt.left, lt.right))
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
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
    pub rules: HashMap<Node, ScopeRule<Node>>,
    kind: Kind
}

impl<Node> fmt::Display for ScopeRules<Node>
    where Node: fmt::Display + Clone + Eq + Hash
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for rule in self.rules.values() {
            if rule.kind == self.kind && !rule.implicit() {
                try!(write!(f, "{}", rule));
            }
        }
        Ok(())
    }
}

impl<Node> ScopeRules<Node> {
    fn new(rules: Vec<ScopeRule<Node>>, kind: Kind) -> ScopeRules<Node>
        where Node: Eq + Hash + Clone
    {
        let mut map = HashMap::new();
        for rule in rules.into_iter() {
            map.insert(rule.node.clone(), rule);
        }
        ScopeRules{
            rules: map,
            kind: kind
        }
    }

    pub fn insert(&mut self, fact: Fact<Node>) -> Vec<Fact<Node>>
        where Node: Clone + Eq + Hash + fmt::Display
    {
        let lt = Lt::new(fact.left, fact.right);
        let ref mut rule = match self.rules.get_mut(&fact.node) {
            None => panic!("Declaration for {} not found", &fact.node),
            Some(rule) => rule
        };
        rule.order.insert(lt).iter().map(|lt| {
            Fact::new(fact.node.clone(), lt.left, lt.right)
        }).collect()
    }

    pub fn complement(&self) -> HashSet<Fact<Node>>
        where Node: Clone + Eq + Hash
    {
        let mut complement = HashSet::new();
        for rule in self.rules.values() {
            for lt in rule.order.complement().into_iter() {
                complement.insert(Fact::new(rule.node.clone(), lt.left, lt.right));
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
               mut surf_scope: Vec<ScopeRule<Node>>,
               rewrite_rules: Vec<RewriteRule<Node, Val>>)
               -> Language<Node, Val>
        where Node: Clone + Eq + Hash + fmt::Display + 
    {
        fn gather_arities<Node, Val>(term: &Term<Node, Val>,
                                     surf_scope: &mut Vec<ScopeRule<Node>>)
            where Node: Clone + fmt::Display + Eq
        {
            match term {
                &Term::Stx(ref node, ref subterms) => {
                    let mut exists = false;
                    for ref rule in surf_scope.iter() {
                        if &rule.node == node {
                            exists = true;
                        }
                    }
                    if !exists {
                        let arity = subterms.len();
                        surf_scope.push(ScopeRule::new_implicit(node.clone(), arity));
                    }
                    for term in subterms.iter() {
                        gather_arities(term, surf_scope)
                    }
                }
                _ => ()
            }
        }

        for rule in core_scope.iter() {
            surf_scope.push(rule.clone());
        }
        for rule in rewrite_rules.iter() {
            gather_arities(&rule.left, &mut surf_scope);
            gather_arities(&rule.right, &mut surf_scope);
        }
        
        Language{
            name: name,
            core_scope: ScopeRules::new(core_scope, Kind::Core),
            surf_scope: ScopeRules::new(surf_scope, Kind::Surface),
            rewrite_rules: rewrite_rules
        }
    }
}

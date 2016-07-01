use std::fmt;
use std::collections::{HashSet, HashMap};
use std::hash::Hash;

use preorder::Preorder;
use term::{Term, RewriteRule};

use self::Elem::*;


// Section 4.4
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Elem {
    Imp,
    Exp,
    Child(usize)
}

impl From<Elem> for usize {
    fn from(elem: Elem) -> usize {
        match elem {
            Imp => 0,
            Exp => 1,
            Child(i) => i + 2
        }
    }
}

impl From<usize> for Elem {
    fn from(size: usize) -> Elem {
        match size {
            0 => Imp,
            1 => Exp,
            i => Child(i - 2)
        }
    }
}

impl fmt::Display for Elem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Imp => write!(f, "⊤"),
            Exp => write!(f, "⊥"),
            Child(i)   => write!(f, "{}", i + 1)
        }
    }
}


// Section 4.4
// left <. right
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fact<Node> {
    node: Node,
    left: Elem,
    right: Elem
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

impl<Node> fmt::Display for Fact<Node>
    where Node: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match (self.left, self.right) {
            (Child(a), Imp)      => write!(f, "import {}", a + 1),
            (Exp, Child(b))      => write!(f, "export {}", b + 1),
            (Child(a), Child(b)) => write!(f, "bind {} in {}", b + 1, a + 1),
            (Exp, Imp)           => write!(f, "export imports"),
            (a, b) => write!(f, "[invalid fact {} ⋖ {}]", a, b)
//            (a, b) => panic!("Attempted to print invalid fact: {} ⋖ {}", a, b)
        }
    }
}

impl<Node> fmt::Debug for Fact<Node>
    where Node: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {} ⋖ {}", self.node, self.left, self.right)
    }
}


// Section 4.4
pub struct ScopeRule<Node> {
    node: Node,
    order: Preorder
}

impl<Node> fmt::Display for ScopeRule<Node>
    where Node: fmt::Display + Copy 
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let arity = self.arity();
        try!(write!(f, "{} {} {{\n", self.node, self.arity()));
        for fact in self.iter() {
            try!(write!(f, "    {}\n", fact))
        }
        write!(f, "}}\n")
    }
}

impl<Node> ScopeRule<Node> {
    pub fn new(node: Node, arity: usize, facts: Vec<(Elem, Elem)>) -> ScopeRule<Node>
        where Node: fmt::Display + Copy {
        // Scope Rule Axiom 1/4 (transitivity): guaranteed by Preorder.
        let mut order = Preorder::new_non_reflexive(arity + 2);
        for &(left, right) in facts.iter() {
            // Scope Rule Axiom 2/4
            if right == Exp {
                panic!("Cannot import bindings from {}", Exp)
            }
            // Scope Rule Axiom 3/4
            if left == Imp {
                panic!("Cannot export bindings from {}", Imp)
            }
            let left_index = usize::from(left);
            if left_index >= arity + 2 {
                panic!("Child {} is out of bounds; this rule has arity {}", left, arity);
            }
            let right_index = usize::from(right);
            if right_index >= arity + 2 {
                panic!("Child {} is out of bounds; this rule has arity {}", left, arity);
            }
            order.insert((left_index, right_index));
        }
        // Scope Rule Axiom 4/4
        order.insert((usize::from(Exp), usize::from(Imp)));
        ScopeRule{
            node: node,
            order: order
        }
    }

    pub fn iter(&self) -> Iter<Node> where Node: Copy {
        let pairs = self.order.as_pairs();
        Iter{
            node: self.node,
            pairs: pairs
        }
    }

    pub fn arity(&self) -> usize {
        self.order.size - 2
    }

    pub fn lt(&self, left: Elem, right: Elem) -> bool {
        self.order.lt((usize::from(left), usize::from(right)))
    }
}

pub struct Iter<Node> {
    node: Node,
    pairs: Vec<(usize, usize)>
}

impl<Node> Iterator for Iter<Node> where Node: Copy {
    type Item = Fact<Node>;
    fn next(&mut self) -> Option<Fact<Node>> {
        match self.pairs.pop() {
            None => None,
            Some((a, b)) => Some(Fact::new(self.node, Elem::from(a), Elem::from(b)))
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
        let node = fact.node;
        let ref mut rule = self.rules.get_mut(&node).unwrap();
        let mut transitive_closure_facts = vec!();
        for pair in rule.order.insert((usize::from(fact.left), usize::from(fact.right))) {
            let fact = Fact::new(node, Elem::from(pair.0), Elem::from(pair.1));
            transitive_closure_facts.push(fact);
        }
        transitive_closure_facts
    }

    pub fn complement(&self) -> HashSet<Fact<Node>>
        where Node: Copy + Eq + Hash
    {
        let mut complement = HashSet::new();
        for rule in self.rules.values() {
            for pair in rule.order.complement_as_pairs().iter() {
                let fact = Fact::new(rule.node, Elem::from(pair.0), Elem::from(pair.1));
                complement.insert(fact);
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

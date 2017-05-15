use std::fmt;
use std::collections::{HashSet, HashMap};
use std::ops::Index;

use preorder::{Elem, Lt, Preorder};
use term::{Term, RewriteRule};

pub use term::Node;


// Section 4.4
#[derive(Clone)]
pub struct ScopeRule {
    node: Node,
    args: Vec<String>,
    kind: Kind,
    implicit: bool,
    order: Preorder,
    disjs: Preorder
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Kind { Core, Surface }

impl fmt::Display for ScopeRule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "({}", self.node));
        for arg in self.args.iter() {
            try!(write!(f, " {}", arg));
        }
        try!(write!(f, ") {{\n"));
        for fact in self.iter() {
            try!(write!(f, "    "));
            try!(fact.pretty(f, &self.args));
            try!(write!(f, ";\n"));
        }
        write!(f, "}}\n\n")
    }
}

impl ScopeRule {
    pub fn new_core(node: Node, args: Vec<String>, facts: Vec<Lt>) -> ScopeRule
    {
        ScopeRule::make(node, args, facts, vec!(), Kind::Core, false)
    }

    pub fn new_surface(node: Node, args: Vec<String>, disjs: Vec<Lt>) -> ScopeRule
    {
        ScopeRule::make(node, args, vec!(), disjs, Kind::Surface, false)
    }

    fn new_implicit(node: Node, arity: usize) -> ScopeRule
    {
        let mut args = vec!();
        for i in 1 .. arity + 1 {
            args.push(format!("{}", i));
        }
        ScopeRule::make(node, args, vec!(), vec!(), Kind::Surface, true)
    }
    
    fn make(node: Node, args: Vec<String>, facts: Vec<Lt>, disjs: Vec<Lt>, kind: Kind, implicit: bool)
            -> ScopeRule
    {
        let arity = args.len();
        let order = Preorder::from_facts(arity, facts);
        let disj_order = Preorder::from_facts(arity, disjs);
        ScopeRule{
            node: node,
            args: args,
            order: order,
            disjs: disj_order,
            kind: kind,
            implicit: implicit
        }
    }

    pub fn iter(&self) -> Iter {
        let mut pairs = self.order.facts();
        pairs.reverse();
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
    
    pub fn disj(&self, left: Elem, right: Elem) -> bool {
        let lt = Lt::new(left, right);
        self.disjs.contains(lt)
    }

    pub fn implicit(&self) -> bool {
        self.implicit
    }
}

pub struct Iter {
    node: Node,
    pairs: Vec<Lt>
}

impl Iterator for Iter {
    type Item = Fact;
    fn next(&mut self) -> Option<Fact> {
        match self.pairs.pop() {
            None => None,
            Some(lt) => Some(Fact::new(self.node.clone(), lt.left, lt.right))
        }
    }
}

// Section 4.4
// (left, right) in Sigma[Node]
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Fact {
    pub node: Node,
    pub left: Elem,
    pub right: Elem
}

pub type Conj = Vec<Fact>;

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {} ⋖ {}", self.node, self.left, self.right)
    }
}

impl Fact {
    pub fn new(node: Node, left: Elem, right: Elem) -> Fact {
        Fact{
            node: node,
            left: left,
            right: right
        }
    }

    fn pretty(&self, f: &mut fmt::Formatter, args: &Vec<String>) -> fmt::Result {
        Lt::new(self.left, self.right).pretty(f, args)
    }
}

pub struct ScopeRules {
    pub rules: HashMap<Node, ScopeRule>,
    kind: Kind
}

impl fmt::Display for ScopeRules {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for rule in self.rules.values() {
            if rule.kind == self.kind && !rule.implicit() {
                try!(write!(f, "{}", rule));
            }
        }
        Ok(())
    }
}

impl ScopeRules {
    fn new(rules: Vec<ScopeRule>, kind: Kind) -> ScopeRules {
        let mut map = HashMap::new();
        for rule in rules.into_iter() {
            map.insert(rule.node.clone(), rule);
        }
        ScopeRules{
            rules: map,
            kind: kind
        }
    }

    pub fn satisfied(&self, fact: &Fact) -> bool {
        match self.rules.get(&fact.node) {
            None => false,
            Some(rule) => rule.lt(fact.left, fact.right)
        }
    }

    pub fn disjoint(&self, fact: &Fact) -> bool {
        match self.rules.get(&fact.node) {
            None => false,
            Some(rule) => rule.disj(fact.left, fact.right)
        }
    }

    pub fn insert(&mut self, fact: Fact) -> Vec<Fact> {
        let lt = Lt::new(fact.left, fact.right);
        let ref mut rule = match self.rules.get_mut(&fact.node) {
            None => panic!("Declaration for {} not found", &fact.node),
            Some(rule) => rule
        };
        rule.order.insert(lt).iter().map(|lt| {
            Fact::new(fact.node.clone(), lt.left, lt.right)
        }).collect()
    }

    pub fn complement(&self) -> HashSet<Fact> {
        let mut complement = HashSet::new();
        for rule in self.rules.values() {
            for lt in rule.order.complement().into_iter() {
                complement.insert(Fact::new(rule.node.clone(), lt.left, lt.right));
            }
        }
        complement
    }
}

impl<'a> Index<&'a str> for ScopeRules {
    type Output = ScopeRule;
    fn index(&self, index: &'a str) -> &ScopeRule {
        match self.rules.get(index) {
            Some(rule) => rule,
            None => panic!("Internal error: Failed to find node {}", index)
        }
    }
}



pub struct Language<Val> {
    pub name: String,
    pub core_scope: ScopeRules,
    pub surf_scope: ScopeRules,
    pub rewrite_rules: Vec<RewriteRule<Val>>
}

impl<Val> Language<Val> {
    pub fn new(name: String,
               core_scope: Vec<ScopeRule>,
               mut surf_scope: Vec<ScopeRule>,
               rewrite_rules: Vec<RewriteRule<Val>>)
               -> Language<Val>
    {
        fn gather_arities<Val>(term: &Term<Val>, surf_scope: &mut Vec<ScopeRule>, core_scope: &Vec<ScopeRule>) {
            match term {
                &Term::Stx(ref node, ref subterms) => {
                    let mut exists = false;
                    for ref rule in surf_scope.iter() {
                        if &rule.node == node {
                            exists = true;
                            let arity = subterms.len();
                            let expected_arity = rule.arity();
                            if arity != expected_arity {
                                panic!("Term `{}` constructed with the wrong number of children. Found {} children, but expected {} children.",
                                       node, arity, expected_arity);
                            }
                        }
                    }
                    if !exists {
                        let arity = subterms.len();
                        surf_scope.push(ScopeRule::new_implicit(node.clone(), arity));
                    }
                    for term in subterms.iter() {
                        gather_arities(term, surf_scope, core_scope)
                    }
                }
                _ => ()
            }
        }

        for rule in core_scope.iter() {
            surf_scope.push(rule.clone());
        }
        for rule in rewrite_rules.iter() {
            gather_arities(&rule.left, &mut surf_scope, &core_scope);
            gather_arities(&rule.right, &mut surf_scope, &core_scope);
        }
        
        Language{
            name: name,
            core_scope: ScopeRules::new(core_scope, Kind::Core),
            surf_scope: ScopeRules::new(surf_scope, Kind::Surface),
            rewrite_rules: rewrite_rules
        }
    }
}

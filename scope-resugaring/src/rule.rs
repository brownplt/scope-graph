use std::fmt;
use std::collections::HashSet;

use preorder::Preorder;

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
            Child(i)   => i + 1
        }
    }
}

impl From<usize> for Elem {
    fn from(size: usize) -> Elem {
        match size {
            0 => Imp,
            1 => Exp,
            i => Child(i - 1)
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
            (Child(a), Child(b)) => write!(f, "bind {} in {}", a + 1, b + 1),
            (Exp, Imp)           => write!(f, "export imports"),
            (a, b) => panic!("Attempted to print invalid fact: {} ⋖ {}", a, b)
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

impl<Node> ScopeRule<Node> {
    pub fn new(node: Node, arity: usize, facts: Vec<(Elem, Elem)>) -> ScopeRule<Node> {
        // Scope Rule Axiom 1/4 (transitivity): guaranteed by Preorder.
        let mut order = Preorder::new_non_reflexive(arity);
        for &(left, right) in facts.iter() {
            // Scope Rule Axiom 2/4
            if left == Exp {
                panic!("Cannot import bindings from {}", Exp)
            }
            // Scope Rule Axiom 3/4
            if right == Imp {
                panic!("Cannot export bindings from {}", Imp)
            }
            order.insert((left, right));
        }
        // Scope Rule Axiom 4/4
        order.insert((Imp, Exp));
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
    pub rules: Vec<ScopeRule<Node>>
}

impl<Node> ScopeRules<Node> {
    pub fn new() -> ScopeRules<Node> {
        ScopeRules{
            rules: vec!()
        }
    }

    pub fn insert(&mut self, fact: Fact<Node>) -> Vec<Fact<Node>> {
        panic!("NYI")
    }

    pub fn complement(&self) -> HashSet<Fact<Node>> {
        panic!("NYI")
    }
}

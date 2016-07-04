use std::fmt;
use std::ops::{Index, IndexMut};

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
            Child(i) => i + 1
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
            Imp      => write!(f, "⊤"),
            Exp      => write!(f, "⊥"),
            Child(i) => write!(f, "{}", i)
        }
    }
}




// Section 4.4
// left <. right
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Lt {
    pub left: Elem,
    pub right: Elem
}

impl Lt {
    pub fn new(left: Elem, right: Elem) -> Lt {
        Lt{
            left: left,
            right: right
        }
    }
}

impl fmt::Display for Lt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match (self.left, self.right) {
            (Child(i), Imp)      => write!(f, "import {}", i + 1),
            (Exp, Child(j))      => write!(f, "export {}", j + 1),
            (Child(i), Child(j)) => write!(f, "jind {} in {}", j + 1, i + 1),
            (Exp, Imp)           => write!(f, "export imports"),
            (a, b)               => write!(f, "[invalid fact {} ⋖ {}]", a, b)
        }
    }
}



// Edges are more direct representations of Lts, for use in Preorder impl.
pub type Edge = (usize, usize);

impl From<Edge> for Lt {
    fn from(edge: Edge) -> Lt {
        Lt::new(Elem::from(edge.0), Elem::from(edge.1))
    }
}

impl From<Lt> for Edge {
    fn from(fact: Lt) -> Edge {
        (usize::from(fact.left), usize::from(fact.right))
    }
}



// Invariant: Always is transitively and reflexively closed
// Invariant: `order` always has size `size`
pub struct Preorder {
    pub size: usize,
    order: Vec<Vec<bool>>
}

impl Index<Edge> for Preorder {
    type Output = bool;
    fn index(&self, edge: Edge) -> &bool {
        &self.order[edge.0][edge.1]
    }
}

impl IndexMut<Edge> for Preorder {
    fn index_mut(&mut self, edge: Edge) -> &mut bool {
        &mut self.order[edge.0][edge.1]
    }
}

impl Preorder {
    pub fn new(size: usize) -> Preorder {
        // Initialize with the empty preorder (which has x <= x for all x)
        let mut order = Vec::with_capacity(size);
        for i in 0..size {
            let mut row = Vec::with_capacity(size);
            for j in 0..size {
                row.push(i == j);
            }
            order.push(row);
        }
        Preorder{
            size: size,
            order: order
        }
    }

    // Used by rules: closed under transitivity, but not reflexivity.
    pub fn new_non_reflexive(size: usize) -> Preorder {
        let mut order = Vec::with_capacity(size);
        for _ in 0..size {
            let mut row = Vec::with_capacity(size);
            for _ in 0..size {
                row.push(false);
            }
            order.push(row);
        }
        Preorder{
            size: size,
            order: order
        }
    }

    pub fn contains(&self, fact: Lt) -> bool {
        self[Edge::from(fact)]
    }

    // O(n*n*n) amortized
    pub fn insert(&mut self, init_fact: Lt) -> Vec<Lt>
    {
        let init_edge = Edge::from(init_fact);
        let mut new_facts = vec!();
        let mut frontier = vec!(init_edge);
        while let Some(edge) = frontier.pop() {
            if !self[edge] {
                self[edge] = true;
                if edge != init_edge {
                    new_facts.push(Lt::from(edge));
                }
                for i in 0..self.size {
                    if self[(edge.1, i)] {
                        frontier.push((edge.0, i));
                    }
                }
                for i in 0..self.size {
                    if self[(i, edge.0)] {
                        frontier.push((i, edge.1));
                    }
                }
            }
        }
        new_facts
    }

    pub fn facts(&self) -> Vec<Lt> {
        let mut pairs = vec!();
        for x in 0..self.size {
            for y in 0..self.size {
                let edge = (x, y);
                if self[edge] {
                    pairs.push(Lt::from(edge));
                }
            }
        }
        pairs
    }

    pub fn complement(&self) -> Vec<Lt> {
        let mut pairs = vec!();
        for x in 0..self.size {
            for y in 0..self.size {
                let edge = (x, y);
                if !self[edge] {
                    pairs.push(Lt::from(edge));
                }
            }
        }
        pairs
    }
}


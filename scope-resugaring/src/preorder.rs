

// Invariant: Always is transitively and reflexively closed
// Invariant: `order` always has size `size`
pub struct Preorder {
    size: usize,
    order: Vec<Vec<bool>>
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
        for i in 0..size {
            let mut row = Vec::with_capacity(size);
            for j in 0..size {
                row.push(false);
            }
            order.push(row);
        }
        Preorder{
            size: size,
            order: order
        }
    }

    pub fn lt<Elem>(&self, a: Elem, b: Elem) -> bool where usize: From<Elem> {
        self.order[usize::from(a)][usize::from(b)]
    }

    // O(n*n*n) amortized
    pub fn insert<Elem>(&mut self, edge: (Elem, Elem)) where usize: From<Elem> {
        let edge = (usize::from(edge.0), usize::from(edge.1));
        let mut frontier = vec!(edge);
        while let Some(edge) = frontier.pop() {
            if !self.order[edge.0][edge.1] {
                self.order[edge.0][edge.1] = true;
                for i in 0..self.size {
                    if self.order[edge.1][i] {
                        frontier.push((edge.0, i));
                    }
                }
                for i in 0..self.size {
                    if self.order[i][edge.0] {
                        frontier.push((i, edge.1));
                    }
                }
            }
        }
    }

    pub fn as_pairs(&self) -> Vec<(usize, usize)> {
        let mut pairs = vec!();
        for x in 0..self.size {
            for y in 0..self.size {
                if self.order[x][y] {
                    pairs.push((x, y));
                }
            }
        }
        pairs
    }
}

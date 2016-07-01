

// Invariant: Always is transitively and reflexively closed
// Invariant: `order` always has size `size`
pub struct Preorder {
    pub size: usize,
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

    pub fn lt(&self, edge: (usize, usize)) -> bool {
        self.order[edge.0][edge.1]
    }

    // O(n*n*n) amortized
    pub fn insert(&mut self, init_edge: (usize, usize)) -> Vec<(usize, usize)>
    {
        let mut new_edges = vec!();
        let mut frontier = vec!(init_edge);
        while let Some(edge) = frontier.pop() {
            if !self.order[edge.0][edge.1] {
                self.order[edge.0][edge.1] = true;
                if edge != init_edge {
                    new_edges.push(edge);
                }
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
        new_edges
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

    pub fn complement_as_pairs(&self) -> Vec<(usize, usize)> {
        let mut pairs = vec!();
        for x in 0..self.size {
            for y in 0..self.size {
                if !self.order[x][y] {
                    pairs.push((x, y));
                }
            }
        }
        pairs
    }
}



static mut id: usize = 0;

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct Atom {
    id: usize
}

impl Atom {
    pub fn fresh() -> Atom {
        // Not thread safe!
        unsafe {
            id += 1;
            Atom{
                id: id
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::Atom;

    #[test]
    fn fresh_atoms() {
        let x: Atom = Atom::fresh();
        let y: Atom = Atom::fresh();
        assert!(x == x);
        assert!(y == y);
        assert!(x != y);
        assert!(y != x);
    }
}

use std::collections::HashMap;
use std::ops::Index;

struct StringCache {
    forward: HashMap<String, usize>,
    backward: Vec<String>
}

impl StringCache {
    pub fn new() -> StringCache {
        StringCache{
            forward: HashMap::new(),
            backward: vec!()
        }
    }

    pub fn insert(&mut self, s: String) -> usize {
        if self.forward.contains_key(&s) {
            panic!("Duplicate name: {}", s);
        }
        self.backward.push(s.clone());
        let i = self.backward.len();
        self.forward.insert(s, i);;
        i
    }
}

impl Index<usize> for StringCache {
    type Output = str;
    fn index(&self, i: usize) -> &str {
        &self.backward[i]
    }
}

impl<'a> Index<&'a str> for StringCache {
    type Output = usize;
    fn index(&self, s: &'a str) -> &usize {
        &self.forward[s]
    }
}

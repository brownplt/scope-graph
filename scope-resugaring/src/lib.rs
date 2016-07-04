extern crate regex;
#[macro_use] extern crate lazy_static;

mod util;
pub mod preorder;
pub mod term;
pub mod rule;
mod parser;
pub mod resugar;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}


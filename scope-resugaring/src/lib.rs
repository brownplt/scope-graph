extern crate regex;
#[macro_use] extern crate lazy_static;

mod util;
mod preorder;
mod term;
mod rule;
pub mod parser;
pub mod resugar;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}


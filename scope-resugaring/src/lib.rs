extern crate regex;
#[macro_use] extern crate lazy_static;

mod util;
pub mod fresh;
pub mod preorder;
pub mod term;
pub mod scope;
pub mod rule;
mod source;
mod lexer;
mod parser;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}

/* [TODO]:
 *   Test case: error messages from the two Pi calculus rules:
 *   P | (v x) Q    =>  (v x) (P | Q)
 *   (v x) (P | Q)  =>  P | (v x) Q
 */

extern crate regex;
#[macro_use] extern crate lazy_static;

mod util;
mod preorder;
mod term;
mod resolve;
pub mod rule;
pub mod parser;
pub mod infer;
mod tests;

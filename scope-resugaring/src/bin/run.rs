extern crate scope_resugaring;

use std::time::SystemTime;

use self::scope_resugaring::rule::Language;
use self::scope_resugaring::parser::SourceFile;
use self::scope_resugaring::parser::parse_language;
use self::scope_resugaring::resugar::resugar_scope;

type Node = String;


fn main() {
    let total_timer = SystemTime::now();
    let mut lang_1: Language<Node, usize> =
        parse_language(&SourceFile::open("src/example_1.scope").unwrap());
    let mut lang_2: Language<Node, usize> =
        parse_language(&SourceFile::open("src/example_2.scope").unwrap());
    let mut lang_3: Language<Node, usize> =
        parse_language(&SourceFile::open("src/pyret.scope").unwrap());
    let resugar_timer = SystemTime::now();
    resugar_scope(&mut lang_1);
    resugar_scope(&mut lang_2);
    resugar_scope(&mut lang_3);
    let total_time = total_timer.elapsed();
    let resugar_time = resugar_timer.elapsed();

    println!("\n\n=============== Example 1 (Let) ================\n");
    println!("{}", lang_1.surf_scope);
    println!("\n\n=============== Example 2 (Let*) ===============\n");
    println!("{}", lang_2.surf_scope);
    println!("\n\n====================  Pyret  ===================\n");
    println!("{}", lang_3.surf_scope);

    println!("\nTotal time {:?}", total_time);
    println!("Resugar time {:?}", resugar_time);
}

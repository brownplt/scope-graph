extern crate scope_inference;

use std::time::SystemTime;

use self::scope_inference::rule::Language;
use self::scope_inference::parser::SourceFile;
use self::scope_inference::parser::parse_language;
use self::scope_inference::infer::infer_scope;


fn main() {
    let total_timer = SystemTime::now();
    let mut lang_1: Language<usize> =
        parse_language(&SourceFile::open("src/example_1.scope").unwrap());
    let mut lang_2: Language<usize> =
        parse_language(&SourceFile::open("src/example_2.scope").unwrap());
    let mut lang_3: Language<usize> =
        parse_language(&SourceFile::open("src/pyret.scope").unwrap());
    let infer_timer = SystemTime::now();
    infer_scope(&mut lang_1);
    infer_scope(&mut lang_2);
    infer_scope(&mut lang_3);
    let total_time = total_timer.elapsed();
    let infer_time = infer_timer.elapsed();

    println!("\n=============== Example 1 (Let) ================\n");
    println!("{}", lang_1.surf_scope);
    println!("\n=============== Example 2 (Let*) ===============\n");
    println!("{}", lang_2.surf_scope);
    println!("\n====================  Pyret  ===================\n");
    println!("{}", lang_3.surf_scope);

    println!("\nTotal time {:?}", total_time);
    println!("Infer time {:?}", infer_time);
}

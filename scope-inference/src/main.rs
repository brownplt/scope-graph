extern crate scope_inference;

use std::time::SystemTime;
use std::env;

use self::scope_inference::rule::Language;
use self::scope_inference::parser::SourceFile;
use self::scope_inference::parser::parse_language;
use self::scope_inference::infer::infer_scope;



fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        panic!("\n\nUsage:
    cargo run timing_test    : run and time test cases
    cargo run stdin          : infer scope from language file in stdin)
    cargo run filename.scope : infer scope from file\n\n");
    }
    if args[1] == "timing_test" {
        timing_test();
    } else if args[1] == "stdin" {
        let mut lang: Language<usize> = parse_language(&SourceFile::open_stdin()
                                                       .expect("Invalid language from stdin"));
        infer_scope(&mut lang);
        println!("{}", lang.surf_scope);
    } else {
        let mut lang: Language<usize> = parse_language(&SourceFile::open(&args[1])
                                                       .expect("Could not open file"));
        infer_scope(&mut lang);
        println!("{}", lang.surf_scope);
    }
}

fn timing_test() {
    let total_timer = SystemTime::now();
    let mut lang_1: Language<usize> =
        parse_language(&SourceFile::open("src/examples/example_1.scope").unwrap());
    let mut lang_2: Language<usize> =
        parse_language(&SourceFile::open("src/examples/example_2.scope").unwrap());
    let mut lang_4: Language<usize> =
        parse_language(&SourceFile::open("src/examples/list_comprehension.scope").unwrap());
    let mut lang_5: Language<usize> =
        parse_language(&SourceFile::open("src/examples/pyret.scope").unwrap());
    let mut lang_6: Language<usize> =
        parse_language(&SourceFile::open("src/examples/r5rs.scope").unwrap());
    let infer_timer = SystemTime::now();
    infer_scope(&mut lang_1);
    infer_scope(&mut lang_2);
    infer_scope(&mut lang_4);
    infer_scope(&mut lang_5);
    infer_scope(&mut lang_6);
    let total_time = total_timer.elapsed();
    let infer_time = infer_timer.elapsed();

    println!("\n=============== Example 1 (Let) ================\n");
    println!("{}", lang_1.surf_scope);
    println!("\n=============== Example 2 (Let*) ===============\n");
    println!("{}", lang_2.surf_scope);
    println!("\n=============== Haskell List Comprehensions ====\n");
    println!("{}", lang_4.surf_scope);
    println!("\n====================  Pyret  ===================\n");
    println!("{}", lang_5.surf_scope);
    println!("\n===============  R5RS Scheme  ==================\n");
    println!("{}", lang_6.surf_scope);

    println!("\nTotal time {:?}", total_time);
    println!("Infer time {:?}", infer_time);
}

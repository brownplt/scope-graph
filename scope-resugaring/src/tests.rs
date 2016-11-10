#[cfg(test)]
mod tests {
    use resugar::*;
    use term::{RewriteRule};
    use rule::{Fact, ScopeRule, Language};
    use parser::SourceFile;
    use parser::{parse_rewrite_rule, parse_language, parse_fact};

    type Node = String;

    #[test]
    fn constraint_generation() {
        let rule_1: RewriteRule<Node, usize> =
            parse_rewrite_rule(&SourceFile::from_str(
                "rule (Let a b c) => (Apply (Lambda a c) b)" ));

        let actual_constraints: Vec<String> = gen_constrs(&rule_1).iter()
            .map(|c| { format!("{}", c) })
            .collect();

        // Notation: ⊥ means R↓, ⊤ means R↑
        let expected_constraints = [
            "Let: R↑ ⋖ R↓   iff   Apply: R↑ ⋖ R↓",
            "Let: R↑ ⋖ 1   iff   Apply: R↑ ⋖ 1 & Lambda: R↑ ⋖ 1",
            "Let: R↑ ⋖ 2   iff   Apply: R↑ ⋖ 2",
            "Let: R↑ ⋖ 3   iff   Apply: R↑ ⋖ 1 & Lambda: R↑ ⋖ 2",
            "Let: 1 ⋖ R↓   iff   Apply: 1 ⋖ R↓ & Lambda: 1 ⋖ R↓",
            "Let: 1 ⋖ 1   iff   Lambda: 1 ⋖ 1",
            "Let: 1 ⋖ 2   iff   Apply: 1 ⋖ 2 & Lambda: 1 ⋖ R↓",
            "Let: 1 ⋖ 3   iff   Lambda: 1 ⋖ 2",
            "Let: 2 ⋖ R↓   iff   Apply: 2 ⋖ R↓",
            "Let: 2 ⋖ 1   iff   Apply: 2 ⋖ 1 & Lambda: R↑ ⋖ 1",
            "Let: 2 ⋖ 2   iff   Apply: 2 ⋖ 2",
            "Let: 2 ⋖ 3   iff   Apply: 2 ⋖ 1 & Lambda: R↑ ⋖ 2",
            "Let: 3 ⋖ R↓   iff   Apply: 1 ⋖ R↓ & Lambda: 2 ⋖ R↓",
            "Let: 3 ⋖ 1   iff   Lambda: 2 ⋖ 1",
            "Let: 3 ⋖ 2   iff   Apply: 1 ⋖ 2 & Lambda: 2 ⋖ R↓",
            "Let: 3 ⋖ 3   iff   Lambda: 2 ⋖ 2"];

        assert_eq!(actual_constraints.as_slice(), expected_constraints);
    }

    #[test]
    fn constraint_solving() {

        fn has_fact(rule: &ScopeRule<Node>, fact: &str) -> bool {
            let fact = parse_fact(&SourceFile::from_str(fact));
            rule.lt(fact.left, fact.right)
        }


        let mut lang_1: Language<Node, usize> =
            parse_language(&SourceFile::open("src/example_1.scope").unwrap());
        let mut lang_2: Language<Node, usize> =
            parse_language(&SourceFile::open("src/example_2.scope").unwrap());
        let mut lang_3: Language<Node, usize> =
            parse_language(&SourceFile::open("src/pyret.scope").unwrap());
        resugar_scope(&mut lang_1);
        resugar_scope(&mut lang_2);
        resugar_scope(&mut lang_3);

        
        // Example 1 from the paper (section 2.1: Single-arm Let)

        // (Let statement)
        // child 1: name
        // child 2: definition
        // child 3: body
        let ref let_rule = lang_1.surf_scope.rules["Let"];
        let let_facts: Vec<Fact<Node>> = let_rule.iter().collect();
        assert_eq!(let_facts.len(), 4);
        assert!(has_fact(let_rule, "import 1;"));
        assert!(has_fact(let_rule, "import 2;"));
        assert!(has_fact(let_rule, "import 3;"));
        assert!(has_fact(let_rule, "bind 1 in 3;"));
        


        // Example 2 from the paper (section 2.2: Multi-arm Let*)

        // (Let* statement)
        // child 1: bindings
        // child 2: body
        let ref let_rule = lang_2.surf_scope.rules["Let"];
        let let_facts: Vec<Fact<Node>> = let_rule.iter().collect();
        assert_eq!(let_facts.len(), 3);
        assert!(has_fact(let_rule, "import 1;"));
        assert!(has_fact(let_rule, "import 2;"));
        assert!(has_fact(let_rule, "bind 1 in 2;"));

        // (Let* binding)
        // child 1: name
        // child 2: definition
        // child 3: body
        let ref bind_rule = lang_2.surf_scope.rules["Bind"];
        let bind_facts: Vec<Fact<Node>> = bind_rule.iter().collect();
        assert_eq!(bind_facts.len(), 6);
        assert!(has_fact(bind_rule, "import 1;"));
        assert!(has_fact(bind_rule, "import 2;"));
        assert!(has_fact(bind_rule, "import 3;"));
        assert!(has_fact(bind_rule, "bind 1 in 3;"));
        assert!(has_fact(bind_rule, "export 1;"));
        assert!(has_fact(bind_rule, "export 3;"));



        // Pyret language - for loop

        // (For loop)
        // child 1: iterating function
        // child 2: binding list
        // child 4: for loop body
        let ref for_rule = lang_3.surf_scope.rules["For"];
        let for_facts: Vec<Fact<Node>> = for_rule.iter().collect();
        assert_eq!(for_facts.len(), 4);
        assert!(has_fact(for_rule, "import 1;"));
        assert!(has_fact(for_rule, "import 2;"));
        assert!(has_fact(for_rule, "import 3;"));
        assert!(has_fact(for_rule, "bind 2 in 3;"));

        // (For loop binding)
        // child 1: parameter
        // child 2: value
        // child 3: rest of bindings
        let ref bind_rule = lang_3.surf_scope.rules["From"];
        let bind_facts: Vec<Fact<Node>> = bind_rule.iter().collect();
        assert_eq!(bind_facts.len(), 5);
        assert!(has_fact(bind_rule, "import 1;"));
        assert!(has_fact(bind_rule, "import 2;"));
        assert!(has_fact(bind_rule, "import 3;"));
        assert!(has_fact(bind_rule, "export 1;"));
        assert!(has_fact(bind_rule, "export 3;"));

        // (Function definition)
        // child 1: function name
        // child 2: parameters
        // child 3: function body
        // child 4: rest of program
        let ref fun_rule = lang_3.surf_scope.rules["Fun"];
        let fun_facts: Vec<Fact<Node>> = fun_rule.iter().collect();
        assert_eq!(fun_facts.len(), 11);
        assert!(has_fact(fun_rule, "import 1;"));
        assert!(has_fact(fun_rule, "import 2;"));
        assert!(has_fact(fun_rule, "import 3;"));
        assert!(has_fact(fun_rule, "import 4;"));
        assert!(has_fact(fun_rule, "export 1;"));
        assert!(has_fact(fun_rule, "export 4;"));
        assert!(has_fact(fun_rule, "bind 1 in 4;"));
        assert!(has_fact(fun_rule, "bind 1 in 2;"));
        assert!(has_fact(fun_rule, "bind 1 in 3;"));
        assert!(has_fact(fun_rule, "bind 2 in 3;"));
        assert!(has_fact(fun_rule, "bind 1 in 1;"));

        // (Let statement)
        // child 1: name
        // child 2: definition
        // child 3: rest of program
        let ref let_rule = lang_3.surf_scope.rules["Let"];
        let let_facts: Vec<Fact<Node>> = let_rule.iter().collect();
        assert_eq!(let_facts.len(), 4);
        assert!(has_fact(let_rule, "import 1;"));
        assert!(has_fact(let_rule, "import 2;"));
        assert!(has_fact(let_rule, "import 3;"));
        assert!(has_fact(let_rule, "bind 1 in 3;"));

        
    }

}

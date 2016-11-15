#[cfg(test)]
mod tests {
    use std::fmt;
    use infer::*;
    use term::{Path, RewriteRule, Term};
    use rule::{Fact, ScopeRule, Language};
    use parser::SourceFile;
    use parser::{parse_rewrite_rule, parse_language, parse_fact};
    use resolve::{resolve_bindings};

    /// Constraint Generation test (section 5.2)
    #[test]
    fn constraint_generation() {
        let rule_1: RewriteRule<usize> =
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
    #[should_panic(expected = "The variable reference y is unbound in the right hand side of the rule:")]
    fn hygiene_check_unbound() {
        load_lang("src/test_hygiene_check_unbound.scope");
    }

    #[test]
    fn binding() {
        let lang = load_lang("src/test_binding.scope");
        let ref term1 = lang.rewrite_rules[2].right;
        let ref term2 = lang.rewrite_rules[3].right;
        assert!(has_binding(term1, &lang, (vec!(2, 1), vec!(1))));
        assert!(has_binding(term2, &lang, (vec!(2, 1, 2), vec!(1))));
        assert!(has_binding(term2, &lang, (vec!(2, 2), vec!(2, 1, 1))));
    }

    /// Example 1 from the paper (section 2.1: Single-arm Let)
    #[test]
    fn example_1() {
        let lang = load_lang("src/example_1.scope");

        // (Let statement)
        // child 1: name
        // child 2: definition
        // child 3: body
        let ref let_rule = lang.surf_scope.rules["Let"];
        let let_facts: Vec<Fact> = let_rule.iter().collect();
        assert_eq!(let_facts.len(), 4);
        assert!(has_fact(let_rule, "import 1;"));
        assert!(has_fact(let_rule, "import 2;"));
        assert!(has_fact(let_rule, "import 3;"));
        assert!(has_fact(let_rule, "bind 1 in 3;"));
    }

    
    /// Example 2 from the paper (section 2.2: Multi-arm Let*)
    #[test]
    fn example_2() {
        let lang = load_lang("src/example_2.scope");

        // (Let* statement)
        // child 1: bindings
        // child 2: body
        let ref let_rule = lang.surf_scope.rules["Let"];
        let let_facts: Vec<Fact> = let_rule.iter().collect();
        assert_eq!(let_facts.len(), 3);
        assert!(has_fact(let_rule, "import 1;"));
        assert!(has_fact(let_rule, "import 2;"));
        assert!(has_fact(let_rule, "bind 1 in 2;"));

        // (Let* binding)
        // child 1: name
        // child 2: definition
        // child 3: body
        let ref bind_rule = lang.surf_scope.rules["Bind"];
        let bind_facts: Vec<Fact> = bind_rule.iter().collect();
        assert_eq!(bind_facts.len(), 6);
        assert!(has_fact(bind_rule, "import 1;"));
        assert!(has_fact(bind_rule, "import 2;"));
        assert!(has_fact(bind_rule, "import 3;"));
        assert!(has_fact(bind_rule, "bind 1 in 3;"));
        assert!(has_fact(bind_rule, "export 1;"));
        assert!(has_fact(bind_rule, "export 3;"));
    }


    /// The Pyret examples from the paper (section 6)
    #[test]
    fn example_pyret() {
        let lang = load_lang("src/pyret.scope");

        // (For loop)
        // child 1: iterating function
        // child 2: binding list
        // child 4: for loop body
        let ref for_rule = lang.surf_scope.rules["For"];
        let for_facts: Vec<Fact> = for_rule.iter().collect();
        assert_eq!(for_facts.len(), 4);
        assert!(has_fact(for_rule, "import 1;"));
        assert!(has_fact(for_rule, "import 2;"));
        assert!(has_fact(for_rule, "import 3;"));
        assert!(has_fact(for_rule, "bind 2 in 3;"));

        // (For loop binding)
        // child 1: parameter
        // child 2: value
        // child 3: rest of bindings
        let ref bind_rule = lang.surf_scope.rules["From"];
        let bind_facts: Vec<Fact> = bind_rule.iter().collect();
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
        let ref fun_rule = lang.surf_scope.rules["Fun"];
        let fun_facts: Vec<Fact> = fun_rule.iter().collect();
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
        let ref let_rule = lang.surf_scope.rules["Let"];
        let let_facts: Vec<Fact> = let_rule.iter().collect();
        assert_eq!(let_facts.len(), 4);
        assert!(has_fact(let_rule, "import 1;"));
        assert!(has_fact(let_rule, "import 2;"));
        assert!(has_fact(let_rule, "import 3;"));
        assert!(has_fact(let_rule, "bind 1 in 3;"));

        
    }

    // Load a language from a file and infer its scope.
    fn load_lang(filename: &str) -> Language<usize> {
        let mut lang: Language<usize> =
            parse_language(&SourceFile::open(filename)
                           .expect(&format!("Could not load file: {}", filename)));
        infer_scope(&mut lang);
        lang
    }

    // Check that a rule contains at least a particular fact
    fn has_fact(rule: &ScopeRule, fact: &str) -> bool {
        let fact = parse_fact(&SourceFile::from_str(fact));
        rule.lt(fact.left, fact.right)
    }

    // Check that a rule's RHS contains a particular variable binding
    fn has_binding<Val>(term: &Term<Val>,
                        lang: &Language<Val>,
                        binding: (Path, Path)) -> bool
        where Val : fmt::Display
    {
        let bindings = resolve_bindings(&lang.surf_scope, term);
        let (refn, decl) = binding;
        match bindings.get(&refn) {
            None => false,
            Some(&(_, ref decls)) => {
                decls.len() == 1 && decls[0] == decl
            }
        }
    }
}

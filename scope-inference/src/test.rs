#[cfg(test)]
mod tests {
    use std::fmt;
    use infer::*;
    use term::{Path, RewriteRule, Term};
    use rule::{ScopeRule, Language};
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

        // Notation:
        // R↑ ⋖ R↓ means `re-export`
        // R↑ ⋖ i  means `export i` (where i is an integer)
        // i ⋖ R↓  means `import i` (where i is an integer)
        // i ⋖ j   means `bind i in j` (where i and j are integers)
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
        load_lang("src/tests/hygiene_check_unbound.scope");
    }

    #[test]
    #[should_panic(expected = "The variable reference as_refn$z is unbound in the right hand side of the rule:")]
    fn hole_as_refn_check_unbound() {
        load_lang("src/tests/hole_as_refn_check_unbound.scope");
    }

    #[test]
    #[should_panic(expected = "")]
    fn check_disjoint() {
        load_lang("src/tests/disjointness.scope");
    }

    #[test]
    #[should_panic(expected = "")]
    fn check_disjoint_letrec() {
        load_lang("src/tests/disjointness_letrec.scope");
    }

    #[test]
    #[should_panic(expected = "Term `Lambda` constructed with the wrong number of children. Found 1 children, but expected 2 children.")]
    fn check_arity_error() {
        load_lang("src/tests/arity_error.scope");
    }

    #[test]
    #[should_panic(expected = "Hole `name` used both under 1 ellipses and under 0 ellipses. Holes must be used at consistent ellipsis depth.")]
    fn check_ellipses_depth_error() {
        load_lang("src/tests/ellipses_depth_test.scope");
    }
    
    #[test]
    fn binding() {
        let lang = load_lang("src/tests/binding.scope");
        let ref term1 = lang.rewrite_rules[2].right;
        let ref term2 = lang.rewrite_rules[3].right;
        assert!(has_binding(term1, &lang, (vec!(2, 1), vec!(1))));
        assert!(has_binding(term2, &lang, (vec!(2, 1, 2), vec!(1))));
        assert!(has_binding(term2, &lang, (vec!(2, 2), vec!(2, 1, 1))));
    }

    /// Example 1 from the paper (section 2.1: Single-arm Let)
    #[test]
    fn example_1() {
        let lang = load_lang("src/examples/single_arm_let.scope");

        // (Let statement)
        let ref let_rule = lang.surf_scope.rules["Let"];
        let children = make_children(vec!("name", "definition", "body"));
        assert_eq!(let_rule.iter().count(), 4);
        assert!(has_fact(let_rule, &children, "import name;"));
        assert!(has_fact(let_rule, &children, "import definition;"));
        assert!(has_fact(let_rule, &children, "import body;"));
        assert!(has_fact(let_rule, &children, "bind name in body;"));
    }

    
    /// Example 2 from the paper (section 2.2: Multi-arm Let*)
    #[test]
    fn example_2() {
        let lang = load_lang("src/examples/multi_arm_let.scope");

        // (Let* statement)
        let ref let_rule = lang.surf_scope.rules["Let"];
        let children = make_children(vec!("bindings", "body"));
        assert_eq!(let_rule.iter().count(), 3);
        assert!(has_fact(let_rule, &children, "import bindings;"));
        assert!(has_fact(let_rule, &children, "import body;"));
        assert!(has_fact(let_rule, &children, "bind bindings in body;"));

        // (Let* binding)
        let ref bind_rule = lang.surf_scope.rules["Bind"];
        let children = make_children(vec!("name", "definition", "body"));
        assert_eq!(bind_rule.iter().count(), 6);
        assert!(has_fact(bind_rule, &children, "import name;"));
        assert!(has_fact(bind_rule, &children, "import definition;"));
        assert!(has_fact(bind_rule, &children, "import body;"));
        assert!(has_fact(bind_rule, &children, "bind name in body;"));
        assert!(has_fact(bind_rule, &children, "export name;"));
        assert!(has_fact(bind_rule, &children, "export body;"));
    }
    
    #[test]
    fn example_r5rs() {
        let lang = load_lang("src/examples/r5rs.scope");
        run_r5rs_tests(lang);
    }

    #[test]
    fn example_r5rs_ellipses() {
        let lang = load_lang("src/examples/r5rs_ellipses.scope");
        run_r5rs_tests(lang);
    }

    fn run_r5rs_tests(lang: Language<usize>) {
        // See R5RS, section 7.3 "derived expression types"
        // http://www.schemers.org/Documents/Standards/R5RS/HTML/

        // (Let*)
        let ref rule = lang.surf_scope.rules["Letstar"];
        let children = make_children(vec!("bindings", "body"));
        assert_eq!(rule.iter().count(), 3);
        assert!(has_fact(rule, &children, "import bindings;"));
        assert!(has_fact(rule, &children, "import body;"));
        assert!(has_fact(rule, &children, "bind bindings in body;"));

        // (Let* binding)
        let ref rule = lang.surf_scope.rules["LetstarBind"];
        let children = make_children(vec!("name", "definition", "rest"));
        assert_eq!(rule.iter().count(), 6);
        assert!(has_fact(rule, &children, "import name;"));
        assert!(has_fact(rule, &children, "import definition;"));
        assert!(has_fact(rule, &children, "import rest;"));
        assert!(has_fact(rule, &children, "bind name in rest;"));
        assert!(has_fact(rule, &children, "export name;"));
        assert!(has_fact(rule, &children, "export rest;"));

        // (Letrec)
        let ref rule = lang.surf_scope.rules["Letrec"];
        let children = make_children(vec!("bindings", "body"));
        assert_eq!(rule.iter().count(), 3);
        assert!(has_fact(rule, &children, "import bindings;"));
        assert!(has_fact(rule, &children, "import body;"));
        assert!(has_fact(rule, &children, "bind bindings in body;"));
        
        // (Letrec binding)
        let ref rule = lang.surf_scope.rules["LetrecBind"];
        let children = make_children(vec!("name", "definition", "rest"));
        assert_eq!(rule.iter().count(), 8);
        assert!(has_fact(rule, &children, "import name;"));
        assert!(has_fact(rule, &children, "import definition;"));
        assert!(has_fact(rule, &children, "import rest;"));
        assert!(has_fact(rule, &children, "export name;"));
        assert!(has_fact(rule, &children, "export rest;"));
        assert!(has_fact(rule, &children, "bind name in definition;"));
        assert!(has_fact(rule, &children, "bind rest in definition;"));
        assert!(has_fact(rule, &children, "bind name in rest;"));
        
        // (Regular Let)
        let ref rule = lang.surf_scope.rules["Let"];
        let children = make_children(vec!("bindings", "body"));
        assert_eq!(rule.iter().count(), 3);
        assert!(has_fact(rule, &children, "import bindings;"));
        assert!(has_fact(rule, &children, "import body;"));
        assert!(has_fact(rule, &children, "bind bindings in body;"));

        // (Regular Let binding)
        let ref rule = lang.surf_scope.rules["LetBind"];
        let children = make_children(vec!("name", "definition", "rest"));
        assert_eq!(rule.iter().count(), 5);
        assert!(has_fact(rule, &children, "import name;"));
        assert!(has_fact(rule, &children, "import definition;"));
        assert!(has_fact(rule, &children, "import rest;"));
        assert!(has_fact(rule, &children, "export name;"));
        assert!(has_fact(rule, &children, "export rest;"));
        
        // ("Named" Let loop)
        let ref rule = lang.surf_scope.rules["NamedLet"];
        let children = make_children(vec!("tag", "bindings", "body"));
        assert_eq!(rule.iter().count(), 6);
        assert!(has_fact(rule, &children, "import tag;"));
        assert!(has_fact(rule, &children, "import bindings;"));
        assert!(has_fact(rule, &children, "import body;"));
        assert!(has_fact(rule, &children, "bind tag in bindings;"));
        assert!(has_fact(rule, &children, "bind bindings in body;"));
        assert!(has_fact(rule, &children, "bind tag in body;"));

        // ("Named" Let binding)
        let ref rule = lang.surf_scope.rules["NamedLetBind"];
        let children = make_children(vec!("name", "definition", "rest"));
        assert_eq!(rule.iter().count(), 5);
        assert!(has_fact(rule, &children, "import name;"));
        assert!(has_fact(rule, &children, "import definition;"));
        assert!(has_fact(rule, &children, "import rest;"));
        assert!(has_fact(rule, &children, "export name;"));
        assert!(has_fact(rule, &children, "export rest;"));
    }

    #[test]
    fn example_list_comprehension() {
        // See Haskell Standard, section 3.11: List Comprehensions
        // https://www.haskell.org/onlinereport/derived.html
        let lang = load_lang("src/examples/list_comprehension.scope");

        // [ e | Q ]
        //   1   2
        let ref rule = lang.surf_scope.rules["ListCompr"];
        let children = make_children(vec!("e", "Q"));
        assert_eq!(rule.iter().count(), 3);
        assert!(has_fact(rule, &children, "import e;"));
        assert!(has_fact(rule, &children, "import Q;"));
        assert!(has_fact(rule, &children, "bind Q in e;"));

        // Boolean Guards
        // b, Q
        // 1  2
        let ref rule = lang.surf_scope.rules["BooleanGuard"];
        let children = make_children(vec!("b", "Q"));
        assert_eq!(rule.iter().count(), 3);
        assert!(has_fact(rule, &children, "import b;"));
        assert!(has_fact(rule, &children, "import Q;"));
        assert!(has_fact(rule, &children, "export Q;"));

        // Generators
        // p <- l, Q
        // 1    2  3
        let ref rule = lang.surf_scope.rules["Generator"];
        let children = make_children(vec!("p", "l", "Q"));
        assert_eq!(rule.iter().count(), 6);
        assert!(has_fact(rule, &children, "import p;"));
        assert!(has_fact(rule, &children, "import l;"));
        assert!(has_fact(rule, &children, "import Q;"));
        assert!(has_fact(rule, &children, "bind p in Q;"));
        assert!(has_fact(rule, &children, "export p;"));
        assert!(has_fact(rule, &children, "export Q;"));

        // Local bind
        // let decls, Q
        //      1     2
        let ref rule = lang.surf_scope.rules["LocalBind"];
        let children = make_children(vec!("decls", "Q"));
        assert_eq!(rule.iter().count(), 5);
        assert!(has_fact(rule, &children, "import decls;"));
        assert!(has_fact(rule, &children, "import Q;"));
        assert!(has_fact(rule, &children, "bind decls in Q;"));
        assert!(has_fact(rule, &children, "export decls;"));
        assert!(has_fact(rule, &children, "export Q;"));
    }

    #[test]
    fn example_pyret() {
        let lang = load_lang("src/examples/pyret.scope");
        run_pyret_tests(lang);
    }

    #[test]
    fn example_pyret_ellipses() {
        let lang = load_lang("src/examples/pyret_ellipses.scope");
        run_pyret_tests(lang);
    }

    /// The Pyret examples from the paper (section 6)
    fn run_pyret_tests(lang: Language<usize>) {
        // (For loop)
        // child 1: iterating function
        // child 2: binding list
        // child 4: for loop body
        let ref for_rule = lang.surf_scope.rules["For"];
        let children = make_children(vec!("func", "froms", "body"));
        assert_eq!(for_rule.iter().count(), 4);
        assert!(has_fact(for_rule, &children, "import func;"));
        assert!(has_fact(for_rule, &children, "import froms;"));
        assert!(has_fact(for_rule, &children, "import body;"));
        assert!(has_fact(for_rule, &children, "bind froms in body;"));

        // (For loop binding)
        // child 1: parameter
        // child 2: value
        // child 3: rest of bindings
        let ref bind_rule = lang.surf_scope.rules["From"];
        let children = make_children(vec!("param", "value", "rest"));
        assert_eq!(bind_rule.iter().count(), 5);
        assert!(has_fact(bind_rule, &children, "import param;"));
        assert!(has_fact(bind_rule, &children, "import value;"));
        assert!(has_fact(bind_rule, &children, "import rest;"));
        assert!(has_fact(bind_rule, &children, "export param;"));
        assert!(has_fact(bind_rule, &children, "export rest;"));

        // (Function definition)
        // child 1: function name
        // child 2: parameters
        // child 3: function body
        // child 4: rest of program
        let ref fun_rule = lang.surf_scope.rules["Fun"];
        let children = make_children(vec!("name", "params", "body", "rest"));
        assert_eq!(fun_rule.iter().count(), 10);
        assert!(has_fact(fun_rule, &children, "import name;"));
        assert!(has_fact(fun_rule, &children, "import params;"));
        assert!(has_fact(fun_rule, &children, "import body;"));
        assert!(has_fact(fun_rule, &children, "import rest;"));
        assert!(has_fact(fun_rule, &children, "export name;"));
        assert!(has_fact(fun_rule, &children, "export rest;"));
        assert!(has_fact(fun_rule, &children, "bind name in rest;"));
        assert!(has_fact(fun_rule, &children, "bind name in params;"));
        assert!(has_fact(fun_rule, &children, "bind name in body;"));
        assert!(has_fact(fun_rule, &children, "bind params in body;"));

        // (Let statement)
        // child name: name
        // child 2: definition
        // child 3: rest of program
        let ref let_rule = lang.surf_scope.rules["Let"];
        let children = make_children(vec!("name", "definition", "rest"));
        assert_eq!(let_rule.iter().count(), 4);
        assert!(has_fact(let_rule, &children, "import name;"));
        assert!(has_fact(let_rule, &children, "import definition;"));
        assert!(has_fact(let_rule, &children, "import rest;"));
        assert!(has_fact(let_rule, &children, "bind name in rest;"));
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
    fn has_fact(rule: &ScopeRule, children: &Vec<String>, fact: &str) -> bool {
        let fact = parse_fact(&SourceFile::from_str(fact), children);
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

    fn make_children(v: Vec<&'static str>) -> Vec<String> {
        v.into_iter().map(|s| s.to_string()).collect()
    }
}

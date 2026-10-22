#[cfg(test)]
mod tests {
    use crate::ast::{ResolvedCommand, RuleEvalMode, sanitize_internal_names};
    use crate::proof::{Justification, ProofId, ProofStore};
    use crate::{
        CommandOutput, EGraph, Error, ProofEncodingUnsupportedReason, ProvedVariants, TermDag,
        TermId, add_primitive_with_validator,
    };
    use std::collections::HashSet;

    fn term_encode(source: &str) -> Vec<ResolvedCommand> {
        let mut egraph = crate::EGraph::new_with_term_encoding();
        egraph.resolve_program(None, source).unwrap()
    }

    /// The proof encoder reads body variables' `term_proof`s from the RHS via
    /// `:unsafe-seminaive` lookups. Assert this produces the same database as
    /// the safe baseline (the same rules annotated `:naive`), for a hardcoded
    /// handful of files (running it across all tests would be too slow).
    #[test]
    fn unsafe_seminaive_matches_naive() {
        let files = [
            "tests/calc.egg",
            "tests/integer_math.egg",
            "tests/fibonacci-demand.egg",
            "tests/until.egg",
        ];

        for file in files {
            let source = std::fs::read_to_string(file)
                .unwrap_or_else(|e| panic!("couldn't read {file}: {e}"));

            // Guard against a vacuous comparison: the two encodings must differ.
            let encode = |naive: bool| -> String {
                let mut egraph = crate::EGraph::new_with_proofs();
                egraph.proof_state.force_proof_naive = naive;
                egraph
                    .resolve_program(Some(file.to_string()), &source)
                    .unwrap_or_else(|e| panic!("{file} resolve (naive={naive}) failed: {e}"))
                    .iter()
                    .map(|cmd| cmd.to_string())
                    .collect::<Vec<_>>()
                    .join("\n")
            };
            assert!(
                encode(false).contains(":unsafe-seminaive") && encode(false) != encode(true),
                "expected {file} to exercise the `:unsafe-seminaive` encoding path"
            );

            // `print-size` summarizes the whole database (per-function row
            // counts, sorted) deterministically.
            let program = format!("{source}\n(print-size)");

            let run = |naive: bool| -> Vec<CommandOutput> {
                let mut egraph = crate::EGraph::new_with_proofs();
                egraph.proof_state.force_proof_naive = naive;
                egraph
                    .parse_and_run_program(Some(file.to_string()), &program)
                    .unwrap_or_else(|e| panic!("{file} (naive={naive}) failed: {e}"))
            };

            let unsafe_seminaive = CommandOutput::snapshot_stable_under_proof_encoding(&run(false));
            let naive = CommandOutput::snapshot_stable_under_proof_encoding(&run(true));

            assert_eq!(
                unsafe_seminaive, naive,
                ":unsafe-seminaive and :naive proof encodings disagree for {file}"
            );
        }
    }

    /// A user rule marked `:naive` must stay `:naive` through proof encoding;
    /// dropping it would silently switch the rule to seminaive evaluation.
    #[test]
    fn proof_encoding_preserves_naive() {
        // The second case binds an eq-sort body var, whose `term_proof` RHS
        // read would otherwise force `:unsafe-seminaive`. Both must stay naive.
        let cases = [
            r#"(relation r (i64))
               (relation s (i64))
               (rule ((r x)) ((s x)) :naive :name "keep")"#,
            r#"(sort Math)
               (constructor Num (i64) Math)
               (constructor Neg (Math) Math)
               (relation seen (Math))
               (rule ((Neg m)) ((seen m)) :naive :name "keep")"#,
        ];
        for source in cases {
            let mut egraph = crate::EGraph::new_with_proofs();
            let resolved = egraph.resolve_program(None, source).unwrap();
            let rule = resolved
                .iter()
                .find_map(|c| match c {
                    ResolvedCommand::Rule { rule } if rule.name == "keep" => Some(rule),
                    _ => None,
                })
                .expect("instrumented rule not found");
            assert_eq!(
                rule.eval_mode,
                RuleEvalMode::Naive,
                "proof encoding did not preserve :naive for:\n{source}"
            );
        }
    }

    #[test]
    fn proof_mode_allows_eq_sort_primitive_results_in_facts() {
        let mut egraph = EGraph::default();
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-id" = |x: #| -> # { x },
            validator
        );
        let mut egraph = egraph.with_proofs_enabled();

        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math
                  (Done)
                  (Num i64))
                (relation Seed (Math))

                (Seed (Num 1))

                (rule ((Seed y)
                       (= x (proof-id y)))
                      ((Done))
                      :name "use-proof-id")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    #[test]
    fn proof_support_rejects_naive_eq_sort_primitive_results_in_facts() {
        let mut egraph = EGraph::default();
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-id" = |x: #| -> # { x },
            validator
        );
        let mut egraph = egraph.with_proofs_enabled();

        let err = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math
                  (Done)
                  (Num i64))
                (relation Seed (Math))

                (rule ((Seed y)
                       (= x (proof-id y)))
                      ((Done))
                      :naive
                      :name "naive-use-proof-id")
                "#,
            )
            .unwrap_err();

        assert!(
            matches!(
                err,
                Error::UnsupportedProofCommand {
                    reason: ProofEncodingUnsupportedReason::NaiveEqSortPrimitiveFact,
                    ..
                }
            ),
            "expected NaiveEqSortPrimitiveFact, got {err:?}"
        );
    }

    #[test]
    fn proof_mode_allows_eq_container_primitive_results_in_facts() {
        // A real (presort-declared) eq-container sort, so the term/proof
        // encoding builds its rebuild primitive. A custom identity primitive
        // returns an existing eq-container value, exercising the
        // eq-container-primitive-result-in-a-fact path under proofs.
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                "#,
            )
            .unwrap();

        let eq_container_sort = egraph
            .type_info
            .get_sort_by_name("EqContainer")
            .expect("EqContainer sort")
            .clone();
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        add_primitive_with_validator!(
            &mut egraph,
            "proof-container-id" = |x: # (eq_container_sort)| -> # (eq_container_sort) { x },
            validator
        );
        let validator =
            |_: &mut TermDag, args: &[TermId]| -> Option<TermId> { args.first().copied() };
        let original_typechecking = egraph.proof_state.original_typechecking.as_mut().unwrap();
        add_primitive_with_validator!(
            &mut **original_typechecking,
            "proof-container-id" = |x: # (eq_container_sort)| -> # (eq_container_sort) { x },
            validator
        );

        egraph
            .parse_and_run_program(
                None,
                r#"
                (relation SeedContainer (EqContainer))
                (relation Done ())

                (SeedContainer (vec-of (Mk)))

                (rule ((SeedContainer ys)
                       (= xs (proof-container-id ys)))
                      ((Done))
                      :name "use-proof-container-id")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    // A container constructed in the query body and not used in an action: the
    // binding fact's proof is the container's reflexive `Eval`, which the rule
    // check re-derives with the typed primitive.
    #[test]
    fn proof_mode_query_constructed_container_not_used_in_action() {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                (relation SeedElem (E))
                (relation Done ())

                (SeedElem (Mk))

                (rule ((SeedElem e)
                       (= xs (vec-of e)))
                      ((Done))
                      :name "new-container-in-body")

                (run 1)
                (prove (Done))
                "#,
            )
            .unwrap();
    }

    // A container constructed in the query is a side condition with no carryable
    // proof (just an `Eval` marker), so it can't be used in an action. Proof mode
    // rejects such a rule rather than producing an unsound proof.
    #[test]
    fn proof_support_rejects_query_constructed_container_used_in_action() {
        let mut egraph = EGraph::new_with_proofs();
        let err = egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype E (Mk))
                (sort EqContainer (Vec E))
                (relation SeedElem (E))
                (relation Out (EqContainer))

                (rule ((SeedElem e)
                       (= xs (vec-of e)))
                      ((Out xs))
                      :name "new-container-in-action")
                "#,
            )
            .unwrap_err();
        assert!(
            matches!(
                err,
                Error::UnsupportedProofCommand {
                    reason: ProofEncodingUnsupportedReason::ContainerCreatedInQueryUsedInAction,
                    ..
                }
            ),
            "expected ContainerCreatedInQueryUsedInAction, got {err:?}"
        );
    }

    #[test]
    fn doc_example_add_function2() {
        let commands = term_encode(
            r#"
            (function add (i64 i64) i64 :merge old)
            (check (= (add 0 0) 0))
            "#,
        );

        let snapshot = sanitize_internal_names(&commands)
            .iter()
            .map(|cmd| cmd.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        insta::assert_snapshot!("doc_example_add_function2", snapshot);
    }

    #[test]
    fn doc_example_add_function1() {
        let commands = term_encode(
            r#"
(sort Math)
(constructor Add (i64 i64) Math)
(Add 1 2)
(rule ((Add a b))
      ((union (Add a b) (Add b a)))
     :name "commutativity")
(check (= (Add 1 2) (Add 2 1)))
            "#,
        );

        let snapshot = sanitize_internal_names(&commands)
            .iter()
            .map(|cmd| cmd.to_string())
            .collect::<Vec<_>>()
            .join("\n");

        insta::assert_snapshot!("doc_example_add_function1", snapshot);
    }

    const VARIANTS_PROGRAM: &str = r#"
        (datatype Math (Num i64) (Var String) (Add Math Math) (Mul Math Math))
        (rule ((= e (Add a b))) ((union e (Add b a))) :name "add-comm")
        (rule ((= e (Mul a (Add b c)))) ((union e (Add (Mul a b) (Mul a c)))) :name "distribute")
        (rule ((= e (Mul a (Num 1)))) ((union e a)) :name "mul-one")
        (let $start (Mul (Var "x") (Add (Num 1) (Var "y"))))
        (run 4)
    "#;
    const START_TERM: &str = r#"(Mul (Var "x") (Add (Num 1) (Var "y")))"#;

    fn variants_egraph() -> EGraph {
        let mut egraph = EGraph::new_with_proofs();
        egraph
            .parse_and_run_program(None, VARIANTS_PROGRAM)
            .unwrap();
        egraph
    }

    /// Proves `$start = (Add (Var "x") (Mul (Var "x") (Var "y")))` and returns
    /// the proof together with the program used to check it.
    fn forgeable_proof() -> (EGraph, ProofStore, ProofId) {
        let mut egraph = variants_egraph();
        let outputs = egraph
            .parse_and_run_program(
                None,
                r#"(prove (= $start (Add (Var "x") (Mul (Var "x") (Var "y")))))"#,
            )
            .unwrap();
        let Some(CommandOutput::ProveExists {
            proof_store,
            proof_id,
        }) = outputs.into_iter().next()
        else {
            panic!("expected a ProveExists output");
        };
        (egraph, proof_store, proof_id)
    }

    /// Every proof reachable from `root`, so a forgery is never applied to a node
    /// the checker does not visit.
    fn reachable_proofs(store: &ProofStore, root: ProofId) -> Vec<ProofId> {
        let mut seen = HashSet::new();
        let mut order = vec![];
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            order.push(id);
            match store.get(id).justification() {
                Justification::Rule { premise_proofs, .. } => stack.extend(premise_proofs),
                Justification::MergeFn {
                    old_proof,
                    new_proof,
                    ..
                } => stack.extend([*old_proof, *new_proof]),
                Justification::Trans(a, b) => stack.extend([*a, *b]),
                Justification::Sym(a) => stack.push(*a),
                Justification::Congr {
                    proof, child_proof, ..
                } => stack.extend([*proof, *child_proof]),
                Justification::ContainerNormalize { proof } => stack.push(*proof),
                Justification::Fiat | Justification::Eval => {}
            }
        }
        order
    }

    #[test]
    fn prove_variants_proves_every_extracted_variant() {
        // Reference: what `extract` returns on an identical e-graph.
        let mut reference = variants_egraph();
        let outputs = reference
            .parse_and_run_program(None, "(extract $start 20)")
            .unwrap();
        let Some(CommandOutput::ExtractVariants(_, extracted)) = outputs.first() else {
            panic!("expected ExtractVariants");
        };
        let expected_count = extracted.len();
        assert!(expected_count > 1, "the e-class should have several e-nodes");

        let mut egraph = variants_egraph();
        let outputs = egraph
            .parse_and_run_program(None, "(prove-variants $start 20)")
            .unwrap();
        let [CommandOutput::UserDefined(output)] = outputs.as_slice() else {
            panic!("expected a single user-defined output, got {outputs:?}");
        };
        let proved = output
            .as_ref()
            .as_any()
            .downcast_ref::<ProvedVariants>()
            .expect("output should be ProvedVariants");
        assert_eq!(proved.variants.len(), expected_count);

        for variant in &proved.variants {
            let proof = variant.proof_store.get(variant.proof_id);
            let dag = variant.proof_store.term_dag();
            assert_eq!(dag.to_string(proof.lhs()), START_TERM);
            assert_eq!(dag.to_string(proof.rhs()), variant.term);
        }
        let rendered: HashSet<&str> = proved.variants.iter().map(|v| v.term.as_str()).collect();
        let expected: HashSet<&str> = [
            r#"(Add (Var "x") (Mul (Var "x") (Var "y")))"#,
            r#"(Add (Mul (Var "x") (Var "y")) (Var "x"))"#,
            START_TERM,
        ]
        .into_iter()
        .collect();
        assert_eq!(rendered, expected);
        assert!(proved.to_string().contains("(variant "));
    }

    #[test]
    fn prove_variants_requires_proofs() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, VARIANTS_PROGRAM)
            .unwrap();
        let err = egraph
            .parse_and_run_program(None, "(prove-variants $start 20)")
            .unwrap_err();
        assert!(err.to_string().contains("proofs must be enabled"), "{err}");
    }

    #[test]
    fn prove_variants_rejects_bad_count() {
        let mut egraph = variants_egraph();
        for bad in [
            "(prove-variants $start 0)",
            r#"(prove-variants $start "three")"#,
            "(prove-variants $start (Num 1))",
            "(prove-variants $start)",
        ] {
            assert!(
                egraph.parse_and_run_program(None, bad).is_err(),
                "{bad} should be rejected"
            );
        }
    }

    #[test]
    fn checker_rejects_a_forged_proof() {
        let (egraph, mut store, proof_id) = forgeable_proof();
        store
            .check_proof(proof_id, &egraph.proof_check_program)
            .expect("the genuine proof should check");

        // Swap the rule a proof step claims to apply.
        let mut forged = store.clone();
        let rule_node = reachable_proofs(&forged, proof_id)
            .into_iter()
            .find(|id| {
                matches!(
                    forged.get(*id).justification(),
                    Justification::Rule { name, .. } if name == "distribute"
                )
            })
            .expect("the proof should apply `distribute`");
        let Justification::Rule { name, .. } = &mut forged.id_to_proof[rule_node].justification
        else {
            unreachable!()
        };
        *name = "mul-one".to_string();
        assert!(
            forged
                .check_proof(proof_id, &egraph.proof_check_program)
                .is_err(),
            "a proof citing the wrong rule must be rejected"
        );

        // Point a congruence step at the wrong child.
        let mut forged = store.clone();
        let congr_node = reachable_proofs(&forged, proof_id)
            .into_iter()
            .find(|id| matches!(forged.get(*id).justification(), Justification::Congr { .. }))
            .expect("the proof should contain a congruence step");
        let Justification::Congr { child_index, .. } =
            &mut forged.id_to_proof[congr_node].justification
        else {
            unreachable!()
        };
        *child_index ^= 1;
        assert!(
            forged
                .check_proof(proof_id, &egraph.proof_check_program)
                .is_err(),
            "a congruence step on the wrong child must be rejected"
        );
    }
}

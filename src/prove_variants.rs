//! The `prove-variants` command: a checked proof for every extracted variant.

use std::fmt;
use std::sync::Arc;

use crate::ast::{Command, Expr, Fact};
use crate::proof::{ProofId, ProofStore};
use crate::{CommandOutput, EGraph, Error, UserDefinedCommand, span};
use egglog_ast::generic_ast::Literal;

/// Name under which the command is registered.
pub(crate) const COMMAND_NAME: &str = "prove-variants";

/// One variant of the queried expression together with the proof that the
/// expression equals it.
#[derive(Debug)]
pub struct ProvedVariant {
    /// The variant, rendered as an egglog term.
    pub term: String,
    /// The store holding [`ProvedVariant::proof_id`]; each variant has its own.
    pub proof_store: ProofStore,
    /// The checked proof of `expr = term`.
    pub proof_id: ProofId,
}

/// Output of `(prove-variants <expr> <n>)`.
///
/// Holds one [`ProvedVariant`] per variant returned by `(extract <expr> <n>)`,
/// in the same order. Recover it from [`CommandOutput::UserDefined`] with
/// [`UserDefinedCommandOutput::as_any`](crate::UserDefinedCommandOutput::as_any).
#[derive(Debug)]
pub struct ProvedVariants {
    /// The proved variants.
    pub variants: Vec<ProvedVariant>,
}

impl fmt::Display for ProvedVariants {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for variant in &self.variants {
            writeln!(f, "(variant {})", variant.term)?;
            writeln!(f, "{}", variant.proof_store.proof_to_string(variant.proof_id))?;
        }
        Ok(())
    }
}

/// `(prove-variants <expr> <n>)`: proves `expr = variant` for each of the (at
/// most `n`) variants that `(extract <expr> <n>)` returns, i.e. one per e-node
/// of the e-class of `expr`, each built from its cheapest children.
///
/// Requires proofs mode (`EGraph::new_with_proofs`, or `--proofs` on the CLI).
pub(crate) struct ProveVariants;

impl UserDefinedCommand for ProveVariants {
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
        let span = args.first().map_or_else(|| span!(), |arg| arg.span());
        let bad_args = |msg: &str| Error::DesugarError(span.clone(), format!("{COMMAND_NAME}: {msg}"));

        let [expr, count] = args else {
            return Err(bad_args("expected two arguments: `(prove-variants <expr> <n>)`"));
        };
        match count {
            Expr::Lit(_, Literal::Int(n)) if *n >= 1 => {}
            _ => return Err(bad_args("the second argument must be an integer literal >= 1")),
        }
        if !egraph.are_proofs_enabled() {
            return Err(bad_args(
                "proofs must be enabled (use `--proofs` or `EGraph::new_with_proofs`)",
            ));
        }

        let outputs = egraph.run_program(vec![Command::Extract(
            span.clone(),
            expr.clone(),
            count.clone(),
        )])?;
        let Some(CommandOutput::ExtractVariants(termdag, terms)) = outputs.into_iter().next()
        else {
            return Err(bad_args("extraction did not return variants"));
        };

        let mut variants = Vec::with_capacity(terms.len());
        for term in terms {
            let variant = termdag.term_to_expr(&term, span.clone());
            let outputs = egraph.run_program(vec![Command::Prove(
                span.clone(),
                vec![Fact::Eq(span.clone(), expr.clone(), variant)],
            )])?;
            let Some(CommandOutput::ProveExists {
                proof_store,
                proof_id,
            }) = outputs.into_iter().next()
            else {
                return Err(bad_args("proving a variant did not return a proof"));
            };
            variants.push(ProvedVariant {
                term: termdag.to_string(term),
                proof_store,
                proof_id,
            });
        }
        Ok(vec![CommandOutput::UserDefined(Arc::new(ProvedVariants {
            variants,
        }))])
    }
}

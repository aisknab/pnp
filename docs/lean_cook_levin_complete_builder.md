# M230: complete all-input Cook–Levin formula builder

## Exact result

For every concrete polynomial-time verifier and every ordinary raw input,
one finite machine now produces the original canonical encoded Cook–Levin
formula. The domain includes empty and odd-length bitstrings. Construction,
handoff, output finalization and output size are bounded by polynomials in
the original input length, with the verifier fixed independently of that input.

The public endpoint in
[CookLevinCompleteBuilder.lean](../lean/PNP/Concrete/CookLevinCompleteBuilder.lean)
is:

    PNP.Concrete.CookLevin.cook_levin_formula_builder_checked_complete

Its type quantifies over every verifier and input, and identifies the output
of polynomialReduction verifier exactly with
(VerifierTableauProblem.mk verifier input).encodedFormula.
The reduction itself has type PolynomialReduction language CNFSAT;
its correctness uses the already proved original formula semantics.

The [M230 reconstruction plan](plans/2026-09-06-complete-cook-levin-formula-builder.md)
records the pinned legacy manuscript anchor, dependency edge, source-derived
construction and individual verified integration steps. This completes that
builder dependency, not the manuscript's residual minimisation argument.

## Construction and bounds

The machine composes BuilderRawInputLoop.machine verifier with
BuilderOutputFinalizer.machine, then uses the existing work-machine compiler.
The loop derives each request from the actual source and retained cursor,
traverses the entire verifier-derived schedule, and reaches the complete
canonical token stream. The finalizer removes the private workspace and
places exactly that stream on the ordinary output tape.

The original-input runtime polynomial is exactly the sum of
BuilderRawInputLoop.rawTimeBound verifier, the six-step inter-stage launch,
and BuilderOutputFinalizer.rawTimeBound verifier. The output-size polynomial
is BuilderCanonicalOutput.encodedSizeBound verifier.
The formulaBuilder definition is an actual machine leaf of PolynomialTimeFunction,
with total halting, runtime and encoded-output bounds. The ordinary-input
blank-equivalence bridge covers empty and odd-length source words; the
output bridge preserves exact bits, not merely satisfiability.

The formulaBuilder_rawRefinement_output theorem also proves exact output for the
recursive FunctionProgram.RawRefinement compiler. There is no caller-supplied
trace, route, family, rank map, semantic minimum or correctness certificate.

## Axiom and hostile-test boundary

The permanent [root-importing audit](../lean-audit/PNPConcreteCookLevinCompleteBuilderAxiomAudit.lean)
covers all ten public declarations. Seven machine, budget, function and
output/refinement declarations use only propext and Quot.sound.
The reduction and its two output endpoints additionally use the existing
formula-semantics dependency Classical.choice. This is a permitted Lean
standard axiom, not a project-specific axiom; no allowlist was widened.

The [Lean regressions](../lean-regression/PNPConcreteCookLevinCompleteBuilder.lean)
check the actual full interface. The
[source and publication contracts](../audits/lean-concrete-cook-levin-complete-builder0.test.mjs)
reject finite-only domains, supplied correctness data, missing launch cost,
weakened raw-output or reduction linkage, missing compiled evidence, and
unjustified progress credit.

The existing component proofs are reused. Root build and inventory extraction
belong to the core repository; PNPLabs must not compile this proof a second time.

## Fixed checkpoint and remaining obligations

M230 closes exactly reductions-complete-cook-levin-builder, the fixed
three-point all-input polynomial builder and packaged-reduction checkpoint.
No extra points are awarded for its internal component count or publication row.

Formal artefact coverage: 206 of 208 current scoped publication rows earned.
Risk-weighted proof completion estimate: 38%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

The separate named concrete NP-hardness or NP-completeness transport is still
open. So are deterministic CNFSAT ∈ P, unconditional residual minimisation
and ZeroSlack, the complete polynomial PCCMin algorithm and certificate bounds,
and PNP.Main.p_eq_np. The five global gates remain open, the compiled
project-specific axiom inventory is empty, and publication remains disabled.
This is not a proof of P = NP, a probability of success, or a delivery estimate.

The canonical [progress ledger](../status/PROOF_PROGRESS.json) records the
checkpoint, compiled evidence, source coordinate, score change and unchanged
uncertainty range. A major PNPLabs publication is warranted after the exact core
merge passes its release gates, because a fixed checkpoint and the public
all-input construction capability have changed.

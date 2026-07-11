# Lean finite charged-pipeline complexity interface

`lean/PNP/Concrete/Complexity.lean` defines concrete bitstring languages, proof-bearing P and NP
witnesses, and polynomial many-one reductions without storing executable Lean functions or string
code handles. `lean/PNP/Concrete/TapeHandoff.lean` supplies the observable first-blank output
decoder and a pure canonical handoff target. `lean/PNP/Concrete/PipelineTapeGeometry.lean` supplies
a two-track boundary frame with arbitrary exterior garbage and proved local move/expansion geometry.
`lean/PNP/Concrete/PipelineRefinement.lean` pins exact raw-machine refinement
contracts and proves the two machine-leaf cases. `lean/PNP/Concrete/Target.lean` names the
corresponding inactive target proposition. The explicit declarations in all five layers have empty
compiled axiom closures.

This is a finite charged-pipeline interface. Its leaves are concrete `Machine` values, but the
current formalization does not compile or refine an arbitrary composite pipeline into one raw
single-tape `Machine`. That missing link is recorded as
`Formal.ConcreteComplexityMachineLink`; consequently the publication map keeps
`standardComplexityModelEligible` false.

The refinement boundary is intentionally proof-bearing. A `FunctionProgram.RawRefinement` or
`DecisionProgram.RawRefinement` supplies one raw machine, one natural-polynomial budget, a
no-timeout theorem for every source input covered by `Halts`, and exact output or verdict equality.
The module constructs these witnesses for raw machine leaves, transports the output bound of a
`PolynomialTimeFunction`, and converts a `PolynomialTimeDecider` to a raw
`PolynomialTimeMachine` only when a refinement of its complete program is supplied. It does not
construct that refinement for composition or precomposition.

Clearing that blocker requires more than compiling the pipeline syntax. The refinement must prove
output preservation with polynomial overhead, realize both verifier input modes (including an
input-only-to-canonical-pair adapter), preserve the fixed tape-output convention, and establish
equivalence of the resulting raw-machine P/NP classes. Until all of those facts are proved, the
charged interpreter remains a distinct, not-yet-linked model.

## Finite programs and costs

`FunctionProgram` is closed syntax with two constructors:

- a concrete `Machine` run at a `NatPolynomial` transition budget; and
- sequential composition of two finite function programs.

Machine output is read from the focused cell through the first blank delimiter; it no longer depends
on the unobservable end of the represented `Tape.right` list. `FunctionProgram.eval` interprets the syntax,
and `FunctionProgram.chargedSteps` charges the first run, the size of the intermediate output for
handoff/copying, and the second run. `FunctionProgram.Halts` requires every leaf to reach a
designated accept or reject state rather than time out.

`PolynomialTimeFunction` adds proof-bearing `NatPolynomial` runtime and output-size bounds. For
composition, Lean constructs:

```text
first runtime
+ first output-size bound
+ second runtime with its input variable replaced by the first output-size bound
```

The composed output-size bound is obtained by the same polynomial substitution. The proofs use
monotonicity of the natural-polynomial syntax. Identity is a zero-step concrete machine whose
initial tape already contains the input.

`DecisionProgram` is likewise finite syntax: a terminal concrete machine, optionally preceded by a
finite `FunctionProgram`. Its charged cost includes preprocessing, intermediate-output handoff, and
the final decision run. `PolynomialTimeDecider` supplies a polynomial bound, halting proof, and the
exact equivalence between acceptance and language membership.

## P and bounded-certificate NP

A `Language` is a predicate on `BitString`. The class predicates are:

```lean
def InP (language : Language) : Prop :=
  Nonempty (PolynomialTimeDecider language)

def InNP (language : Language) : Prop :=
  Nonempty (PolynomialTimeVerifier language)
```

A verifier contains a finite `DecisionProgram` and a finite `VerifierInputMode`. Paired mode feeds
the decision program the canonical self-delimiting `BitString.pair input certificate`; input-only
mode is used when a deterministic decider ignores its certificate. A
`PolynomialTimeVerifier` contains:

- a `NatPolynomial` certificate-size bound;
- a `NatPolynomial` runtime bound;
- a proof that every bounded-certificate run halts;
- a proof of the charged runtime bound; and
- the usual existential acceptance equivalence for a bounded certificate.

`verifierFromDecider` constructs the P-to-NP embedding with input-only mode, certificate bound zero,
and the empty certificate. Therefore `p_subset_np` is a theorem constructed from executable syntax,
not a closure property supplied as a field.

## Polynomial reductions

`PolynomialReduction source target` stores a `PolynomialTimeFunction` and proves, for every input,
that source membership is equivalent to target membership of the computed output. The module
constructs and proves:

- `reduction_refl`, using the concrete identity pipeline;
- `reduction_comp`, composing programs in source-to-middle-to-target order;
- `reduction_transports_p`, by precomposing the target decider with the reduction; and
- `np_complete_in_p_implies_p_eq_np`, which combines P contained in NP with NP-hardness and
  reduction transport.

The concrete equality proposition is mutual inclusion:

```lean
def PEqualsNP : Prop :=
  (∀ language, InP language → InNP language) ∧
  (∀ language, InNP language → InP language)
```

No proposition extensionality is needed for that statement or theorem.

## Inactive target and publication boundary

`PNP.Main.ConcretePEqualsNP` is an axiom-free **definition** aliasing
`PNP.Concrete.PEqualsNP`. `PNP.Main.concretePEqualsNP_iff` only pins that definitional expansion. It
does not prove the target. There is no `PNP.Main.p_eq_np` compatibility/root theorem.

The expected target type/value, compatibility-root type, axiom-closure, and source-closure
activation fingerprints remain unset. The concrete target is visible to the compiled inventory,
but the compatibility root is absent and the fail-closed publication gate remains false. The older
string-handle proposition `PNP.PEqualsNP` remains publication-ineligible.

The compiled-inventory generator supplies the exact declaration, theorem, module, private-
auxiliary, and reviewed-candidate counts after each source-closure regeneration; this prose does
not duplicate those moving totals. The current Lean source closure contains four project-specific
axioms. Seven blockers remain, beginning with `Formal.ConcreteComplexityMachineLink`.

## Audit

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPConcreteTapeHandoffAxiomAudit.lean
lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineTapeGeometryAxiomAudit.lean
lake env lean -DwarningAsError=true lean-audit/PNPConcreteComplexityAxiomAudit.lean
lake env lean -DwarningAsError=true lean-audit/PNPConcretePipelineRefinementAxiomAudit.lean
lake env lean -DwarningAsError=true lean-audit/PNPConcreteTargetAxiomAudit.lean
node --test audits/lean-concrete-complexity0.test.mjs
node --test audits/lean-concrete-tape-handoff0.test.mjs
node --test audits/lean-concrete-pipeline-tape-geometry0.test.mjs
node --test audits/lean-concrete-pipeline-refinement0.test.mjs
```

The source audit rejects hidden executable function fields, string code handles, assumptions,
shortcuts, noncanonical pair order, missing certificate bounds, timeout-as-rejection behavior,
reversed reduction composition, omitted handoff costs, omitted polynomial substitution, weakened
refinement contracts, compiler overclaims, supplied transport fields, target forgery, transcript
truncation, and compatibility-root injection.

## Exact nonclaim

This milestone does not provide a compiler/refinement theorem from the charged pipeline interpreter
to the raw `Machine` kernel. It also does not formalize concrete SAT or SAT NP-hardness, instantiate
the global locked-NAND threshold package, prove the residual-band or ZeroSlack obligations, prove
the remaining end-to-end polynomial bounds, or establish `P = NP`.

# Source-generated shared refutations

This construction turns a false verdict of the existing partial source reducer
into a compact refutation of the original ordered source rows. It does not make
the reducer complete and does not settle P versus NP.

## Source-only interface

[SharedRefutationExtraction](../lean/PNP/Concrete/ResidualReduction/SharedRefutationExtraction.lean)
defines `extract F` using only the original source family `F`. It runs the
existing reducer once, constructs its own certificate from an actual false
zero-dimensional terminal, and unwinds the history that the reducer generated.
The caller does not supply an old refutation, a correctness certificate, or a
history-completeness premise.

The theorem `extract_of_false_verdict` establishes that whenever
`SourceChain.verdict F = some false`, extraction returns a certificate that is
well formed and refutes the original rows. If the original family has `m` rows
and `n` variables, its shared coefficient circuit contains at most
`2 + (4 * m + 1) * n` gates. The bound holds for arbitrary source dimensions
and row families satisfying the stated false-verdict premise.

`extract_contract` gives well-formedness, the refutation identity, and that gate
bound for every returned certificate. `extract_unsatisfiable` establishes that
a returned certificate implies that the original family has no model.

## Why sharing matters

The construction lifts coefficient circuits through each recorded contraction
without expanding them into a list of polynomial monomials. Terminal roots
select one violated scalar row, including when several rows are violated.
Each replay step preserves the original-row refutation identity while adding
only the bounded shared circuit structure counted by the theorem.

The lower-level replay lemmas expose their semantic hypotheses explicitly.
Those hypotheses are discharged by the source-generated history in `extract`;
the lower-level `unwind` function is not a semantic validator for arbitrary
caller-supplied histories.

## Remaining boundaries

- A positive-dimensional stopped core remains unknown and is not a refutation.
- The construction does not prove that every unsatisfiable input reaches a false
  terminal, or that every satisfiable input yields a model.
- A gate-count bound is not an encoded bit-size or whole-extractor runtime
  theorem. Full representation and execution costs still require proofs.
- Well-formed circuit references are not an efficient independent test of an
  arbitrary circuit identity. No general-purpose polynomial-time refutation
  checker is claimed.
- No fixed progress checkpoint, global gate, or additional publication row is
  earned by this integration. The eligible root theorem remains absent.

## Verification

The explicit `PNP` root imports the regression and strict compiled namespace
audit. The regression examples include malformed references, nonlinear
substitution, terminal-row selection, a source-generated contradiction, and
unknown or satisfiable cases that must not be reported as refutations.
General correctness comes from the kernel-checked theorems, not those examples.

The focused source-contract tests are
`node --test audits/lean-shared-refutation0.test.mjs`. They pin the reviewed
interfaces and reject mutations that hide premises or widen claims.
After the normal authoritative root/inventory build, run
`lake env lean -DwarningAsError=true lean-audit/PNPSharedRefutationAxiomAudit.lean`.
This checks the complete compiled shared-refutation namespace in the root
context, allowing only `propext` and `Quot.sound`.

See the [existing polynomial source phase and its remaining solver boundary](./lean_source_contraction_runtime.md)
and the [canonical progress ledger](../status/PROOF_PROGRESS.json).

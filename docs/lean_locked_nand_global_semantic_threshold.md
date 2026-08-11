# Lean locked-NAND global semantic threshold

`lean/PNP/LockedNANDGlobalSemanticThreshold.lean` closes the remaining
semantic branch of the legacy Section 17 locked-NAND construction. It works
for every finite topologically ordered NAND circuit and reuses the same
answer-independent baseline and full candidates constructed by the preceding
modules.

## Plain-language result

The construction turns a NAND circuit into a larger circuit with a known
reference size `B`. The larger circuit always has `B + 4` gates. Lean now
proves the exact semantic split:

- if the source circuit has no satisfying input, the best equivalent
  implementation has size exactly `B`;
- if the source circuit has a satisfying input, every equivalent
  implementation needs at least `B + 1` gates, while the displayed
  implementation supplies the upper bound `B + 4`; and
- therefore the source is satisfiable exactly when the exhaustive reference
  minimum crosses the threshold from `B` to at least `B + 1`.

The same candidate is used in both cases. It is not chosen after learning
whether the source is satisfiable.

## Technical result

For a source `circuit`, let

```text
B = lockedBaselineCount circuit.program
I = Implementation.mk (B + 4) (fullCandidate circuit)
```

The new public theorems prove:

```text
circuit.Satisfiable →
  OutputNonconstant (fullCandidate circuit) (conditionalFinalOutput B)

circuit.Satisfiable →
  OutputNotPositiveProjection
    (fullCandidate circuit) (conditionalFinalOutput B)

circuit.Satisfiable →
  every embedded baseline output differs from the final output

circuit.Satisfiable →
  B + 1 ≤ referenceMinimum I ∧ referenceMinimum I ≤ B + 4

residualSlack I ≤ 4

circuit.Satisfiable ↔ B + 1 ≤ referenceMinimum I
```

Together with the preceding unsatisfiable theorem,
`¬ circuit.Satisfiable → referenceMinimum I = B`, this is the exact typed
semantic threshold.

## How final-lock separation is proved

The final output has the already-proved semantics

```text
z ∧ tracePredicate circuit.program valuation ∧
  valuation.trace circuit.outputGate
```

A satisfying source input has a coherent carrier trace for which the last two
conjuncts are true. Holding that carrier fixed and changing only the fresh
final-lock bit `z` changes the final output from false to true. Lean proves
that the trace predicate is invariant under this change.

That pair of valuations establishes nonconstancy. It also separates the final
output from every positive carrier projection other than `z`. The `z`
projection itself is separated by a valuation with `z = true` and the output
trace bit false. Finally, every baseline coordinate is already known to be
independent of `z`; comparing its common value on the on/off pair with the
two different final values separates it from the final coordinate.

These three results instantiate
`ConditionalFinalOutputSatConditions`. The definition
`fullCandidateThresholdPremises` then supplies all six fields of
`ConditionalThresholdBoundaryPremises`:

1. `baselineCandidate`;
2. `fullCandidate`;
3. `baselineConditions`;
4. `initialOutputsPreserved`;
5. `unsatisfiableFinalZero`; and
6. `satisfiableFinalConditions`.

The missing-instantiation inventory is therefore empty.

## Constructive case elimination

The final iff theorem needs a `Decidable circuit.Satisfiable` instance.
The module constructs it privately by enumerating `allBoolTuples inputs` and
checking the source program. This is exhaustive finite search. It is used only
to eliminate a proposition-level case split in the semantic theorem.

There is no `Classical.choice`, caller certificate, host-side lookup,
`native_decide`, SAT solver shortcut, or polynomial-runtime claim. The public
candidate definitions remain answer-independent.

## Public and audit surface

The module exposes exactly eight declarations:

1. `fullCandidate_final_nonconstant_of_satisfiable`;
2. `fullCandidate_final_notPositiveProjection_of_satisfiable`;
3. `fullCandidate_final_distinctFromBaseline_of_satisfiable`;
4. `fullCandidate_satisfiableFinalConditions`;
5. `fullCandidateThresholdPremises`;
6. `fullCandidate_referenceMinimum_bounds_of_satisfiable`;
7. `fullCandidate_residualSlack_le_four`; and
8. `fullCandidate_satisfiable_iff_referenceMinimum_ge_succ`.

`lean-audit/PNPLockedNANDGlobalSemanticThresholdAxiomAudit.lean` prints the
compiled axiom closure of all eight. Every declaration depends on exactly the
Lean-standard pair `Quot.sound` and `propext`; none depends on
`Classical.choice`, `sorryAx`, or any of the four project axioms.

`lean-regression/PNPLockedNANDGlobalSemanticThreshold.lean` exercises:

- a satisfiable zero-input constant-true circuit;
- a satisfiable one-input negation circuit;
- an unsatisfiable zero-input constant-false circuit;
- the final-lock and an ordinary primary-coordinate projection;
- separation from every baseline output;
- all six packaged premises;
- the satisfiable minimum bounds;
- the global residual bound;
- both directions of the semantic threshold; and
- the preceding exact unsatisfiable minimum.

`audits/lean-locked-nand-global-semantic-threshold0.test.mjs` rejects missing
or extra declarations, an incomplete axiom transcript, weakened theorem
shapes, an omitted package field, answer-dependent candidates, host lookup,
caller certificates, forbidden shortcuts, and overclaims.

## Mechanically generated evidence

Inventory coordinate
`PNP-LEAN-THEOREM-INVENTORY-2026-08-11-128` records 27,442 declarations,
14,309 theorems, 7,290 assumption-free theorems, 14,999 excluded private
declarations, 246 source-closure modules, and 2,548 reviewed milestone
candidates. Its 17,726,895-byte canonical inventory has SHA-256
`612342db90e5887e2da6417963946437c82a14003f48deeddeae03d50caf637f`;
the Lean source-closure SHA-256 is
`4fde46c2f495422c43f5d2eb3ed80500c097a94b511aaecc74f5e8da979cd910`.

Publication map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-08-11-129` contains 107 milestones: 105
earned and two deliberately unearned. The new
`locked-nand-global-semantic-threshold` milestone pins the seven new theorem
types plus the reused exact unsatisfiable-minimum theorem. The generated map
is 826,175 bytes with SHA-256
`9093dd1bdc84405be1748831ad59b98a60aabbd80d389f26f38f889de44770ea`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-11-129` sets the semantic-threshold,
six-field-package, derived-final-output, and residual-at-most-four evidence
fields true. It retains all four project assumptions, all five blockers,
unset activation fingerprints, an absent `PNP.Main.p_eq_np`, and a false
concrete publication gate. The status is 2,076,560 bytes with SHA-256
`79c3ef6dace2f95cdad66add48c105e4ed5f95609b9c2819533685f63ed941aa`.

The generated canonical report source is 217,706 bytes with SHA-256
`e43ad410bc6e10f4e5d22d24c559b236e5698eb54b8b6b2659e2d0b3a8e4989c`.
Its deterministic A4 PDF is 85 pages and 455,104 bytes with SHA-256
`f48bc615866790d08151198272e89c9e68f8e1fd404ae46700ced768f42aa70c`.

## Exact boundary

This milestone follows the legacy manuscript’s semantic construction and
closes its typed threshold argument. Its successors fix the normalized
version-zero bitstring semantics, provide a literal polynomial-time
parser/validator and target emitter, and package their exact composition as a
concrete `PolynomialReduction`. These milestones still do not connect the
concrete target to the abstract `PNP.LockedNANDThreshold` language, prove
CNFSAT in P, transport NP-hardness or NP-completeness, discharge the project
axiom `PNP.LockedNANDThreshold`, or prove `P = NP`. If Lean exposes a
contradiction in the legacy route, the formalization must stop and repair or
replace that step rather than add an assumption.

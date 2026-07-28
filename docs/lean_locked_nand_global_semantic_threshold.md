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
`PNP-LEAN-THEOREM-INVENTORY-2026-07-29-90` records 13,731 declarations,
7,827 theorems, 4,012 assumption-free theorems, 6,908 excluded private
declarations, 117 source-closure modules, and 2,008 reviewed milestone
candidates. Its 11,544,049-byte canonical inventory has SHA-256
`bc9f93749d14dd5d646ee37540f365d9c712f599a4aadd45262bb1ab063146c5`;
the Lean source-closure SHA-256 is
`22510170cf53b25ddd89df7cf9d01fefc0aff38ba52ae030c55c46c1b16cf50e`.

Publication map coordinate
`PNP-FORMAL-PUBLICATION-MAP-2026-07-29-90` contains 70 milestones: 67
earned and three deliberately unearned. The new
`locked-nand-global-semantic-threshold` milestone pins the seven new theorem
types plus the reused exact unsatisfiable-minimum theorem. The generated map
is 657,356 bytes with SHA-256
`abc16d916b77f37dffceed60440fcf966056e1da1785834867a8c49ddc58f383`.

Status coordinate
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-29-90` sets the semantic-threshold,
six-field-package, derived-final-output, and residual-at-most-four evidence
fields true. It retains all four project assumptions, all six blockers,
unset activation fingerprints, an absent `PNP.Main.p_eq_np`, and a false
concrete publication gate. The status is 1,611,774 bytes with SHA-256
`c5f375d6a2fe9cae42901997357ab626ae69481f6a81f7217a889937c8d26ed5`.

The generated canonical report source is 156,947 bytes with SHA-256
`4fef9bd1525e1f700b8eb98f5a9c54396b39013e1619fe803df8c1a047588fad`.
Its deterministic A4 PDF is 64 pages and 408,994 bytes with SHA-256
`40e93415f0ce334d53ac8ee0c691df828b8ea5ddaeb45d3c22d2faec6d88d9eb`.

## Exact boundary

This milestone follows the legacy manuscript’s semantic construction and
closes its typed threshold argument. Its first successor fixes and verifies
the exact normalized version-zero bitstring semantics; the next now supplies a
literal polynomial-time parser/validator for that fixed grammar. These
milestones still do not supply the target emitter, its construction and
output-size bounds, the composed `PolynomialReduction`, connection to the
abstract `PNP.LockedNANDThreshold` language, a CNFSAT-in-P theorem,
NP-hardness or NP-completeness transport, discharge of the project axiom
`PNP.LockedNANDThreshold`, or `P = NP`.

The next non-repetitive step is therefore the complete target emitter followed
by parser/emitter composition, not another manually repeated semantic
coordinate. If Lean exposes a contradiction in the legacy route, the
formalization must stop and repair or replace that step rather than add an
assumption.

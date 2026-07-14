# Lean conditional locked-NAND threshold boundary

`lean/PNP/LockedNANDThresholdBoundary.lean` proves the semantic deductions that follow from an
explicit proof-bearing candidate package. It is not the report threshold theorem and does not
construct that package for a source circuit.

## The six required premises

For an arbitrary proposition `satisfiable`, input width, and natural number `baseline`, Lean
requires one `ConditionalThresholdBoundaryPremises` value with exactly these fields:

| Field | Required evidence |
| --- | --- |
| `baselineCandidate` | A typed candidate with exactly `baseline` gates and `baseline` outputs. |
| `fullCandidate` | A typed candidate with exactly `baseline + 4` gates and `baseline + 1` outputs. |
| `baselineConditions` | Semantic nonconstant, nonprojection, and pairwise-distinct conditions for every baseline output. |
| `initialOutputsPreserved` | The first `baseline` full outputs compute the corresponding baseline functions on every valuation. |
| `unsatisfiableFinalZero` | If `satisfiable` is false, the full final coordinate is false on every valuation. |
| `satisfiableFinalConditions` | If `satisfiable` is true, the final output is nonconstant, nonprojection, and distinct from every baseline output. |

These are propositions about actual typed candidates and their Boolean semantics. They are not
metadata flags, certificate identifiers, or string claims. They are also not instantiated in this
module. The machine-readable `leanLockedNANDThresholdMissingInstantiationInventory` repeats these
six field names exactly so none can disappear behind a broad completion flag.

## What Lean derives from the package

The module projects the first `baseline` outputs from the full word and transports the supplied
baseline conditions through their pointwise semantic equivalence. It also constructs a free
constant-zero final output by output wiring alone, without adding a NAND gate.

From the six premises Lean proves:

```text
baseline ≤ referenceMinimum(full)
residualSlack(full) ≤ 4

¬satisfiable → referenceMinimum(full) = baseline

satisfiable →
  baseline + 1 ≤ referenceMinimum(full) ≤ baseline + 4

[Decidable satisfiable] →
  satisfiable ↔ baseline + 1 ≤ referenceMinimum(full)
```

The residual bound is therefore conditional on the premise package. It is not an unconditional
`≤ 4` theorem for every report locked-NAND word.

## Exact hostile-review mapping

The historical adversarial review named exactly five threshold lemmas:

| Hostile-review lemma | Current formal status |
| --- | --- |
| `DirectWireOutputLowerBound` | Discharged generally by the direct-wire output-to-gate injection and used here through reference-minimum lower bounds. |
| `MacroDistinct` | Only the five local square macro instances are discharged. The global carrier-tagged, cross-instance form remains missing and must instantiate `baselineConditions`. |
| `TraceEquivalence` | The circuit-specific theorem remains missing. It must justify `initialOutputsPreserved` and the source-specific final-output laws. |
| `ZeroOutputConvention` | The model-level convention is discharged: appending a constant-zero output preserves the program and gate count. The global `unsatisfiableFinalZero` law still has to be derived from trace equivalence. |
| `FinalLockSeparation` | The required semantic consequences are stored in `satisfiableFinalConditions`; deriving them from a fresh final lock and the real construction remains missing. |

Thus the new module closes the deduction from the explicit semantic package. It does not hide the
global cross-instance `BaselineDistinct`, `TraceEquivalence`, or final-lock argument inside the
theorem statement.

## Missing global instantiation

A report-level use still has to supply all six fields above for the concrete circuit construction.
In particular it must:

1. construct the baseline and full candidates with the exact widths, using a concrete carrier
   layout and globally fresh tags;
2. prove global cross-instance `BaselineDistinct`/`MacroDistinct` for the complete baseline tuple;
3. prove preservation of the first `B` functions;
4. prove the whole-carrier unsatisfiable final-zero law from `TraceEquivalence`;
5. prove the satisfiable final output is nonconstant, nonprojection, and distinct from each
   baseline coordinate using `FinalLockSeparation`; and
6. construct this package uniformly, answer-independently, and in polynomial time.

The last condition matters: the premise structure by itself does not prevent choosing candidates
after inspecting whether `satisfiable` is true. Such an answer-dependent witness would not be a SAT
reduction.

The parameters are merely an arbitrary proposition and an arbitrary natural number. This module
does not identify them with source-circuit satisfiability and `lockedBaselineCount program`, prove
their size alignment, or connect the boundary to the abstract `PNP.LockedNANDThreshold` language
and reduction trust surface.

## Audit boundary

The dedicated transcript covers all 32 explicit declarations and reports no axioms. Nevertheless,
the global carrier layout, global baseline distinctness, trace equivalence, derived final-output
laws, uniform builder, threshold theorem, unconditional residual-slack-at-most-four theorem, and
polynomiality all remain false in the formal status. The charged-pipeline-to-raw-machine link is
now discharged; six blockers remain, including the still-missing global threshold work. The four
project-specific axioms and absent
`PNP.Main.p_eq_np` root theorem also remain. The axiom-free inactive
`PNP.Main.ConcretePEqualsNP` definition does not change this threshold boundary or activate the
publication gate.

The ordered multi-output convention and quarantined legacy `m = 2` accounting remain as documented
in [Lean locked-NAND direct candidates and local baselines](./lean_locked_nand_baseline.md).

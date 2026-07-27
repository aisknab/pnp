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
metadata flags, certificate identifiers, or string claims. They are not instantiated in this
conditional module. The later global-candidate layer constructs
`baselineCandidate`, `fullCandidate`, and `initialOutputsPreserved`; the
following global baseline-distinctness layer constructs `baselineConditions`,
and the unsatisfiable-final-zero layer constructs `unsatisfiableFinalZero` on
the whole carrier. The machine-readable
`leanLockedNANDThresholdMissingInstantiationInventory` now repeats exactly
the one field still missing: `satisfiableFinalConditions`.

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
| `MacroDistinct` | Discharged globally for the complete carrier-tagged baseline by `baselineCandidate_outputConditions`; the square baseline consequently has exact reference minimum `B`. |
| `TraceEquivalence` | Discharged for arbitrary finite typed NAND circuits by `LockedNANDCarrierTrace`; `LockedNANDGlobalCandidates` connects it to the complete exposed baseline/full candidates and exact final-conjunction semantics. The unsatisfiable branch is now derived; the satisfiable final-output conditions remain open. |
| `ZeroOutputConvention` | Discharged on the whole carrier: appending a constant-zero output preserves the program and gate count, and unsatisfiability now proves the constructed full final output is identically false. |
| `FinalLockSeparation` | The required semantic consequences are stored in `satisfiableFinalConditions`; deriving them from a fresh final lock and the real construction remains missing. |

Thus the conditional module closes the deduction from the explicit semantic
package. The candidate and baseline-distinctness milestones supply the
construction, preservation, and baseline-condition fields without hiding the
derived final-output branch laws or final-lock separation argument inside the
theorem statement.

## Missing global instantiation

A report-level use still has to supply the remaining two fields for the concrete circuit
construction. In particular it must:

1. prove the whole-carrier unsatisfiable final-zero law from `TraceEquivalence`;
2. prove the satisfiable final output is nonconstant, nonprojection, and distinct from each
   baseline coordinate using `FinalLockSeparation`; and
3. package those facts uniformly, answer-independently, and in polynomial time.

The last condition matters: the premise structure by itself does not prevent choosing candidates
after inspecting whether `satisfiable` is true. Such an answer-dependent witness would not be a SAT
reduction.

The conditional parameters are merely an arbitrary proposition and an arbitrary natural number.
The candidate layer proves the exact `lockedBaselineCount program` size alignment, but no completed
premise value yet identifies the proposition with source-circuit satisfiability or connects the
boundary to the abstract `PNP.LockedNANDThreshold` language and reduction trust surface.

## Audit boundary

The dedicated conditional-boundary transcript covers all 32 explicit
declarations and reports no axioms. The separate carrier/trace transcript
covers all 71 public declarations, and the complete global-candidate
transcript covers all 64 public declarations, using only the approved
Lean-standard closure and no `Classical.choice`. The five-theorem
baseline-distinctness transcript and two-theorem unsatisfiable-final-zero
transcript use exactly `propext` and `Quot.sound`. Carrier layout, semantic
trace equivalence, exact candidate assembly, global baseline distinctness,
and the whole-carrier unsatisfiable branch are now true in formal status. The
satisfiable final-output conditions, uniform polynomial builder, threshold
theorem, unconditional residual-slack-at-most-four theorem, and polynomiality
remain false. Six blockers remain, including the still-missing global
threshold work. The four project-specific axioms and absent
`PNP.Main.p_eq_np` root theorem also remain. The axiom-free inactive
`PNP.Main.ConcretePEqualsNP` definition does not change this threshold boundary or activate the
publication gate.

The ordered multi-output convention and quarantined legacy `m = 2` accounting remain as documented
in [Lean locked-NAND direct candidates and local baselines](./lean_locked_nand_baseline.md). The
new semantic carrier theorem is documented in
[Lean locked-NAND carrier layout and trace equivalence](./lean_locked_nand_carrier_trace.md), and
the constructed candidates are documented in
[Lean locked-NAND global candidate assembly](./lean_locked_nand_global_candidates.md),
and the discharged baseline conditions are documented in
[Lean locked-NAND global baseline distinctness](./lean_locked_nand_global_baseline_distinct.md).
The derived unsatisfiable branch is documented in
[Lean locked-NAND global unsatisfiable final-zero branch](./lean_locked_nand_global_unsatisfiable_final_zero.md).

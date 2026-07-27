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
the whole carrier. `LockedNANDGlobalSemanticThreshold` derives
`satisfiableFinalConditions` from the fresh final lock and packages all six
fields for the same answer-independent candidate. The machine-readable
`leanLockedNANDThresholdMissingInstantiationInventory` is now empty.
The satisfiable final-output conditions are therefore formally discharged.

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

The deduction in this module is conditional on the premise package.
`LockedNANDGlobalSemanticThreshold` now supplies that package and derives an
unconditional `≤ 4` theorem for the real typed full candidate over every
finite topological NAND circuit. That is still not an encoded construction
or runtime theorem for every report locked-NAND word.

## Exact hostile-review mapping

The historical adversarial review named exactly five threshold lemmas:

| Hostile-review lemma | Current formal status |
| --- | --- |
| `DirectWireOutputLowerBound` | Discharged generally by the direct-wire output-to-gate injection and used here through reference-minimum lower bounds. |
| `MacroDistinct` | Discharged globally for the complete carrier-tagged baseline by `baselineCandidate_outputConditions`; the square baseline consequently has exact reference minimum `B`. |
| `TraceEquivalence` | Discharged for arbitrary finite typed NAND circuits by `LockedNANDCarrierTrace`; `LockedNANDGlobalCandidates` connects it to the complete exposed baseline/full candidates and exact final-conjunction semantics. Both semantic branches are now derived. |
| `ZeroOutputConvention` | Discharged on the whole carrier: appending a constant-zero output preserves the program and gate count, and unsatisfiability now proves the constructed full final output is identically false. |
| `FinalLockSeparation` | Discharged by toggling only the fresh final lock around one satisfying coherent trace, while every baseline coordinate remains unchanged. This proves final nonconstancy, nonprojection, and separation from every baseline output. |

Thus the conditional module closes the deduction from the explicit semantic
package, while the later global modules construct and prove every field
without hiding an answer-dependent candidate or final-lock assumption inside
the theorem statement.

## Completed typed instantiation and remaining report link

The typed circuit use now:

1. proves the whole-carrier unsatisfiable final-zero law from `TraceEquivalence`;
2. proves the satisfiable final output is nonconstant, nonprojection, and distinct from each
   baseline coordinate using the fresh final lock; and
3. packages those facts uniformly and answer-independently for every finite topological NAND
   circuit.

The candidate definitions contain no branch on satisfiability. A private
exhaustive finite decision is used only to eliminate a proposition-level case
split in the final iff theorem; it is not a construction step and carries no
polynomial-runtime claim.

The remaining report-level work is different: construct the encoded
locked-NAND instance with a proved polynomial-time machine and certificate-size
bound, then connect the typed semantic object to the abstract
`PNP.LockedNANDThreshold` language and reduction trust surface.

## Audit boundary

The dedicated conditional-boundary transcript covers all 32 explicit
declarations and reports no axioms. The separate carrier/trace transcript
covers all 71 public declarations, and the complete global-candidate
transcript covers all 64 public declarations, using only the approved
Lean-standard closure and no `Classical.choice`. The five-theorem
baseline-distinctness transcript and two-theorem unsatisfiable-final-zero
transcript use exactly `propext` and `Quot.sound`. The new eight-declaration
semantic-threshold transcript uses the same exact closure. Carrier layout, semantic
trace equivalence, exact candidate assembly, global baseline distinctness,
both whole-carrier branches, the complete six-field package, the typed
semantic threshold, and global residual slack at most four are now true in
formal status. The encoded polynomial builder, report-level threshold link,
and polynomiality remain false. Six blockers remain, including that
construction/link work. The four project-specific axioms and absent
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
The completed satisfiable branch and typed threshold are documented in
[Lean locked-NAND global semantic threshold](./lean_locked_nand_global_semantic_threshold.md).

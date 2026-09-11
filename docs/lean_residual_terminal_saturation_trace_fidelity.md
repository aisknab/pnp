# Saturation trace fidelity and metadata cost balance

M234 closes the replay-endpoint and generated metadata-accounting edges in the
manuscript's saturation argument. It does not claim that every saturation event
is transparent or that every local obligation is discharged.

## Exact theorem boundary

The [executable saturation module](../lean/PNP/ResidualTerminalExecutableSaturation.lean)
preserves its existing work-list algorithm and actual replay field:

- `terminalSaturateTrace_replayRecords_iff` proves that the cost-accounting
  replay contains exactly the records of canonical computed saturation.
- `terminalSaturateTrace_event_valid` proves that each event in the generated
  trace adds its required record and carries a rule that actually relates the
  dependent to that record.

The [trace-fidelity module](../lean/PNP/ResidualTerminalSaturationTraceFidelity.lean)
then uses M233's structural support equality:

- `terminalCandidateSaturateTrace_ambient_eq` identifies the actual replay and
  canonical endpoint ambient implementations.
- `terminalCandidateSaturateTrace_costSnapshot_eq` identifies all computed
  cost coordinates, keeping the stored record list explicit with a record update.
- `terminalCandidateSaturateTrace_metadata_transparent` derives cost
  transparency for every generated non-gate metadata event.

The first two statements quantify over arbitrary finite terminal systems and
seeds. The candidate statements quantify over arbitrary finite dimensions,
executable models, seeds and generated events. Generated-event membership and
the non-gate restriction are domain conditions, not supplied correctness proofs.

The proof erases execution annotations into the original work state, preserves
record-accounting and rule-validity invariants, and transfers selected-gate
equality through the actual extractor. It does not replace the replay with the
separately computed canonical field or unfold exhaustive minima as a shortcut.

## Regressions and assumption audit

The [permanent regression](../lean-regression/PNPResidualTerminalSaturationTraceFidelity.lean)
applies all five interfaces at arbitrary dimensions. Executed fixtures cover
empty and duplicate seeds, cyclic dependencies, competing rule candidates,
and every non-gate record constructor: boundary, interface and profile.
A nonconstant observer reads an actual candidate output.

Missing-rule, incorrect-rule and unrelated-after-state events are not members
of the generated trace. The existing raw-event classifier continues to reject
missing rules and unbalanced snapshots.

A generated constant-output NAND gate increases physical support size but not
the full reference minimum. It is therefore nontransparent. This checked
counterexample prevents metadata balance from being read as a theorem about all
physical materializers. A generated obligation metadata event is cost-balanced
but still has an open obligation; it does not satisfy closure safety.

The [explicit root audit](../lean-audit/PNPResidualTerminalSaturationTraceFidelityAxiomAudit.lean)
checks all five interfaces. Their dependency closures contain only `propext`
and `Quot.sound`, with no project-specific axiom or classical choice.
The [hostile contracts](../audits/lean-residual-terminal-saturation-trace-fidelity0.test.mjs)
reject fixed-instance substitutes, weakened types, supplied premises, a copied
canonical replay field, fingerprint changes and widened publication claims.

## Remaining proof burden

The executable observer and profile model remain supplied data.
Influence and semantic minima use exhaustive finite reference constructions;
no polynomial runtime is proved. Metadata cost balance does not establish
physical-gate transparency, obligation discharge or complete closure safety.

Physical materializers still need forced full-minimum growth, quotient bounds,
ownership and correct routing. This milestone does not derive terminal families
from every valid input, prove global route coverage, unconditional SaturatePositive,
BCELReady or ZeroSlack, or construct the exact polynomial PCCMin algorithm and
certificate bounds. Deterministic CNFSAT in P and the eligible root theorem remain
absent; the publication gate remains false.

The [milestone plan](plans/2026-09-11-saturation-trace-fidelity.md) records the
legacy anchor and remaining dependencies. No fixed weighted checkpoint or
global gate closes.

Formal artefact coverage: 210 of 212 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

These separate measurements come from the
[canonical progress ledger](../status/PROOF_PROGRESS.json). Neither is confidence
that `P = NP` is true, a probability of success or a time estimate.

Publication decision: defer. Preserve the coherent M231 PNPLabs source pin
until a major publication is warranted. Verified core milestone and
submilestone notifications continue independently.

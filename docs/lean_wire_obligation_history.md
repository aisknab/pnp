# Computed dependency-ordered physical obligation histories

As of PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-15-263.

Formal artefact coverage: 239 of 241 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

M263 closes the computational history dependency recorded in the
[M263 plan](plans/2026-09-15-dependency-ordered-wire-obligation-history.md).
The manuscript anchors are sections 4, 5, 6.1 and 6.2 of the
[pinned legacy report](../archive/legacy-v0/ARCHIVE.json).
This is not the complete Package E calculus.

## Order is derived from raw data

[FiniteDependencyScheduler.lean](../lean/PNP/FiniteDependencyScheduler.lean)
handles arbitrary finite graphs with arbitrary finite predecessor lists.
The general success theorem characterizes exactly well-founded dependency
relations. The returned order is complete, duplicate-free and strictly places
each predecessor before its consumer. A stuck nonempty remainder rejects.

[NANDWireObligationHistory.lean](../lean/PNP/NANDWireObligationHistory.lean)
decodes natural-number event identities, explicit predecessors and the intrinsic
creation references of R6/R8. It rejects duplicate identities, missing references
and cycles before execution. No order, rank or correctness certificate is supplied.

Acyclicity guarantees a computed order, not semantic admissibility of every
instruction set. The chosen deterministic order must also pass the actual
lifecycle checks. Confluence of underspecified event graphs is not claimed.

## Physical state, source binding and full discharge

[NANDWireObligationHistoryState.lean](../lean/PNP/NANDWireObligationHistoryState.lean)
maintains one evolving computational carrier. R5 records the actual pre-drop carrier
and source at a fresh creation identity. Its quotient padding does not remove a
physical gate. Normalization computes actual gate savings and retains every open
creation snapshot unchanged.

The source-identity R6 case scans for a genuinely visible original source and
rebinds its current physical wire; it does not compare gate numbers across
different programs or use forgotten padding. R8 computes the missing-wire
materializer from the exact captured carrier, appends it and charges the whole
physical program. Separate restorations obtain no free cross-snapshot sharing.
A full-mode read is permitted only when its field is available.

[NANDWireObligationHistoryExecution.lean](../lean/PNP/NANDWireObligationHistoryExecution.lean)
constructs one indexed transition per event. Creation, discharge and read records
retain actual physical source bindings. Every creation must discharge strictly later
in the same trace, and the final ledger must be empty. A stale creation identity
cannot close a different entry occupying the same field.

For every successful history and every input valuation, every ordinary output
and computational field has its original full value. The constructor derives all
witnesses internally; its input is a source carrier and raw instructions, not
caller-supplied semantic proofs or a successful replay.

## Every restoration is paid

The general trace theorem states:

```text
final physical gates + actual removed gates
  = initial physical gates + actual appended materializer charges
```

Gate removal is charged only by actual physical normalization. R5 masking alone
earns no physical saving, and R8 can increase size. The exact gate equation and
finite termination do not establish polynomial execution time.

The [permanent axiom audit](../lean-audit/PNPWireObligationHistoryAxiomAudit.lean)
imports the explicit root and checks all 46 reviewed theorem closures. The
[permanent regression](../lean-regression/PNPWireObligationHistory.lean)
checks general theorem types and bounded cases: fan-in, cycles after partial
progress, missing references, duplicate IDs, normalization before restoration,
fresh identities on repeated fields, R6 after physical wire renumbering, ordinary
outputs, empty dimensions and invalid or unfinished lifecycles. These executable
fixtures are regression evidence, never proof authority.
The [source and publication contracts](../audits/lean-wire-obligation-history-publication0.test.mjs)
freeze the reviewed interfaces, compiled types and conservative claims.

## Remaining obligations and publication decision

Full R7 and other R1-R9 semantics, all N1-N10 transports, arbitrary observers and
profiles, noncomputational carrier records, matched-cost support Pull/Expand and
the complete Package E verifier remain open. So do input-derived terminal
families, global routes, unconditional SaturatePositive/BCELReady/ZeroSlack, exact
PCCMin and full encoded-input polynomial runtime, output and certificate bounds.
Deterministic SAT and the eligible root theorem remain absent; P = NP is not proved.

No fixed weighted checkpoint or global proof gate closes. Formal artefact
coverage changes independently of the risk-weighted proof estimate in the
[canonical progress ledger](../status/PROOF_PROGRESS.json).

Publication decision: defer PNPLabs. This release completes one computational
history dependency, not a complete manuscript package or a weighted checkpoint.
Keep the coherent M262 website source pin unchanged and batch this result into a
later major publication. Verified submilestone notifications remain independent
of website cadence.

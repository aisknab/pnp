# M180 proof-bearing Packet/budget no-lower ZeroSlack sidecar

## Evidence-led selection

The pinned manuscript's Section 16 requires the ZeroSlack branch to retain a
checked no-lower ledger before positive residual slack is routed through the
BCEL contradiction. The current reconstruction already has one executable
checker that composes the complete finite terminal budget-support ledger with
the checked Packet ledger over the same direct-wire candidate, but
`ZeroSlack.lean` still stores `noLowerRouteLedgerComplete` as an uninterpreted
string.

M180 replaces that string with a proof-bearing checked sidecar. The sidecar
carries arbitrary finite direct-wire, budget, saturation, Packet, typed-realizer,
dependency, and residual-rank data together with the actual composed checker
equation. Existing reflection theorems then recover semantic minimum status for
every budget-feasible governed support, exclude a feasible strict-equivalent
gain, and exclude a positive Packet conclusion for the supplied family.

## Legacy anchor and dependency edge

- Legacy anchor: report Section 16, especially the rank-ordered oracle's
  no-lower ledger and the first paragraph of the ZeroSlack proof.
- Closed edge: executable same-candidate Packet/budget no-lower composition ->
  proof-bearing `PacketBudgetNoLowerZeroSlackSidecarCertificate` -> the
  structured `ZeroSlackCertificate`.
- Unbounded abstraction: arbitrary natural input, gate, output, profile-width,
  and rank counts; arbitrary finite typed Packet carriers, tables, dependency
  rows, residual-rank maps, and terminal support budgets.

## Exact theorem target

For every `PacketBudgetNoLowerZeroSlackSidecarCertificate`, prove
`PNP.packet_budget_no_lower_zeroslack_sidecar_checked_complete`: every governed
budget-feasible support implementation is semantically minimum, no governed
budget-feasible support has a strict equivalent gain, and the supplied grouped
family has no positive Packet conclusion.

The certificate must not carry a caller success Boolean, proof-valued
conclusions, a string ledger handle, or an independently supplied statement of
the result. Its accepted proposition must be reflected from the existing
`checkTerminalPacketBudgetNoLowerComposition = true` equation.

## Claim boundary and downstream blockers

The budget caps, candidate-derived saturation model, grouped family, typed
payload fields, finite ranks, realizer claims, activity environment, dependency
rows, and before/after rank maps remain supplied inputs. M180 covers exactly the
existing finite Packet and budget-support branches. It does not cover
normalization, HResolve, saturation-loss, named-route, replay, or other
manuscript no-lower rows; construct terminal data; prove Packet adequacy; provide
the complete no-lower ledger; connect positive slack to BCEL or a faithful
selector; prove unconditional ZeroSlack or PCCMin; establish polynomial size or
runtime; put SAT in P; remove a project axiom; or prove `P = NP`.

## Required evidence

- root import and compiled theorem-inventory inclusion;
- an explicit axiom transcript for every new public declaration;
- a regression retaining all three semantic consequences through the new
  certificate and its `ZeroSlackCertificate` field;
- hostile mutations for retained strings, caller flags, supplied conclusions,
  omitted checker bindings, assumptions, fixed dimensions, and claim widening;
- publication-map and formal-status rows with reviewed kernel fingerprints;
- current reconstruction, audit, pipeline, terminology, README, and canonical
  report documentation; and
- durable CI and aggregate-verifier coverage.

## Verification order and deduplication

Run lightweight source-shape checks before remote proof feedback. On the
configured remote builder, compile the new dependency and root once, run its
axiom transcript and regression, reconcile generated publication evidence,
then run the complete core suite and one fresh exact-merge reproduction. Do not
rerun a targeted command already covered by an unchanged broader suite unless
diagnosing a failure. PNPLabs imports the exact verified core artifacts and
must not invoke Lean, Lake, Elan, or the core proof suite.

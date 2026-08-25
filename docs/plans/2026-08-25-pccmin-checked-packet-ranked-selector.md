# M192 checked Packet rank-ordered selector construction

## Evidence-led selection

M191 reconstructs the manuscript's Section 16.1 control flow, but its
`PCCMinRankedSelectorPlan` still accepts both `selectorsAt` and `realize` as
arbitrary proof-bearing functions.  Earlier milestones already provide an
exhaustive canonical Packet-handle list, a finite rank assignment, data-only
gain-or-typed-bot claims, and an executable checker whose accepted gain rows
yield genuine `StrictEquivalentGain` evidence.  The next load-bearing edge is
therefore to derive the M191 selector rows and realizer outcomes from that
checked table instead of asking a caller to supply them independently.

## Legacy anchor and unbounded abstraction

- Legacy anchor: the pinned canonical manuscript, Section 16.1, lines
  `construct finite rank list P_1,...,P_M`, `for K in K_{P_j}(C)`,
  `out = Real(C,K)`, and `store Real(C,K)=bot` before the final ZeroSlack
  branch.
- Closed edge: one exhaustive checked data-only Packet table -> canonical
  exact-rank selector rows -> proof-bearing gain-or-typed-blocker outcomes ->
  the M191 rank-ordered oracle and checked PCCMin loop.
- Unbounded abstraction: arbitrary finite direct-wire dimensions, every
  current implementation, every supplied finite grouped Packet family, every
  finite rank count, and every data-only claim table.  No fixed circuit,
  selector, rank, or table instance earns the milestone.

## Exact theorem target

Add a fail-closed checker covering every canonical Packet claim, not only rows
whose supplied faithfulness bit is true.  Prove that acceptance reconstructs
exactly one of:

- a checker-validated unit-charge blueprint carrying a genuine strict
  equivalent gain; or
- the exact stored HN, budget, or lower-seed typed blocker.

Derive each rank row by filtering the canonical exhaustive Packet-handle list
with the table-owned `rankOf` function.  Prove that every canonical handle is
in its assigned row and that row membership implies the exact rank equation.
Use these rows and checked outcomes to construct the M191
`PCCMinRankedSelectorPlan`.

Define a Packet-backed rank-ordered oracle plan in which HResolve and
BudgetResolve retain their proof-bearing M191 interfaces, but the selector
plan is constructed from checked data after both negative resolver outcomes.
Compose it with normalization and the existing well-founded loop.  The public
endpoint
`PNP.DirectWire.pccmin_normalize_checked_packet_rank_ordered_oracle_loop_checked_complete`
must return an equivalent exact minimum, the exhaustive reference-minimum
gate count, zero residual slack, and the existing strict-gain iteration bound.

## Claim boundary and downstream blockers

M192 does not construct the grouped Packet family, finite rank assignment,
data-only claim table, HResolve, BudgetResolve, normalizer, blocker semantics,
or the implication from complete checked silence to ZeroSlack.  The complete
table may be exponentially large and no encoded-size or runtime theorem is
claimed.  It therefore does not prove unconditional SaturatePositive,
BCELReady, ZeroSlack, executable polynomial PCCMin, SAT in P, or the eligible
root theorem.

Because family/table construction and the final ZeroSlack closure remain
supplied, M192 does not close a fixed risk-weighted checkpoint or global gate.
The risk-weighted estimate remains 35 percent, the uncertainty range remains
20 to 40 percent, and zero of five global gates remain closed.  One formal
publication evidence row may be added independently.

## Required evidence

- compilation of the new leaf module and explicit root import;
- regressions for a checked gain, each of the three typed blockers, exact rank
  row membership, a later-rank gain, complete silence, and loop composition;
- rejection of an unchecked gain row by the all-claim checker;
- an axiom transcript for the reviewed public declarations, rejecting project
  axioms and `Classical.choice`;
- hostile checks rejecting arbitrary caller-supplied selector rows, a
  proof-bearing claim table, fixed rank prefixes, unchecked gains, hidden
  exhaustive minimization, and polynomial or unconditional-ZeroSlack claims;
- current status, inventory, publication map, progress ledger, report, audit
  questions, and documentation updates with the weighted score unchanged; and
- normal core and PNPLabs exact-merge validation, publication, deployment, and
  production-verification gates.

## Verification and deduplication

Compile the new leaf module, regression, and axiom audit first on the capped
remote builder.  Regenerate the compiled inventory and derived publication
artefacts only after the theorem surface stabilizes.  Run the complete core
suite and exact-head clean reproduction once, then let PNPLabs consume the
exact merged core evidence without rebuilding Lean.

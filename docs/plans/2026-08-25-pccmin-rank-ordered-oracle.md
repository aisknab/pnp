# M191 rank-ordered PCCOracle orchestration

## Evidence-led selection

M189 formalized the well-founded PCCMin loop under one opaque proof-bearing
total oracle. M190 composed the manuscript's `NormalizeOrGain` stage with that
oracle, but still accepted the entire `PCCOracle` as one supplied function.
The pinned manuscript's Section 16.1 instead fixes a load-bearing order:
HResolve, then BudgetResolve after NoHereditary, then every selector in finite
packet-rank order, and ZeroSlack only after the complete selector-silence
ledger has been recorded.

M191 reconstructs that exact control-flow dependency. It keeps the component
algorithms and final mathematical closure explicit, but prevents an oracle
builder from skipping resolver stages, scanning only a fixed rank prefix, or
returning ZeroSlack without a typed blocker equation for every selector in
every supplied finite rank row.

## Legacy anchor and unbounded abstraction

- Legacy anchor: the pinned canonical manuscript, Section 16.1, “Rank-ordered
  PCCOracle,” lines `HResolve_exp`, `BudgetResolve_exp`, the finite rank loop
  over `K_{P_j}(C)`, and the final ZeroSlack return after selector silence.
- Closed edge: separated proof-bearing HResolve/BudgetResolve outcomes plus a
  complete canonical finite-rank selector scan -> the total oracle consumed by
  the M189 loop -> the M190 normalization/oracle composition.
- Unbounded abstraction: arbitrary finite direct-wire dimensions, every
  current implementation, every finite number of ranks, arbitrary finite
  selector rows at each rank, and arbitrary proof-bearing resolver and
  realizer implementations. No fixed rank, selector, circuit, or schedule
  prefix earns the milestone.

## Exact theorem target

Define proof-bearing resolver and realizer outcomes, a finite ranked selector
plan, row and rank-list scanners, the complete canonical `allFin` scan, a
rank-ordered oracle plan, and a total plan builder.

The scanner must establish that:

- HResolve is observed before BudgetResolve;
- BudgetResolve is reached only with the actual NoHereditary payload;
- selector rows are visited through the complete canonical finite rank list;
- any realizer gain is a genuine `StrictEquivalentGain` and returns
  immediately;
- the silent outcome contains a typed blocker equation for every selector in
  every rank row; and
- ZeroSlack can be returned only by applying the explicit mathematical
  closure to that complete silence ledger.

Convert the builder into `PCCMinTotalOracle`, compose it with the M190
normalizer, and prove the public endpoint
`PNP.DirectWire.pccmin_normalize_rank_ordered_oracle_loop_checked_complete`.
The loop result must remain semantically equivalent to its input, globally
minimum, equal in size to the exhaustive reference minimum, zero in residual
slack, and bounded in strict-gain iterations by the starting residual slack.

## Claim boundary and downstream blockers

M191 does not construct NormalizeOrGain, HResolve, BudgetResolve, terminal
candidates, packet families, rank rows, selector tables, realizer claims, HN,
BUD or HB blocker semantics, or the final ZeroSlack implication. In particular,
the `zeroSlackOfSilence` field remains the precise load-bearing mathematical
boundary. The result proves no selector-universe encoded-size bound, no
polynomial runtime, no unconditional ZeroSlack, no executable concrete PCCMin,
no SAT algorithm, and no eligible root theorem.

Because these component constructors and the exactness closure remain supplied,
M191 does not close a fixed risk-weighted checkpoint or a global gate. The
risk-weighted estimate remains 35 percent, the uncertainty range remains 20 to
40 percent, and zero of five global gates remain closed. One formal-publication
evidence row may be added independently.

## Required evidence

- compilation of the new module and explicit root import;
- regressions covering both resolver exact/gain branches, an early-rank
  selector gain, a later-rank selector gain, and complete-silence ZeroSlack;
- an axiom transcript for the reviewed public declarations, rejecting project
  axioms and `Classical.choice`;
- hostile checks rejecting an unresolved constructor, a fixed rank prefix,
  direct ZeroSlack without complete silence, hidden exhaustive minimization,
  component-construction claims, and polynomial-runtime or final-theorem
  overclaims;
- theorem inventory, formal status, publication map, progress ledger, report,
  audit questions, and current documentation updates with the weighted score
  unchanged; and
- normal core and PNPLabs verification, exact-merge reproduction, publication,
  and deployment gates.

## Verification and deduplication

Compile the new leaf module, regression, and axiom audit first on the capped
remote builder. After the source and exact expectation chain stabilize,
regenerate the compiled inventory and derived publication artefacts once, then
run the complete core suite and clean exact-head reproduction. PNPLabs consumes
the exact merged core evidence and does not rebuild Lean.

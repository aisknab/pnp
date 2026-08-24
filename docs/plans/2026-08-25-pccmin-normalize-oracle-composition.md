# M190 proof-bearing PCCMin normalization/oracle composition

## Evidence-led selection

M189 formalized well-founded recursive PCCMin control flow for one
proof-bearing total oracle, but the canonical manuscript's Section 16 loop has
two distinct stages at every iteration: `NormalizeOrGain` runs first, and the
rank-ordered `PCCOracle` runs only after normalization succeeds. The active Lean
surface does not yet prove that a gain returned after normalization is still a
strict gain from the pre-normalized implementation, or that an exact or
ZeroSlack oracle endpoint transports back through normalization.

M190 closes that control-flow edge. A typed normalizer may return either a
genuine strict equivalent gain or a semantically equivalent normalized
implementation whose gate count does not increase. The existing typed oracle
then runs on that normalized implementation. The composition converts every
possible branch into the exact M189 oracle interface, so the existing
well-founded loop can recurse without fuel or an unchecked success case.

## Legacy anchor and unbounded abstraction

- Legacy anchor: the pinned manuscript's `PCCMin_exp` pseudocode and residual-
  band exact-minimization proof in Section 16.2, specifically the
  `NormalizeOrGain_exp(C)` stage followed by `PCCOracle_exp(C)` and the claim
  that every nonterminal gain decreases global residual slack.
- Closed edge: proof-bearing normalizer result followed by a proof-bearing
  oracle result -> one sound M189 total-oracle result relative to the original
  implementation -> the existing well-founded exact loop.
- Unbounded abstraction: arbitrary finite direct-wire input and output
  dimensions, every current implementation, every proof-bearing total
  normalizer, and every proof-bearing total oracle. The theorem is not tied to
  one circuit, one supplied candidate list, or one fixed iteration count.

## Exact theorem target

Define `PNP.DirectWire.PCCMinNormalizedResult`,
`PNP.DirectWire.PCCMinNormalizeOutcome`,
`PNP.DirectWire.PCCMinTotalNormalizer`,
`PNP.DirectWire.composePCCMinNormalizerOracle`, and
`PNP.DirectWire.runPCCMinNormalizeOracleLoop`.

The normalization result must carry complete Boolean semantic equivalence and
a non-increasing gate-count proof. The composition must prove that:

- a normalizer gain is already a `StrictEquivalentGain` from `current`;
- an oracle gain from the normalized implementation lifts to a
  `StrictEquivalentGain` from `current` and therefore strictly decreases
  `residualSlack current`;
- an oracle exact result transports its equivalence back to `current`; and
- an oracle ZeroSlack result becomes an exact-minimum result for `current`
  without claiming that the pre-normalized implementation itself is minimum.

Prove the public endpoint
`PNP.DirectWire.pccmin_normalize_oracle_loop_checked_complete`. Its result must
be semantically equivalent to the original implementation, globally minimum,
equal in gate count to the exhaustive reference minimum, zero in residual
slack, and reached through no more strict-gain iterations than the original
residual slack.

## Claim boundary and downstream blockers

M190 does not construct the normalizer or oracle. It does not derive terminal
families, payloads, maps, ranks, realizer tables, HN/BUD/HB semantics, complete
route coverage, unconditional SaturatePositive, BCELReady, or ZeroSlack. It
does not encode either stage as a finite raw machine, bound the cost of one
stage, prove the starting residual band logarithmic, complete Cook--Levin, put
CNFSAT in P, create the eligible root theorem, open a global gate, or prove
`P = NP`.

Because both load-bearing stages remain explicit arguments, M190 does not close
the fixed `pccmin-executable-loop`, `pccmin-iteration-sound-descent`, or
`pccmin-termination-exactness` checkpoints. The risk-weighted estimate remains
35 percent with a 20-to-40-percent uncertainty range and zero of five global
gates closed. One formal-publication evidence row may be added independently.

## Required evidence

- compilation of the new module and explicit root import;
- regression coverage for a direct normalizer gain, a normalized oracle gain,
  a normalized exact endpoint, and a normalized ZeroSlack endpoint;
- an axiom transcript for every public declaration, rejecting project axioms
  and `Classical.choice`;
- hostile source checks rejecting an unresolved branch, normalization without
  semantic equivalence or non-increasing size, unrelated fuel recursion,
  unproved oracle construction, and widened runtime/ZeroSlack/final claims;
- theorem-inventory, formal-status, publication-map, progress-ledger, and
  canonical-report updates with the fixed score unchanged; and
- normal core and PNPLabs verification, exact-merge reproduction, publication,
  and deployment gates.

## Verification and deduplication

Compile the new module, regression, and axiom audit first on the capped remote
builder. After the theorem source stabilizes, regenerate the compiled inventory
and all derived publication artefacts once, then run the complete core suite and
fresh exact-merge reproduction. PNPLabs consumes the exact merged evidence and
does not rebuild Lean.

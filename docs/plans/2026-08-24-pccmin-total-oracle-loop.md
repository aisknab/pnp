# M189 proof-bearing PCCMin total-oracle loop

## Evidence-led selection

M188 made the PCCPack generator and checker transparent, but its explicit
`PCCMinLoopCertificate` still arrives from outside the active construction.
The formal status continues to leave `Formal.ResidualBandMinimizer`,
`Formal.ZeroSlack`, and `Formal.PolynomialRuntimeAndCertificateBounds` open.
The existing residual kernel proves strict semantic descent, finite gain-chain
bounds, and exact stopping once global no-gain evidence is supplied, but it
does not yet contain the report's recursive PCCMin control flow.

M189 adds that general control-flow kernel. A typed total oracle may return a
genuine strict equivalent gain, an exact-minimum result, or a proof-bearing
ZeroSlack result for the current implementation. The transparent recursive
loop follows gains, terminates by strict residual-slack descent, preserves the
complete Boolean semantics, returns a globally minimum implementation, and
bounds the number of gain iterations by the starting residual slack.

## Legacy anchor and unbounded abstraction

- Legacy anchor: the canonical manuscript's PCCMin loop and rank-parametric
  ZeroSlack endpoint in Section 16, especially the three oracle outcomes and
  the claim that every nonterminal gain lowers residual slack.
- Closed edge: proof-bearing total oracle outcomes at every current
  implementation -> well-founded recursive PCCMin control flow -> exact
  minimum result and semantic gain-iteration bound.
- Unbounded abstraction: arbitrary input and output dimensions, every finite
  direct-wire implementation, and every total oracle whose outcomes carry the
  exact Lean proofs required by their route. The theorem is not tied to one
  circuit, supplied finite candidate list, or fixed iteration count.

## Exact theorem target

Define the dependent outcome type and total oracle interface

```text
PNP.DirectWire.PCCMinOracleOutcome current
PNP.DirectWire.PCCMinTotalOracle
```

with only three routes:

```text
gain next (StrictEquivalentGain current next)
exact (ExactMinimumResult current)
zeroSlack (ZeroSlackResult current)
```

Define a transparent well-founded loop

```text
PNP.DirectWire.runPCCMinTotalOracleLoop
```

and prove

```text
PNP.DirectWire.pccmin_total_oracle_loop_checked_complete
```

for every oracle and current implementation. The checked endpoint must expose
semantic equivalence of the result to the input, global semantic minimality,
the exact reference-minimum gate count, zero result slack, and a gain-iteration
bound by the input residual slack.

## Claim boundary and downstream blockers

M189 does not construct the total oracle. In particular, it does not derive
terminal families, route tables, selector completeness, HN/BUD/HB semantics,
unconditional ZeroSlack, or a polynomial implementation of any oracle route.
It does not formalize normalization, encode the loop as a finite raw machine,
bound the cost of one iteration, prove the starting residual band logarithmic,
construct a residual-band decider, complete Cook--Levin, prove SAT hardness,
put CNFSAT in P, create the eligible root theorem, open a global gate, or prove
`P = NP`.

Because the load-bearing oracle remains an explicit argument, M189 does not
close the fixed `pccmin-executable-loop`,
`pccmin-iteration-sound-descent`, or
`pccmin-termination-exactness` checkpoints. The risk-weighted estimate remains
35 percent with a 20-to-40-percent uncertainty range and zero of five global
gates closed. One formal-publication evidence row may be added without calling
that row proof completion.

## Required evidence

- compilation of the new module and the explicit root import;
- a focused regression instantiating gain, exact, and ZeroSlack terminal paths
  without introducing an axiom;
- an axiom transcript for every public declaration, rejecting project axioms
  and `Classical.choice`;
- hostile source checks rejecting an unresolved outcome, a non-strict gain,
  recursion on an unrelated fuel, loss of semantic equivalence, deletion of
  the iteration bound, or widened runtime/ZeroSlack/final claims;
- theorem-inventory, formal-status, publication-map, progress-ledger, and
  canonical-report updates with the fixed score unchanged; and
- normal core and PNPLabs verification, merge reproduction, publication, and
  deployment gates.

## Verification and deduplication

Run the new module, regression, and axiom audit first on the capped remote
builder. After the theorem source stabilizes, regenerate the compiled inventory
and all derived publication artefacts once, then run the complete core suite and
fresh exact-merge reproduction. PNPLabs consumes the exact merged evidence and
performs its full current-surface audit without rebuilding the already verified
Lean tree.

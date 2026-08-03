# Verified residual-gain chain bound

`lean/PNP/ResidualGainChain.lean` formalizes one unbounded part of the
residual-band minimization argument: a finite sequence of independently
verified strict equivalent gains cannot be longer than the residual slack of
its starting implementation. `lean/PNP/LockedNANDResidualGainBound.lean`
specializes that theorem to the complete locked-NAND candidate.

## Legacy anchor

The intended route is the canonical manuscript pinned by
`archive/legacy-v0/ARCHIVE.json` at the annotated tag
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`.

- Report §16 states, in the `PCCMin` loop, that every nonterminal verified gain
  lowers residual slack by at least one and therefore the number of gain steps
  is at most the starting residual slack.
- Report §17 proves the locked-NAND family has residual slack at most four.

This milestone reconstructs exactly that iteration-count edge. It does not
formalize the manuscript's route generator, stopping rule, ZeroSlack
contradiction, exact-minimum return branches, or polynomial runtime.

## Lean interface

For implementations with fixed input and output widths:

- `StrictGainChain current chain` requires every adjacent pair to carry a
  `StrictEquivalentGain` proof;
- `strictGainChainBool current chain` executably checks the same adjacency
  condition using the exhaustive finite truth-table equivalence checker from
  `ResidualRoutes`;
- `gainChainEnd current chain` returns the final disclosed implementation;
- `strictGainChainBool_eq_true_iff` proves that Boolean acceptance is exactly
  the proof-bearing predicate;
- `StrictGainChain.end_equivalent` and
  `StrictGainChain.end_referenceMinimum_eq` preserve complete multi-output
  semantics and the exhaustive semantic reference minimum;
- `StrictGainChain.end_residualSlack_add_length_le` proves

  ```text
  residualSlack(endpoint) + chain.length ≤ residualSlack(start).
  ```

  Consequently, `StrictGainChain.length_le_residualSlack` and the two Boolean
  transport theorems bound the number of accepted steps by the starting slack
  or by any separately proved upper bound on that slack.

If the starting slack is zero, both the proof-bearing and executable forms
prove that an accepted chain is empty. This is a consequence of an already
proved zero-slack premise; it is not a procedure for establishing ZeroSlack.

The locked specialization packages `fullCandidate circuit` as an
`Implementation`, imports the existing
`fullCandidate_residualSlack_le_four`, and proves that every proof-bearing or
executably accepted chain from that candidate has length at most four.

## Trust and audit boundary

The generic module has 12 public declarations. Its complete `#print axioms`
transcript reports no axioms for every declaration. The locked specialization
has four public declarations; their compiled closure is exactly the approved
Lean-standard pair `Quot.sound` and `propext`, inherited from the existing
finite semantic candidate construction. Neither transcript contains a project
axiom or `Classical.choice`.

The static hostile audit rejects changed adjacency, `&&` replaced by `||`,
incorrect endpoint threading, a hard-coded family bound in the universal
module, removal of the locked residual-slack theorem, a changed four-step
bound, transcript drift, hidden assumptions, private or unaudited
declarations, `sorry`, `admit`, native evaluation, host lookup, caller
certificates, exact-search injection, and theorem overclaims.

Run the focused checks after building the root target:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualGainChainAxiomAudit.lean
lake env lean -DwarningAsError=true lean-audit/PNPLockedNANDResidualGainBoundAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualGainChain.lean
node --test audits/lean-residual-gain-chain0.test.mjs
```

## Exact non-claims

The checker validates a chain supplied to it. It does not find a gain, prove
route completeness, exclude an unlisted or undisclosed gain, or justify
stopping before the residual bound is exhausted. It does not construct a
ZeroSlack certificate, compute an exact minimizer, prove a polynomial runtime
for exhaustive truth-table checking or PCCMin, put SAT in deterministic
polynomial time, discharge any of the four project assumptions, or prove
`P = NP`.

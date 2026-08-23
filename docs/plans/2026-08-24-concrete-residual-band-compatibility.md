# M187 concrete residual-band language compatibility

## Evidence-led selection

The active bridge still names `PNP.ResidualBandExactMinimization` as an
uninterpreted project axiom and asks callers to supply a second reduction from
the report-facing locked-NAND threshold language. M186 established that the
locked-NAND endpoint is already the concrete all-bitstring predicate decoded
from a candidate and threshold. That predicate is not restricted by a
caller-supplied locked-shape certificate: after fail-closed decoding it asks
the existing direct-wire semantic specification whether the exact reference
minimum exceeds the encoded threshold.

M187 makes that existing predicate the concrete residual-band decision
language. The locked-NAND endpoint and residual-band endpoint therefore share
the same canonical query bytes and exact semantic threshold, so their
polynomial reduction is the concrete identity program rather than caller
trust. This removes the language axiom and the corresponding checker-trust
field without claiming that the exhaustive semantic specification is an
executable polynomial minimizer.

## Legacy anchor and unbounded abstraction

- Legacy anchor: the canonical manuscript's Sections 16.2, 17.2 and 18,
  specifically the exact-minimum threshold query consumed by the locked-NAND
  SAT decision rule and the locked-to-residual-band compatibility edge.
- Closed edge: canonical encoded direct-wire candidate and threshold -> exact
  reference-minimum predicate -> report-facing residual-band language ->
  identity locked-to-residual transport.
- Unbounded abstraction: arbitrary finite input, gate and output counts,
  arbitrary intrinsically typed direct-wire candidates, arbitrary natural
  thresholds, and every external bitstring through the fail-closed decoder.

## Exact theorem target

Factor the current concrete locked-NAND target through a generally named
`EncodedDirectWireMinimumThreshold` predicate. For every intrinsically typed
candidate and threshold, prove that encoding and decoding the query yields
exactly

```text
threshold + 1 <= referenceMinimum candidate
```

Define `PNP.ResidualBandExactMinimization` as that concrete predicate, prove
that `PNP.LockedNANDThreshold` is the same language, construct the identity
polynomial reduction, and refactor `CheckerTrustModel` so it no longer accepts
a supplied residual-band reduction. Expose the complete compatibility surface
through one named M187 theorem.

## Claim boundary and downstream blockers

`referenceMinimum` is the already checked finite exhaustive semantic
specification. M187 does not turn that specification into the report's PCCMin
algorithm, prove it polynomial, construct ZeroSlack evidence, prove an
encoded-size residual-band promise, or provide a concrete residual-band
decider. The supplied `PCCMinLoopCertificate.residualBandDecider` remains an
external proof-bearing field. Concrete SAT NP-hardness, deterministic SAT in
P, `GeneratePCCPack`, `CheckPCCPackexp`, the eligible root theorem, and all five
global gates remain open.

This closes exactly the fixed checkpoint
`axiom-remove-residual-band-minimum`. The compiled project-axiom inventory must
fall from three to two and the risk-weighted estimate may move from 32 to 33
percent only after the regenerated inventory proves that the axiom is absent.
The 20--40 percent uncertainty range remains unchanged. One formal-publication
row is added, so current coverage should move from 162/164 to 163/165.

## Required evidence

- focused Lean compilation and axiom transcripts for the general predicate,
  encoded-query theorem, residual-band compatibility, bridge, and root import;
- regression of arbitrary typed candidates, malformed-input rejection,
  language equality, identity transport, P transport, and the two-field checker
  trust boundary;
- hostile checks rejecting restoration of the project axiom, a supplied
  reduction field, a modified endpoint path, caller truth flags, hidden P
  membership, or widened minimizer/runtime claims;
- compiled theorem-inventory and formal-status updates showing two remaining
  project axioms, the absent eligible root, false publication gate, and all
  five global blockers still open;
- a fixed-checkpoint score transition with exact compiled evidence and an
  unchanged uncertainty range; and
- complete core and PNPLabs publication, review, clean-merge reproduction,
  deployment, provenance, route, and service verification gates.

## Verification and deduplication

Run source-contract checks first. Compile the changed Lean dependency and root
once on the capped remote builder, then run the focused regression and axiom
audit. After source stabilization, regenerate the inventory, status, progress
ledger and publication artifacts and run the complete core suite once.
PNPLabs consumes the exact merged core artifacts and performs its full current-
surface publication audit without rebuilding Lean already proved for the same
core tree.

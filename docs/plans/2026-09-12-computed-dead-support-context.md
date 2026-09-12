# M245: computed dead-support replacement context

## Legacy anchor and selected dependency edge

The pinned manuscript's section 5 Package E direct-wire verifier and Traceable
normalization theorem distinguish an explicit compatible proper support and
replacement from a smaller whole-circuit implementation. M244 proves physical
output-cone pruning but does not construct that local replacement context.

This milestone closes the physical deletion edge:
computed output cone -> dead-gate complement with no outgoing ports -> actual
extracted support and input-boundary environment -> explicit zero-output
replacement in a concrete frame -> checked proper-support physical gain.

It does not claim a complete Package E verifier, arbitrary full-profile
compatibility, all N1–N10 traces or global route completeness.

## Construction and exact general theorem target

For every finite `current : Implementation inputs outputs`, compute the dead
support as the existing physical complement of `outputConeRecords current.candidate`.
Prove that its actual outgoing interface is empty. Compute its incoming values
from the retained live frontier, preserving actual primary inputs and all
original ordered outputs as bypass outputs. Use the existing support extractor
and `FramedContext`, with the live cone as environment and a zero-gate bypass
continuation. No context, support, profile observer, replacement correctness
certificate or semantic-minimum witness is supplied by a caller.

Expose the already computed M244 live frontier through a small public wrapper
and a universal semantic theorem. Reuse the existing implementation and proofs;
do not introduce a second gate compiler. Update the closed M244 public-interface
fixture in the same patch, preserving all eleven original theorem types and pins.

For the resulting `deadSupportContext current`, whose support has zero outputs,
the central statement is:

```lean
theorem deadSupportContext_plug_equivalent {inputs outputs replacementGates : Nat}
    (current : Implementation inputs outputs)
    (replacement : Candidate (deadSupportBoundary current).length replacementGates 0) :
    Equivalent ((deadSupportContext current).plug replacement).program
      ((deadSupportContext current).plug replacement).directWireWord
      current.candidate.program current.candidate.directWireWord
```

Prove the environment's exact induced boundary values, complete original-output
semantics, actual dead-support extraction, exact frame size accounting and
equivalence of the zero-gate replacement to the zero-output support. Package a
computed physical gain witness only when both the deleted support and retained
cone are nonempty. Prove acceptance exactly at that boundary and exact physical
slack descent for every returned witness.

An all-unused circuit is not a proper-subset witness. Keep that case explicit;
a normalization component may still return the equivalent smaller circuit in its
non-gain result, without claiming global normal form or semantic minimality.
Do not replace a failed general context proof with a supplied frame or a finite
example.

## Source and expectation changes as one changeset

- M244 frontier wrapper: preserve computation and all existing theorem types;
  update its closed source-head fixture before running that focused contract.
- New context, boundary and witness source: exact arbitrary-dimension Lean type
  regressions, exact axiom audit, root import, inventory producer/required-name
  consumer, publication fingerprint set and durable read-only workflow block.
- Positive fixtures: noncontiguous dead gates depending on live gates, shared
  live predecessors, repeated original outputs, constants and primary inputs.
- Negative fixtures: no deleted gates, all gates dead, zero dimensions, and
  arbitrary full-profile observers that distinguish a physical size reduction.
- No exhaustive subset, candidate, valuation or reference-minimum search in the
  new computation. Runtime fixtures remain bounded test evidence, not proof
  authority.
- Generate status, progress and report only after the final Lean source is
  stable. Derive fingerprints and counts from compiled evidence; reconcile
  current documentation and hostile tests before the broad suite.

## Verification and release

Use one independent remote checkout and an exact predecessor-tree/toolchain
cache preflight. Run the changed leaf chain and targeted contracts first, then
the explicit root and exact type/axiom workflow block. Seal the full inventory,
generate status/progress/current documentation, run focused hostile contracts,
perform the report's built-in reproduction once and one deduplicated complete
suite. Keep normal PR/post-merge CI and exact-object independent reproduction.
Reanchor to the actual M244 merge before publication; do not rerun unchanged
heavy evidence after a same-tree reanchor.

Remove this milestone's exact temporary checkout and transport directory after
final release verification, or after a diagnosed abandoned investigation.

## Progress and publication

Risk-weighted proof completion remains 40%, with 20% to 40% uncertainty, unless
a named fixed checkpoint is actually discharged. No checkpoint transition is
currently expected. Formal artefact coverage is generated independently.
Global gates closed remain 0 of 5; the eligible root remains absent and the
publication gate false.

Properness here concerns the physical gate support and concrete frame, not the
complete manuscript profile, obligation and carrier admissibility conditions.
Unconditional SaturatePositive, BCELReady, ZeroSlack, complete polynomial PCCMin
and deterministic SAT remain open. No claim of encoded-size polynomial runtime
follows from finite termination.

Publication decision: defer PNPLabs. This physical replacement component alone
does not change the coherent published M231 bottom line. Keep meaningful
verified submilestone notifications independent of website cadence.

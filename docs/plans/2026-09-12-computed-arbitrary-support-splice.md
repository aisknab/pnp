# M249: computed arbitrary-support literal replacement

## Pinned dependency and complete milestone boundary

The canonical manuscript pinned by `archive/legacy-v0/ARCHIVE.json`, section 2
Compatible replacement and section 5 N1 topological reorder and renaming,
requires an actual direct-wire program after replacing a support. The existing
arbitrary-support extractor computes every incoming and outgoing port. M237
already constructs a replacement frame for predecessor-closed production
saturation, and M245 handles the computed dead complement. Preserve those
results; do not earn this milestone by repeating them.

Construct the literal replacement graph for an arbitrary extracted support and
an arbitrary replacement word on its exact boundary and ordered interface.
Derive source rebinding, the retained exterior gates, replacement gates, global
outputs, and a deterministic topological compilation from those actual objects.
No replacement frame, gate permutation, schedule, source map, acyclicity proof,
or correctness certificate is a caller argument to the construction.

## Exact general targets

First construct a generic finite raw NAND graph compiler. Scan remaining nodes
in canonical order, append only a node whose two sources are already available,
and remove that exact node. Derive all reindexing maps. Termination is bounded
by the input node count. A stuck nonempty remainder must exhibit an unresolved
predecessor for every remaining node; an acyclic graph cannot be stuck.
Prove complete output semantics against every solution of the original graph
equations and exact accounting of emitted and remaining nodes.

Then construct and compile the actual support replacement graph. For all finite
dimensions, candidates, selection records and same-frontier replacement words:

- successful compilation has exactly the exterior-gate count plus replacement
  gate count, with no invented, duplicated or silently discarded node;
- if the replacement has the extracted support's complete Boolean semantics,
  every ordered global output has the original semantics;
- a strict local physical saving becomes an actual whole-program strict gain
  when the literal graph compiles;
- predecessor-closed production saturation gives an acyclic graph without a
  supplied ordering, so this interface agrees semantically and in size with
  the already checked M237 construction; and
- cyclic literal wiring is rejected, never interpreted as a valid NAND word.

The milestone is not earned by the generic compiler alone, a supplied ordering,
a finite example, or a classifier without the actual support-splice semantics.

## Interpretation and claim boundary

The manuscript requires words to be acyclic, intrinsically ordered NAND
programs. Raw physical port compatibility alone must not be silently treated
as a proof that any replacement's literal wiring is acyclic. Investigate a
minimal interleaved-support example as a regression; do not claim a manuscript
contradiction without establishing its complete carrier premises.

This is the physical well-formedness and substitution edge, not a construction
of the full manuscript profile, R5/R6-R8 obligation ledger, arbitrary-support
Pull/Expand materializer identities or complete Package E. The existing full-
profile observer, global routing, SaturatePositive, BCELReady, ZeroSlack,
PCCMin exactness and encoded-size polynomial bounds remain open. A node-count
termination bound is not a total polynomial runtime theorem. No fixed weighted
checkpoint or global gate is expected to close.

## Source and expectation changes together

Prepare arbitrary-dimension theorem types and axiom contracts with the source.
Regression cases must include source order different from numeric node order,
disconnected nodes, repeated and constant/input outputs, empty dimensions,
self/mutual cycles, arbitrary interleaved support, a smaller replacement,
and actual predecessor-closed saturation. The bounded fixtures must not execute
semantic reference minima or pretend to be universal proof authority.

Hostile contracts must reject supplied schedules, skipped remaining nodes,
unresolved-source defaults, changed ordered outputs, invented savings,
unrestricted cyclic acceptance, finite-only theorem substitutes, altered
compiled types or axioms, and claims of complete profile or global closure.
Update root imports, reviewed-name producers and consumers, exact workflow
blocks, publication/status generators, documentation and tests in one coherent
change after the complete constructor is proved.

## Verification, release and cleanup

Use one separate remote checkout and an exact source-tree/toolchain-matched
cache. Run bounded leaf feedback, then the explicit root and exact workflow
audit/regression block. Freeze Lean source before inventory sealing. Reconcile
the root-closure contract for both explicit pinned-toolchain list imports and
run its positive and unknown-import rejection cases during source preflight.
Reconcile generated expectations before focused contracts, report reproduction
and one deduplicated standard suite. Preserve normal PR/post-merge checks and
exact-object reproduction, without repeating unchanged-tree proof work.

Release only after preceding queued milestones are fully earned. Reanchor
onto the actual verified parent merge and require the tested tree unchanged.
Remove the task-created checkout, patches, helpers and logs after release
verification or completed diagnosis of an abandoned approach.

Proof completion remains 40%, with uncertainty 20% to 40%, unless a fixed
checkpoint actually changes with compiled evidence and rationale. Report
formal artefact coverage separately. Publication decision: defer PNPLabs,
because this physical substitution component alone does not change the
coherent published M231 bottom line. Notify meaningful verified substeps
independently of website cadence.

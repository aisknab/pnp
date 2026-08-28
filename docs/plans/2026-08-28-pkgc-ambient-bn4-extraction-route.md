# M203: PkgC ambient-BN4 extraction route

## Legacy anchor and dependency edge

- Legacy anchor: the pinned manuscript's Section 11.5
  `Separating-consumer theorem`, specifically the branch where a complete
  quotient-to-full matching must produce a same-key cancellation against the
  BN4 residual ledger. Section 11.6 then permits BN6 cellization only after
  every earlier PkgC outcome has been routed.
- Current formal boundary: M202 returns a source-member PkgC same-key
  cancellation, conditional ZeroSlack, or an exact source-ledger BCEL
  activation mismatch. The older ambient-BN4 bridge can reduce an ambient
  residual ledger after a PkgC cancellation, but it still requires the caller
  to supply both an exact remainder and its multiset-permutation embedding.
- Exact edge closed by M203: compute the order-independent removal of the
  generated PkgC cancellation subledger from one candidate-bound ambient BN4
  ledger. Return either the computed remainder with its exact complete
  residual reduction, or a proof that no exact multiset embedding exists. Feed
  that total result into M202's PkgC-cancellation branch while preserving its
  conditional-ZeroSlack and source-activation-mismatch branches literally.

This is an arbitrary-finite theorem. It must not fix the source-cell count,
ambient-ledger length or order, carrier, cut, candidate, circuit, semantic key,
transport key, restoration coordinate, rank count, or selector count.

## Unbounded abstraction and theorem targets

Implement a constructive remove-first multiset extractor over arbitrary finite
lists. For every required list and ambient list it must return exactly one of:

1. a computed remainder together with
   `ambient.Perm (required ++ remainder)`; or
2. a required member together with proof that no remainder can satisfy that
   exact permutation equation.

The recursive implementation must use decidable equality and `List.erase`.
It must preserve duplicates and accept every permutation of an admissible
ambient ledger. It may not use powerset enumeration, a supplied remainder, a
supplied permutation certificate, `Classical.choice`, or an opaque success
Boolean.

Specialize that extractor to
`pair.restorationCancellationCells restorer`. On success, construct the
existing `TerminalPkgCAmbientBN4LedgerEmbedding`, the candidate-derived
`TerminalComputedBN4ActivationCancellation`, and the exact canonical residual
reduction mechanically. On failure, retain the generated cell and prove that
no exact `TerminalPkgCAmbientBN4LedgerEmbedding` exists for any remainder.

Define a source-level wrapper around M202 whose ambient ledger is checked
against the same computed BCEL-ready nucleus. Its total outcome must preserve:

1. `ZeroSlackResult candidate.toImplementation`;
2. an exact source-member PkgC separating pair and same-key realization,
   together with a computed candidate-bound ambient BN4 bridge and complete
   residual reduction;
3. an exact source-member PkgC separating pair and same-key realization,
   together with a generated cell and proof that no exact ambient multiset
   embedding exists; or
4. M202's original nonempty proper singleton/pair cut whose PkgC source
   activation weight differs from the checked BCEL defect.

The public endpoint will be
`PNP.DirectWire.pccmin_checked_packet_pkgc_ambient_bn4_extraction_route_or_zeroslack_checked_complete`.
Its PkgC-success branch must existentially retain the computed remainder,
embedding, candidate-derived BN4 kernel, and exact complete residual-ledger
equality. Its failure branch must retain the no-embedding proof, not merely a
failed equality test or a caller-supplied route label.

## Claim boundary and downstream blockers

The terminal problem, checked finite BCEL-ready certificate, active V54 source
systems and cuts, positive payload atoms, typed restorer, ambient BN4 ledger,
realizer table, accepted claims, rank assignment, dependency table, checked HB
closure, route-clear result, and selector silence remain explicit inputs. M203
checks that every ambient cell uses the candidate-derived BN3 request-atom
space, but it does not derive the ambient cells, source systems, payloads, or
restorer from every valid terminal input.

The computed residual reduction is exact structural evidence. It does not by
itself prove that the remainder is empty, that a surviving residual is
contradicted, or that the PkgC branch gives a verified gain or globally
rank-decreasing transition. A failed exact embedding is a precise missing
compatibility obligation, not a global route. M203 does not construct upstream
BN3--BN5 data, complete PkgC/BN3--BN6 integration, derive blocker semantics or
semantic dependency completeness, prove manuscript-wide `SaturatePositive` or
`BCELReady`, establish unconditional `ZeroSlack`, or construct complete
encoded-size polynomial `PCCMin`.

No fixed progress checkpoint changes state. The risk-weighted estimate remains
35 percent, the uncertainty range remains 20 to 40 percent, and zero of five
global gates remain closed. Formal artefact coverage may change independently
when the publication row is earned.

## Required evidence

- compilation of the arbitrary-finite multiset extractor, computed
  ambient-BN4 specialization, four-way source composition, public endpoint,
  and explicit `PNP` root import;
- regression coverage for a permuted ambient ledger with duplicate generated
  cells, a multiplicity-deficient ambient ledger, the conditional-ZeroSlack
  branch, and M202's source-activation-mismatch branch;
- exact checks that the success branch constructs its remainder and
  permutation rather than accepting either from the caller, and that the
  complete ambient residual ledger equals the computed remainder's residual
  ledger;
- hostile checks rejecting a supplied remainder, supplied embedding, literal
  generated-then-remainder-only serialization, erased mismatch, fixed ambient
  order or length, powerset enumeration, and claims of a verified gain,
  complete route integration, unconditional ZeroSlack, or polynomial PCCMin;
- axiom transcripts for every reviewed declaration, rejecting project axioms,
  `sorryAx`, and `Classical.choice`; and
- synchronized theorem inventory, publication map, status, progress history,
  report, durable workflow expectations, audit questions, and current
  documentation.

## Stop condition

If remove-first extraction cannot construct
`ambient.Perm (generated ++ remainder)` for every accepted permutation, if a
failure cannot prove that no exact remainder embedding exists, or if the
computed success cannot inhabit the existing candidate-derived ambient BN4
residual-reduction boundary, stop at that theorem edge. Do not replace it with
a supplied remainder, supplied permutation, canonical-order-only equality,
fixed finite instance, new axiom, `sorry`, weakened theorem, or broader
completion claim.

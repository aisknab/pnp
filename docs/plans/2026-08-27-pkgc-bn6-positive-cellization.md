# M201: PkgC-to-BN6 positive cellization

## Legacy anchor and dependency edge

- Legacy anchors: the pinned manuscript's PkgC separating-consumer theorem,
  especially `separatingConsumersSingletonized`, and the first paragraph of
  `BN6-HypergraphPacket` that assigns each surviving active quotient key its
  singleton footprint `E(kappa)` with `|E(kappa)| >= 2`.
- Current formal boundary: the PkgC kernel can return an exact same-key
  cancellation or prove that every disjoint consumer pair is singletonized.
  Separately, canonical BN6 grouping consumes raw support lists whose
  length-at-least-two proofs are supplied. No theorem currently constructs
  those BN6 cells from the PkgC consumer systems or proves that the resulting
  raw cut ledger equals the original two-sided activation ledger.
- Exact edge closed by M201: for an arbitrary finite family of active consumer
  systems over one carrier, run the PkgC classifier for each source cell. Return
  the first exact same-key cancellation, or construct every BN6 positive cell
  from the system's singleton footprint and prove exact activation-weight
  conservation for every cut.

This is an arbitrary-finite theorem. It must not fix the carrier, source-cell
count, consumer family, cut, payload, restoration coordinate, candidate, or
circuit.

## Unbounded abstraction and theorem targets

Define one source cell containing:

- a finite minimal-consumer system;
- exact equality between that system's carrier and the common carrier;
- one proof-bearing cut on which the two-sided request is active; and
- one strictly positive payload atom.

For a PkgC-singletonized source cell, prove constructively that:

1. the singleton footprint is a duplicate-free sublist of the common carrier;
2. the active cut supplies two distinct singleton-footprint atoms, so the
   footprint has length at least two;
3. carrier normalization leaves that footprint unchanged;
4. the source cell therefore constructs a valid `TerminalBN6PositiveCell`; and
5. on every cut, the constructed BN6 cell's contribution is exactly the
   source system's two-sided activation bit multiplied by its payload mass.

Define a total recursive classifier over an arbitrary finite source-cell list.
Its successful branch must return a constructed BN6 positive-cell list with
the same length and payload order and prove, for every cut,

```text
terminalBN6PositiveCellsActivationWeight carrier constructedCells cut =
  terminalPkgCBN6SourceActivationWeight sourceCells cut
```

Its failure branch must retain the exact source cell, list membership, first
PkgC separating pair, and proof-bearing
`TerminalPkgCSameKeyCancellationRealization`. It must not return an opaque
Boolean, a caller-labelled route, or an erased mismatch.

The public endpoint will be
`PNP.DirectWire.terminalPkgC_bn6_positive_cellization_checked_complete`.

## Claim boundary and downstream blockers

The active source consumer systems, payload atoms, typed restoration operation,
and restoration-coordinate preservation remain explicit inputs. M201 does not
derive these objects from a terminal candidate, construct the BN3/BN4 ledger,
prove BN5 negative-residual silence, or turn a returned PkgC cancellation into
a globally ranked gain or descent.

The theorem constructs the raw BN6 support ledger and proves exact activation
conservation only after every source system reaches the PkgC singletonized
branch. It does not establish the BCEL constant-cut equation, checked Packet
table, selector faithfulness, blocker semantics, semantic dependency
completeness, complete route silence, or encoded-input polynomial bounds.

Consequently M201 does not close complete PkgC/BN3--BN6 integration,
manuscript-wide `SaturatePositive` or `BCELReady`, unconditional `ZeroSlack`,
polynomial `PCCMin`, deterministic CNFSAT in P, a global gate, the eligible
root theorem, or P = NP. No fixed progress checkpoint changes state. The
risk-weighted estimate remains 35 percent, the uncertainty range remains 20
to 40 percent, and zero of five global gates remain closed. Formal artefact
coverage may change independently when the publication row is earned.

## Required evidence

- compilation of the arbitrary-finite source-cell conversion, total list
  classifier, activation-conservation theorem, and explicit `PNP` root import;
- regressions for a multi-cell singletonized family and for a nonsingleton
  separating pair that returns an exact same-key cancellation;
- payload-order, list-length, footprint-normalization, and all-cut activation
  conservation checks;
- hostile checks rejecting a supplied BN6 support list, supplied
  singletonization or footprint-size certificate, fixed carriers, erased PkgC
  evidence, powerset enumeration, and claims of complete PkgC/BN6 integration,
  polynomial PCCMin, or unconditional ZeroSlack;
- axiom transcripts for every reviewed declaration, rejecting project axioms,
  `sorryAx`, and `Classical.choice`; and
- synchronized theorem inventory, publication map, status, progress history,
  report, workflow expectations, audit questions, and current documentation.

## Stop condition

If PkgC singletonization plus a genuine active cut does not construct a
length-at-least-two singleton footprint with exact all-cut activation
conservation, stop at that theorem edge. Do not replace it with a supplied
footprint-size proof, sampled cuts, a fixed carrier, a powerset scan, a new
axiom, `sorry`, a weakened route, or a broader completion claim.

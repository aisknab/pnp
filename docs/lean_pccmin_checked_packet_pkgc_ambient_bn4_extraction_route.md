# Source-derived PkgC ambient-BN4 extraction route

M203 closes one exact structural seam in M202's PkgC-cancellation branch. The
older ambient-BN4 bridge could prove a complete residual reduction only after
the caller supplied a proposed remainder and a permutation certificate. M203
instead computes the remainder from an arbitrary-order ambient ledger while
preserving every duplicate occurrence.

The extractor recursively removes the first matching ambient occurrence for
each generated PkgC cancellation cell. It returns either:

- a computed remainder with
  `ambient.Perm (generatedCancellationCells ++ remainder)` and the induced
  equality of complete canonical residual ledgers; or
- a required generated cell together with proof that no remainder can satisfy
  the exact multiset embedding.

The implementation uses explicit `DecidableEq`, `List.erase`, and constructive
`List.Perm` recursion. It does not use a supplied remainder, caller-supplied
permutation, powerset enumeration, `Classical.choice`, or a Boolean-only
failure. A private constructive permutation lemma replaces the standard
convenience theorem whose dependency closure includes `Classical.choice`.

The candidate-bound specialization checks that the ambient cells use the same
computed BCEL nucleus's canonical BN3 request atoms, constructs the existing
BN4 activation-cancellation kernel internally, and packages the exact ambient
residual reduction. The source-level composition then preserves all M202
branches: conditional ZeroSlack, source activation mismatch, or an exact
source-member PkgC cancellation refined to either computed ambient reduction
or proved ambient incompatibility.

The public endpoint is
`PNP.DirectWire.pccmin_checked_packet_pkgc_ambient_bn4_extraction_route_or_zeroslack_checked_complete`.

## Claim boundary

The terminal problem, checked finite BCEL-ready certificate, active V54 source
systems and cuts, payload atoms, typed restorer, ambient BN4 ledger, realizer
table, accepted claims, ranks, dependency table, checked HB closure,
route-clear result, and selector silence remain supplied. The ambient ledger is
candidate-bound by its canonical request-atom check, but it is not constructed
from every valid terminal input.

An extracted balanced subledger gives an exact residual-ledger reduction; it
does not prove that the computed remainder is empty or that a surviving
residual is contradicted. A no-embedding result is a precise compatibility
failure, not a verified gain or globally rank-decreasing transition. M203 does
not construct source systems, payloads, the restorer, or downstream tables,
complete PkgC/BN3--BN6 integration, derive blocker semantics or semantic
dependency completeness, prove manuscript-wide SaturatePositive or BCELReady,
establish unconditional ZeroSlack, construct executable polynomial PCCMin,
prove encoded-input polynomial bounds, put CNFSAT in P, create the eligible
root theorem, or prove P = NP.

Formal artefact coverage is 179 of 181 current scoped rows. The separate
risk-weighted proof-completion estimate remains 35 percent, its uncertainty
range remains 20 to 40 percent, and zero of five global gates are closed.

## Verification

```text
lake build PNP
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinCheckedPacketPkgCAmbientBN4ExtractionRoute.lean
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinCheckedPacketPkgCAmbientBN4ExtractionRouteAxiomAudit.lean
node --test audits/lean-pccmin-checked-packet-pkgc-ambient-bn4-extraction-route0.test.mjs
```

The axiom transcript covers ten reviewed declarations. Every declaration
reaches only the approved Lean-standard closure (`propext` and `Quot.sound`);
no project-specific axiom, `sorryAx`, or `Classical.choice` is present.

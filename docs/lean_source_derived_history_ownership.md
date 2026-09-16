# Source-derived physical history ownership

This is the ownership and integer-charge connection for the existing
[computational wire histories](lean_computed_r7_history.md) and their
[literal arbitrary-support splice](lean_wire_history_arbitrary_support.md).
It reconstructs the selected edge from section 4 ChargeSoundness and section
6.1 R9 accounting of the [pinned manuscript](../archive/legacy-v0/ARCHIVE.json).

The source-only entry point is
`PNP.DirectWire.WireHistoryAmbientOwnership.compileOwned`. Its inputs are the
original candidate, selected records and raw events. It runs the existing
history constructor and existing splice compiler internally. It does not accept
an owner family, allocation amount, provenance map, partition proof, topological
order or successful-splice certificate.

## What the record means

Each initial physical gate has an `original` label containing its actual
source coordinate. Each appended materializer gate has an `allocated` label
containing its executing event identity and its local gate coordinate. A
snapshot's creation identity is causal metadata, not the identity of every
later allocation descended from it.

The record distinguishes:

- `live`: labels in the final program's actual physical-position order;
- `charged`: every gate physically allocated during the history;
- `removed`: every original or allocated gate removed by normalization.

Its central conservation statement is a permutation, not an arbitrary equality
of counts:

```text
live ++ removed  ~  original ambient gates ++ charged
```

The left side has no duplicate labels. Its live length is the actual result
gate count; charged and removed lengths are the existing execution's allocation
and removal totals. A removed allocation remains in the historical charged
record. It is not charged again as part of a surviving extracted piece.

## Where the identities come from

| Construction boundary | Source of the physical identity |
| --- | --- |
| Constant propagation | The actual translated-gate append or elimination branch |
| Structural sharing | The actual append or reuse decision; a reused alias does not create a second gate |
| Output-cone pruning | The actual extractor's selected-gate position and computed inverse |
| Complete normalization | Composition through the existing normalization trace |
| Computational history | The executing event and the literal materializer append range |
| Original selected support | The extractor's inverse maps positions back to ambient source coordinates |
| Unchanged exterior | Each actual exterior gate appears once |
| Final program order | The inverse of the same topological compiler position map that built the program |

Creation, cancellation and reads do not allocate gates. R7 and R8 append exactly
the gates in their actual computed materializers. Repeated normalization retains
the surviving labels and records each deleted label once.

The inverse position map is computed by searching the actual compiler placement
map. Theorems prove both inverse directions, injectivity and the complete
permutation of raw nodes; a gate-count equality is not used as a substitute
for physical correspondence.

## Reuse of the existing ownership kernel

`OwnedCompilation.eventRequests` enumerates final physical positions and groups
only the surviving allocations whose executing identity matches a raw event.
This family is computed before a result support is selected. Original surviving
gates belong to the fixed remainder.

The derived requests are disjoint because a physical gate has one origin and
the validated input has unique event identities. The existing
[physical ownership kernel](lean_residual_terminal_physical_ownership.md)
therefore cannot hide overlap by assigning a gate to an arbitrary first
requester. Every allocated live position has an owner in the actual raw input.

The existing kernel is then reused to establish support restriction, exact
extracted piece sizes, the sum of those sizes, independent open-boundary
semantics and induced-boundary reconnection. Smaller supports do not reassign
owners, and duplicate support records do not create duplicate charges.

Historical charged size and surviving owned size deliberately differ. For
example, restoring a gate and later removing it records one historical
allocation but zero surviving gates for that event. Two restoration events
receive distinct allocation labels even when their Boolean functions coincide.

## Source and verification boundaries

The implementation is split across:

- [physical normalization origins](../lean/PNP/NANDPhysicalGateProvenance.lean);
- [complete history ownership](../lean/PNP/NANDWireHistoryPhysicalOwnership.lean);
- [literal compiler-position inverse](../lean/PNP/NANDCompiledGateProvenance.lean);
- [ambient compilation ownership](../lean/PNP/NANDWireHistoryAmbientOwnership.lean);
- [derived requests and extracted charges](../lean/PNP/NANDWireHistoryOwnershipCharges.lean).

`compileOwned_result` proves that dropping the ownership evidence returns
exactly the existing arbitrary-support constructor's result. Ownership changes
neither the accepted input language nor the returned implementation.
`OwnedCompilation.semantics` preserves the original candidate's outputs.

The general Lean theorems cover arbitrary finite dimensions. Regression
fixtures exercise actual reordering, independent allocations, deletion of
original and allocated gates, empty dimensions, invalid event identities and
unfinished histories. They are tests of the implementation, not substitutes for
the general theorem.

The [source and hostile contracts](../audits/lean-source-derived-history-ownership0.test.mjs)
reject supplied ownership, arbitrary permutations, erased historical charges,
hidden premises and weakened conservation statements. Compiled type and axiom
audits remain the mathematical authority.

## What remains open

This result covers the existing computational history language. It does not
construct a globally successful history or complete the manuscript's carrier
and profile universe, all R1-R9 or N1-N10 routes, matched-kappa arbitrary-support
Pull/Expand, composed full-profile Package E, terminal-derived families or global
route coverage. It does not establish unconditional SaturatePositive,
BCELReady or ZeroSlack.

No complete encoded-input polynomial runtime or output/certificate-size theorem
is claimed. Physical identity and integer accounting do not prove such a bound.
The historical and surviving size identities must not be interpreted as runtime
estimates or as credit for an unconditional proof checkpoint.

Maintain progress only through the fixed
[proof-progress ledger](../status/PROOF_PROGRESS.json); additional evidence rows
are formal artefact coverage, not a proof-completion percentage.

## Reviewed publication boundary

As of `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-16-266`:

For arbitrary finite computational carriers, selected support lists and raw-event dimensions, physical origins follow the actual constant, sharing and cone compiler branches and compose through the existing normalization trace. Every initial gate retains its source coordinate; every R7/R8 appended gate is labelled by its executing event identity and local allocation coordinate. Creation, cancellation and reads allocate no gates. The complete closed history computes a duplicate-free partition of live and removed origins into original gates and all historical charges, including allocations later removed. The actual topological compiler's computed two-sided position inverse carries those labels into the literal ambient splice, with every exterior gate present once and extracted coordinates restored to ambient positions. A source-only ownership constructor returns exactly the existing constructor's result. Its disjoint raw-event requests and fixed original-gate remainder reuse the existing ownership kernel for support-stable membership, actual extracted piece sizes and charge identities, independent open semantics and induced-boundary reconnection. No owner family, provenance map, partition proof, charge amount, topological order or successful-splice certificate is supplied.

This is source-derived physical ownership for the existing computational history language, not the complete manuscript carrier/profile universe, all R1-R9 or N1-N10 routes, arbitrary observers, matched-kappa arbitrary-support Pull/Expand or complete Package E. Support coordinates and raw events remain input data; no terminal-derived family or globally successful history is constructed. Historical allocated size and surviving owned size are distinct, and physical identity or integer accounting does not prove a runtime bound. Global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and complete encoded-input polynomial runtime, output and certificate bounds remain open. Finite runtime fixtures are regression evidence, not proof authority. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

Formal artefact coverage: 242 of 244 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

Publication decision: defer. This connects source-derived ownership to the existing computational accounting route, but does not close a fixed weighted checkpoint or global gate or change the published global bottom line. Preserve the coherent M264 website pin and batch M265 and M266 into the next major publication.

The [explicit-root axiom audit](../lean-audit/PNPSourceDerivedHistoryOwnershipAxiomAudit.lean)
and [compiled publication contracts](../audits/lean-source-derived-history-ownership-publication0.test.mjs)
pin the reviewed declarations, types, dependency closures and limitations. Run
`npm run audit:m266` after the compiled inventory and current generated status are synchronized.

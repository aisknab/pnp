# Persistent ownership through descendant histories

M267 carries source-derived physical ownership through an arbitrary finite sequence of raw computational histories. Each stage decodes against the actual preceding descendant; initial gate identities persist, and fresh allocations use stage, event and local-gate coordinates. The complete-program theorem preserves outputs and an exact duplicate-free live/removed/charged partition, retaining every historical allocation after later deletion. Derived owners remain fixed under support restriction. A computed final gain may follow temporarily expanding stages; a failed later stage rejects the whole program. No intermediate implementation, owner map, rank, successful-history certificate or semantic oracle is supplied.

The dependency anchor is section 4 ChargeSoundness and section 6.1 R9 integer accounting in the [pinned manuscript](../archive/legacy-v0/ARCHIVE.json). This closes the persistence edge after [single-history physical ownership](lean_source_derived_history_ownership.md); it is not a proof of full manuscript ChargeSoundness.

## Input and acceptance boundary

`PNP.DirectWire.WireDescendantHistory.compile` receives the original implementation and a finite list of raw stages. Each stage contains support records, a profile width and raw computational events. All dimensions, stage counts and event-list lengths are arbitrary finite data. Decoder theorems preserve the exact accepted coordinates, actions, identities and predecessor lists.

Compilation traverses the whole list. Every next stage uses the actual preceding result, reusing the existing local history and literal ambient splice. Invalid coordinates, an inadmissible local history or a failed later stage return no complete result. A successful prefix is never substituted for a failed complete program. The local history language is unchanged, and each stage must finish its own obligations; open obligations are not carried across supports.

## Persistent identity and exact accounting

Initial gates keep their original source coordinate. New gates receive the computed stage position, executing event identity and local allocation coordinate. Reusing a local event number at another stage therefore cannot alias a previous allocation. Stage positions come from traversal, not caller-supplied freshness evidence.

Each local original coordinate is relabelled through the previous physical-position map. The next map follows the same literal compiler positions as the actual implementation. A count-preserving arbitrary permutation is not enough.

The ledger records live origins in actual final physical order, every historical allocation, and every removed origin. Its arbitrary-program theorem is:

```text
live ++ removed  ~  original source gates ++ charged
```

The left side is duplicate-free. The three ledger lengths equal the actual final gate count and the sums of the existing executions' charge and removal counts. The execution counts are not defined as the ledger lengths. Deleting an earlier allocation preserves its historical charge and records its removal exactly once.

## Derived owners and final gain

Accepted raw stage/event keys form a duplicate-free family. Every historical allocation and every surviving allocated gate traces to an actual key. The final owner requests are derived before selecting a result support; their disjointness and the original-gate remainder are proved rather than supplied. The existing ownership kernel then provides support restriction, exact extracted piece sizes and charges, independent open semantics and induced-boundary reconnection.

`compileGain` first compiles the complete program and then compares final size with original size. Structural Boolean semantics construct the existing `StrictEquivalentGain`, whose residual-descent theorem is reused. Intermediate stages may expand or fail to decrease. No exhaustive equivalence test or reference-minimum search provides the adapter's proof authority.

A guarded regression starts with five gates, grows to six and seven, then ends with four. It retains both historical allocation charges and all three removed identities. These fixed computations exercise the implementation; the arbitrary-program Lean theorems, not the fixtures, establish the general result.

## Source and verification boundaries

| Module | Boundary |
| --- | --- |
| [Raw input](../lean/PNP/NANDWireDescendantInput.lean) | Source-preserving bounded decoding |
| [One stage](../lean/PNP/NANDWireDescendantStage.lean) | Actual local compilation and inherited semantics |
| [Complete run](../lean/PNP/NANDWireDescendantRun.lean) | Whole-list execution and rejection propagation |
| [Persistent ledger](../lean/PNP/NANDWireDescendantLedger.lean) | Literal coordinate lifting and historical conservation |
| [Arbitrary-program ownership](../lean/PNP/NANDWireDescendantOwnership.lean) | Exact execution totals and duplicate-free partition |
| [Raw event provenance](../lean/PNP/NANDWireDescendantEvents.lean) | Stage-qualified input keys and allocation completeness |
| [Owned pieces](../lean/PNP/NANDWireDescendantCharges.lean) | Disjoint, support-stable extraction and exact charges |
| [Final gain](../lean/PNP/NANDWireDescendantGain.lean) | Complete-program semantics and final-size acceptance |

The [source and hostile contracts](../audits/lean-descendant-history-ownership0.test.mjs) reject supplied ownership, omitted charges or removals, ambiguous event keys, partial-prefix success and weakened theorem statements. The [explicit-root audit](../lean-audit/PNPDescendantHistoryOwnershipAxiomAudit.lean) and [compiled publication contracts](../audits/lean-descendant-history-ownership-publication0.test.mjs) bind the reviewed theorem family to its exact compiled types and axiom closures. Run `npm run audit:m267` after the root, inventory and generated status are synchronized. Reuse unchanged component evidence instead of rebuilding the proof in the website repository.

## Reviewed publication boundary

As of `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-16-267`:

For arbitrary finite source dimensions and raw stage/event lists, a source-only decoder and compiler traverse the complete list using each actual preceding descendant. Persistent physical origins relabel original positions through the existing literal ambient compiler and label allocations by computed stage position, executing raw event and local gate. The arbitrary-program theorem conserves original gates and every historical charge as a duplicate-free live/removed permutation with exact actual execution totals; later removal never erases an earlier charge. Accepted input-event keys are distinct across stages, even when local event numbers are reused, and every historical or surviving allocation traces to that raw family. Derived final owner requests are disjoint before support selection and reuse the existing extraction kernel for support-stable ownership, exact piece sizes and charges, open semantics and induced reconnection. Whole-program Boolean semantics and physical size accounting yield an optional final StrictEquivalentGain through a computed final-size comparison, permitting intermediate expansion and propagating every rejected stage. No intermediate implementation, owner family, provenance map, charge amount, rank, successful-history certificate or semantic oracle is supplied.

This covers arbitrary finite sequences of the existing closed computational-history compilations, not the full manuscript carrier/profile universe, cross-support transport of open obligations, all R1-R9 or N1-N10 rules, matched-kappa arbitrary-support Pull/Expand, proper-support VerifyDW, full ChargeSoundness or complete Package E. Raw supports and events remain inputs; no terminal-derived family or globally successful strategy is constructed. Final net gain does not require each stage to decrease, prove local minimality after rejection, bound temporary growth or establish encoded-input polynomial runtime. Global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and complete polynomial runtime, output and certificate bounds remain open. Runtime fixtures are regression evidence, not theorem authority. No fixed weighted checkpoint or global gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

Formal artefact coverage: 243 of 245 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

Publication decision: defer. Persistent descendant ownership advances the existing computational accounting route without closing a fixed weighted checkpoint or global gate or changing the published global bottom line. Preserve the coherent M264 website pin and batch M265 through M267 into the next major publication.

The [fixed progress ledger](../status/PROOF_PROGRESS.json) is authoritative. This added evidence row does not award a fixed weighted checkpoint. The estimate is neither confidence in the route nor a time estimate.

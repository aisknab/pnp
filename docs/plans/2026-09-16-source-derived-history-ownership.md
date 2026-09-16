# M266: source-derived physical ownership through computational histories

## Manuscript anchor and selected dependency

Reconstruct section 4 ChargeSoundness and section 6.1 R9 integer incidence
accounting of the manuscript pinned by
[the archive manifest](../../archive/legacy-v0/ARCHIVE.json).
The bounded target is a source-derived physical ownership ledger for the complete
existing computational R5/R6/R7/R8 history and its literal ambient splice.

The development parent is the actual M265 merge
`092fd5c820ca42a4efd6826e6fa7c467cfd179bb`, tree
`3677bccafc8b359f87ebadd516b16477c1d155cd`.
The parent's required post-merge checks and exact-object reproduction have
passed. M266 remains unearned until its own complete release gates pass.

M241 already partitions physical gates from a supplied raw request family.
Reuse that partition kernel; do not publish it again as new work. M265 computes
actual materializer charges and normalization removals, but its scalar balance
does not name each surviving or deleted physical gate's allocation. Close that
missing edge from actual transformations to unique computational-charge owners.

## Unbounded construction

All input, output, field, gate, support and event dimensions remain arbitrary.

1. Recover retained original gate coordinates from each existing constant
   propagation, structural-sharing and output-cone pass. Follow actual append,
   elimination, reuse and extraction decisions. Preserve the existing algorithms,
   semantics and public theorem statements.
2. Prove exact retained-position correspondence, injectivity and the complement
   of removed gates. A numerical injection justified only by the output size is
   not physical provenance. A sharing alias can be many-to-one; the physical
   retained-origin map must name the actual emitted representative.
3. Compose these maps through the existing strict normalization trace, preserving
   old allocation labels for surviving gates and recording each removal once.
4. Give an initial physical gate its source coordinate. Give each physically
   appended R7 or R8 materializer gate the pair of its executing event identity
   and its local allocation coordinate. The originating snapshot/creation is
   retained as causal metadata, not reused as a fresh physical allocation ID.
5. Carry this ledger through the actual execution. R5 creation, R6 cancellation
   and full reads do not mint NAND gates. R7/R8 mint precisely their actual
   appended materializer gates. Normalization may remove original or previously
   charged gates, but cannot erase their historical charges.
6. Transport the final live labels through the actual topological compiler into
   the literal ambient splice. Retain every exterior gate exactly once, map
   extracted source coordinates back to their ambient gate coordinates, and
   preserve the distinct event-owned materializer allocations.

Do not accept a caller-supplied owner family, provenance map, partition proof,
charge amount, topological order or successful-splice certificate. Do not assign
owners by arbitrary first-requester selection to hide overlapping live owners.
The existing raw-event and source input boundary remains unchanged.

## Intended exact interfaces

Introduce a tagged physical-origin type with original-gate and event-allocation
constructors. The following is the intended general history theorem shape, using
new computed `sourcePhysicalOrigins` and `physicalOwnership` definitions:

```lean
theorem ClosedHistory.physical_ownership
    {inputs outputs fields : Nat}
    {source : WireCarrier inputs outputs fields}
    {raw : List (RawEvent fields)}
    (history : ClosedHistory source raw) :
    let ledger := history.physicalOwnership
    ledger.live.length = history.state.current.implementation.gateCount ∧
    ledger.charged.length = history.execution.charged ∧
    ledger.removed.length = history.execution.removed ∧
    (ledger.live ++ ledger.removed).Nodup ∧
    (ledger.live ++ ledger.removed).Perm
      (sourcePhysicalOrigins source ++ ledger.charged)
```

The computation must additionally expose the actual gate-position origin trace,
not just prove these list/count conditions. Each pass's trace is bound to its
literal compiler branches and actual retained gates. The final ambient theorem
must bind labels to the computed splice's physical gate positions and establish
the same partition with every original ambient gate included exactly once.

Derive owner membership, disjointness, support restriction and actual extracted
piece charges from this construction and the existing ownership kernel. The
historical charged sum and the surviving owned materializer size are distinct:
normalization can remove a charged gate. Do not conflate them.

A failure to prove source-bound provenance stops this target. Do not substitute
a smaller history language, an arbitrary count-preserving permutation, another
finite example, or a supplied correctness field.

## Verification and expectation matrix

| Changed boundary | Reconcile first | Rejecting evidence |
| --- | --- | --- |
| Actual normalization retention maps | Existing pass interfaces and independently reviewed branch behavior | General Lean types, source-shape contracts and exact retained-coordinate fixtures |
| Normalization trace provenance | Old labels, removed complement, exact correspondence and count identity | Arbitrary trace theorem; interactions of all three passes |
| Event allocations and ownership | R5/R6/read mint nothing; R7/R8 exact append ranges; unique executed IDs | Complete history theorem, multi-materializer and later-deletion cases |
| Literal ambient splice | Original support-coordinate map, one exterior copy and actual compiler positions | Arbitrary-support theorem; interleaved exterior/support fixture |
| Existing consumers | Every changed module's closed declarations, source contracts and type pins | Focused consumer checks before broad suites |
| Publication plumbing | Root imports, reviewed Lean/JavaScript names, milestone/type fingerprints, status, progress and docs | Name-set preflight, one refreshed root/inventory, then generated check mode |
| Durable verification | Read-only workflow, package-script fixture and workflow size headroom | Literal changed shell blocks, focused package/surface tests |

Use positive and hostile examples for empty dimensions, repeated field values,
overlapping source ancestry, independent materializer events, sharing aliases,
constant deletion, cone pruning, removed charged gates, stale/reused event IDs
and arbitrary-support reordering. Finite computations are regression evidence,
not the authority for the general theorem.

All processing runs on the configured builder. Reuse the exact-source,
exact-toolchain cache for changed dependency targets. Add tests with the source;
do not knowingly run against obsolete expectations. Run affected small checks,
then the refreshed root and axiom evidence, generated artefacts, the deduplicated
full core suite, normal PR/post-merge CI, and the exact-object reproduction.
Do not rerun unchanged Lean or report work for a deferred website publication.

## Claim boundary and publication

This supplies unique physical allocation/ownership for the existing computational
history route, not the complete manuscript carrier/profile universe, all R1-R9
or N1-N10, matched-kappa arbitrary-support Pull/Expand, composed full-profile
Package E, terminal-derived families, complete global routing, unconditional
SaturatePositive, BCELReady or ZeroSlack. It does not construct a globally
successful history or prove complete encoded polynomial runtime or size bounds.

No fixed weighted checkpoint is expected to change. Formal artefact coverage:
241 of 243 current scoped publication rows earned at the M265 parent.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5. This plan earns no new row or score.

Publication decision: defer a separate PNPLabs cycle unless the completed proof
changes a load-bearing checkpoint or public bottom line beyond this stated
scope. Keep the coherent M264 public pin. Notify genuine verified substeps and
the earned merged core milestone independently of website cadence.

## Root and release integration preflight

The compiled leaf proofs and focused ownership contracts are complete. The
milestone remains unearned until root, inventory, publication and release checks
establish the same source-bound result.

| Producer | Consumers reconciled before checking | Rejecting check |
| --- | --- | --- |
| Root ownership import | Root import closure and all new module imports | Root source audit before the inventory probe |
| Reviewed theorem set | Lean inventory producer, JavaScript required names, root axiom audit, publication row and fingerprint keys | Exact name-set comparison; hashes only from compiled output |
| Shared axiom transcript check | Existing history workflow and its preflight, new helper regressions, verifier list and workflow triggers | Missing/extra declarations, altered closures, wrong kinds and stray-output mutations |
| New milestone command | Package script and the closed public-surface script fixture | Independent package preflight before sealed-status tests |
| New release claims | Status fields, publication map, progress, report and current documentation | Source-bound positive and hostile publication contracts |

The workflow is close to its enforced review-size budget. Move its existing
inventory-bound axiom comparison into a small permanent read-only helper,
preserving exact declaration and axiom matching, warning failures and regression
commands. The helper must not run another root build. Retain the current
workflow budget and run shell-syntax, trigger and size checks before compilation.

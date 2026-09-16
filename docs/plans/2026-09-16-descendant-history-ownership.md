# M267: persistent ownership through descendant computational histories

## Manuscript anchor and missing dependency

Reconstruct the descendant charge universe and unique ownership of section 4,
ChargeSoundness, and the integer accounting of section 6.1, R9, in the manuscript
pinned by [the archive manifest](../../archive/legacy-v0/ARCHIVE.json).

The development parent is the M266 merge
`aaa65c1a5f58fa181f95f7d6f9430c0c738039aa`, tree
`2c725f2e2a97791f7e37ec51790b5145d6d6ed81`.
Its tree is identical to the feature tree that passed every PR check and the
independent exact-head reproduction. At the start of this work, its final
post-merge audit and exact-merge release reproduction remain separate pending
gates. Keep the M266 release checkout unchanged. Development here is isolated;
do not publish or merge this child milestone before the parent release gates pass.

M266 derives actual physical ownership through one complete existing
computational history and its literal ambient splice. Repeating that constructor
on a descendant starts with that descendant's physical gate coordinates, and
event identities are unique only within its local raw list. The missing edge is
a persistent, source-derived ownership record across an arbitrary finite sequence
of such actual compilations, without reclassifying old allocations as new original
gates or colliding when a later stage reuses a local event identity.

The finite dependency path is: existing physical/compiler provenance, then
persistent descendant ownership and exact cumulative accounting, then the
computational charge-certificate boundary needed by manuscript ChargeSoundness.
Complete carrier/profile semantics and cross-support obligation transport remain
additional obligations. This milestone must not be presented as all of
ChargeSoundness, the full manuscript calculus or a global gain-producing strategy.

## Unbounded construction and public input boundary

The original input, output and gate dimensions, every selected support and local
field dimension, the number of stages and the lengths of all event lists are
arbitrary finite data.

1. Introduce raw stage data containing finite support coordinates, a profile
   coordinate width and raw computational events. Decode support and field
   coordinates against the actual current descendant and its actual extracted
   interface. Preserve every successfully decoded coordinate, identity,
   predecessor list and action; reject out-of-range coordinates.
2. Reuse the existing history constructor and literal ambient compilation.
   The public program input must not contain intermediate implementations,
   semantic truth tables, owner maps, allocations, proof terms, successful-history
   evidence, a supplied order/rank or a function oracle.
3. Give initial physical gates their initial source coordinates. Give a fresh
   allocation the computed stage position, its actual executing event identity
   and its local physical allocation coordinate. The stage position is computed
   from the input-list traversal, not supplied as freshness authority.
4. Relabel every local original coordinate through the previous physical-position
   origin map. Follow the actual M266 compiler-position map for the new result.
   Preserve the unchanged exterior and all surviving old allocation identities.
   A count-preserving permutation is not a substitute for this correspondence.
5. Accumulate every actual historical allocation and removal. An allocation
   removed in a later stage remains in the charged history and is removed once.
   Repeated event numbers in different stages must not identify the same charge.
6. Prove exact conservation and semantic preservation over the whole accepted
   program. A malformed or inadmissible stage rejects the program; it must not
   silently drop that stage, return an accepted prefix or forge a final receipt.
7. Derive the final raw-event owner family before selecting a result support,
   then reuse the existing physical ownership/extraction kernel for disjointness,
   support-stable assignment and exact surviving piece charges.
8. Add a net-gain adapter only from the computed complete program: compare its
   final physical size with the original, and construct the existing
   `StrictEquivalentGain` using structural semantic preservation. Reuse its
   residual-descent theorem; do not execute exhaustive equivalence or minimum
   search to supply proof authority.

Intermediate stages may be nondecreasing or temporarily expanding. Do not
replace this target with a sequence in which every stage is required to be a
strict gain. The optional acceptance of the final net-gain adapter is distinct
from successful execution and ownership of the entire program.

The existing local-history language remains unchanged, including its rejection
of duplicate local identities, missing references, invalid lifecycle operations
and unfinished final ledgers. Each ambient compilation still uses a closed local
history. Do not claim open obligations are transported between those stages.

## Intended exact theorem boundary

Use a computed origin type with initial-gate and stage/event/allocation
constructors. The source-only entry point has the following intended shape:

```lean
def compile
    (source : Implementation inputs outputs)
    (stages : List RawStage) :
    Option (CompiledRun source stages)
```

The result and all receipts are produced by this function. The principal
arbitrary-dimension theorem has the shape:

```lean
theorem CompiledRun.physical_ownership
    (run : CompiledRun source stages) :
    let ledger := run.ledger
    ledger.live.length = run.result.gateCount ∧
      ledger.charged.length = run.chargedCount ∧
      ledger.removed.length = run.removedCount ∧
      (ledger.live ++ ledger.removed).Nodup ∧
      (ledger.live ++ ledger.removed).Perm
        (originalOrigins source.gateCount ++ ledger.charged)
```

Here `chargedCount` and `removedCount` must be the sums of the actual existing
stage executions' charges and removals. They must not merely be defined as the
new lists' lengths to make the theorem tautological. The physical-position
map must have separate original and fresh-allocation correspondence theorems
tied to the exact stage compiler.

Also establish:

- complete-program Boolean output preservation for every input valuation;
- the exact global physical size equation;
- every allocation's membership in the actual raw stage and event;
- globally disjoint owner requests and support-stable final ownership;
- decoder round-trip and exact source-coordinate preservation for arbitrary lists;
- rejection propagation and unchanged accepted local-history semantics;
- soundness of the final net-gain adapter via the existing `StrictEquivalentGain`.

Reuse `StrictEquivalentGain.strictResidualDescent` and the existing
`StrictGainChain` theory as downstream facts. A composition wrapper or a repeated
scalar chain inequality is not new milestone evidence. A failed general
provenance proof stops the milestone; do not substitute a fixed two-stage example,
caller-supplied correctness, a smaller history language or an added assumption.

## Producer, consumer and verification matrix

| Boundary | Reconcile with the source | Smallest rejecting evidence |
| --- | --- | --- |
| Raw records and actions | Complete constructor sets, coordinate bounds, exact identity/action preservation | General round-trips and malformed-coordinate regressions |
| Actual stage execution | Current descendant dimensions, existing raw-history rejection and literal result | Source-only constructor contract; decoder/compile correspondence |
| Persistent origins | Actual original-position relabelling and fresh stage/event/local identity | General stage and arbitrary-program provenance theorems |
| Historical accounting | Old allocations retained after later removal, actual execution totals | Conservation permutation, duplicate-freedom and exact size identity |
| Owner restrictions | Actual input-event membership and unchanged extraction kernel | General disjointness/support laws and overlapping-support fixtures |
| Net-gain adapter | Whole-program semantics and final size comparison only | Expanding intermediate stage; accepted and rejected final gain cases |
| Existing interfaces | Paths and declarations in every affected source, audit and Lean regression | Positive/hostile consumer checks before sealing |
| Root and publication | Root imports, reviewed name sets, explicit audit, milestone and fingerprints | Source/name-set preflight before compiled inventory generation |
| Package/workflow | Closed script fixture, existing trigger families, exact shell bodies and size budget | Focused package, shell syntax, trigger and workflow-size checks |
| Generated status/report | Actual compiled counts and hashes, unchanged weighted checkpoints | Generated check mode and hostile publication/progress contracts |

Keep old executable definitions and theorem statements unchanged when new
modules can compose their existing public interfaces. If an existing module is
edited, inspect its complete consumer family and update expectations with the
producer before testing.

Runtime fixtures should cover empty programs and dimensions, changing gate and
field bounds, repeated/reordered supports, reused local event identities across
stages, multiple allocations, old and new allocations removed later, retained
exterior gates, compiler reordering, temporary expansion, invalid later stages,
unfinished local histories and absence of final gain. Fixed fixtures are
regression evidence, not the authority for the arbitrary-program theorem.

Run all processing on the configured builder. Seed the isolated cache only after
the source tree and toolchain match exactly. Run changed targets and focused
contracts first; rebuild the changed dependency chain before imported audits.
Prepare theorem/type and axiom expectations with the source. Refresh root and
inventory once source stabilizes, derive hashes from compiled output, then
synchronize generated consumers before the deduplicated full suite.
Retain every required PR, post-merge and exact-object release boundary.

## Remaining proof burden and progress

This is ownership and accounting for sequences of the existing closed
computational-history compilations. It does not establish the full manuscript
carrier/profile universe, open-obligation transport across supports, all R1-R9
or N1-N10 rules, matched-kappa Pull/Expand, complete Package E, proper-support
VerifyDW, terminal-derived families or globally successful route selection.

Whole-circuit equivalence and net size reduction alone do not prove the
manuscript's proper-support compatibility conditions. A successful final gain
does not make every stage decreasing, bound temporary materialization or prove
an encoded-input polynomial runtime. No global minimality follows from a failed
program or gain check.

Unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin,
complete polynomial runtime/output/certificate bounds, deterministic CNFSAT in P
and the eligible root remain open.

Baseline at the M266 source coordinate: formal artefact coverage is 242 of 244
current scoped publication rows earned. Risk-weighted proof completion estimate:
40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5. This plan awards
no new milestone row or fixed checkpoint credit.

Publication decision: defer a separate PNPLabs cycle unless the completed result
changes a fixed checkpoint or materially changes the public bottom line beyond
this scope. Preserve the coherent M264 website source pin and batch pending
earned milestones when a major publication is warranted. Notify verified
mathematical substeps independently of website cadence.

## Parent release closure

The M266 merge above passed all four normal post-merge checks and its fresh
exact-merge source, archive-pin, publication and release-seal reproduction on
2026-09-16. Its tree matched the verified feature tree, so the unchanged proof,
unit and report evidence was reused. The parent release gate is now complete;
M267 remains an unearned development milestone until its full target and own
release checks pass.

## Mathematical implementation checkpoint

The eight new descendant-history modules and their targeted Lean regressions
compile. Their printed theorem closures contain only `propext` and `Quot.sound`
where required, with no project-specific axioms or classical choice.

- Raw input decoding preserves coordinates, actions and event identities;
  each stage uses the actual preceding descendant and existing compiler.
- The arbitrary-program ownership theorem conserves original and allocated
  identities with exact actual execution totals and persistent removed history.
- Every allocation traces to a raw stage/event key. Derived final owners are
  disjoint and support-independent; existing extraction semantics and charge
  identities apply without a supplied owner family or piece weights.
- The final net-gain adapter uses structural semantics and a final size check.
  A regression grows from five to six to seven gates before ending with four,
  retaining both allocation charges and all three removed identities.

These targeted results are not a completed release. Source and publication
hostile contracts, the explicit-root audit, inventory and generated status,
full validation, normal CI and exact-merge reproduction still remain.

## Compiled integration checkpoint

The explicit root and 84 reviewed theorem closures are checked. The compiled inventory preserves every earlier theorem type pin; the new map seal binds this source closure and exact theorem types. The inventory grew past the previous 64 MiB output buffer, so the bounded exporter now permits 128 MiB and retains its process diagnostic when stderr is empty. Reconcile both the inventory regression and root/workflow contract with that reviewed limit. The mathematical source and theorem statements are unchanged by this transport correction.

Status, package and publication-test contracts, fixed-score history, current documentation and compact CI are being integrated. Full hostile validation, report reproduction, normal CI and exact-merge reproduction remain release gates; this is not a merged milestone.

Formal artefact coverage: 243 of 245 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

Publication decision: defer. Persistent descendant ownership advances the existing computational accounting route without closing a fixed weighted checkpoint or global gate or changing the published global bottom line. Preserve the coherent M264 website pin and batch M265 through M267 into the next major publication.

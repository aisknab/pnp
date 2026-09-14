# M260: source-bounded ordered physical boundary extraction

## Dependency and manuscript anchor

The pinned canonical manuscript's Sections 2 and 3 define the incoming physical
boundary of a selected support by actual gate-source crossings. Its PCCMin
construction requires those supports and their ports to be computed. M258
constructs a polynomially bounded proper zero/unary candidate family and M259
iterates proper and whole-span gains, but their underlying boundary extractor
still enumerates every declared primary-input position, including unused inputs.

Close this specific implementation dependency by computing the exact ordered
physical boundary from gate-source occurrences. Preserve the manuscript's
primary-input-before-gate-output ordering and every ambient coordinate.
This is an implementation refinement of the existing physical construction,
not a change to the manuscript route or a substitute for its global obligations.

The specification remains the immutable document tag
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`. The manuscript is
specification evidence, not theorem authority.

## General target and exact interfaces

For arbitrary `inputs gates outputs profileWidth : Nat`, an actual
`program : Program inputs gates` and any finite list
`records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)`:

1. Enumerate only the nonconstant sources of actual gates. The occurrence list
   has length at most `2 * gates`, independent of unused declared input slots.
2. Filter for the existing physical crossing predicate, remove duplicates and
   sort by the existing canonical coordinate order.
3. Prove the exact list equality, not merely set equivalence:

```lean
terminalBoundaryPortsSourceDriven program records =
  (allTerminalSupportWires inputs gates).filter
    (terminalBoundaryWire program records)
```

4. Make the active `terminalBoundaryPorts` execute the source-driven construction.
   Retain a public reference-equivalence theorem so existing proofs can use the
   old specification without executing its ambient-input enumeration.
5. Prove membership completeness, no duplicate ports, canonical ordering and

```lean
(terminalBoundaryPorts program records).length <= 2 * gates
```

6. Prove order-preserving compatibility of physical completion and extraction
   against the reference list where downstream dependent interfaces need it.
   Rebuild affected dependency chains and the explicit root before imported
   regressions or compiled axiom audits.

The old enumeration is a theorem-side reference only. Runtime fixtures for a
large declared-input dimension must use the source-driven path and bounded
valuations, never enumerate all assignments or execute the old reference there.
There must be no caller-supplied list, completeness certificate, rank map, proof
axiom, unchecked implementation override, native proof authority or weakened
support-compatibility premise.

## Implementation boundary

Prefer a small addition to the existing physical support implementation and
focused proof adaptations over a broad module refactor. A generic canonical-list
helper is acceptable only if it directly serves the active extraction path.
Preserve existing theorem types and source-exact coordinate semantics.
Reconcile every source-shape contract that intentionally names the reference
implementation before running it. Protect the replacement executable definition,
the reference-equality theorem and its integration with independent hostile tests.

The occurrence and output bounds are structural size bounds. They do not assert
total encoded-input-size polynomial runtime for PCCMin, selectors, certificates,
profile families, dependency tables, saturation or the complete route.

## Verification order and evidence reuse

1. Record this plan before implementation in an isolated checkout of the fully
   core-verified M259 tree. Preserve that queued result and the M253-M258 release.
2. Compile bounded general-list/source/boundary theorem prefixes first, with a
   focused axiom closure probe before the downstream root rebuild.
3. Add guarded runtime regressions for empty programs, constants, duplicate
   sources, nonconsecutive selected gates, crossing producer gates, mixed primary
   and gate ports, canonical order, and very large unused declared-input width.
   Compare exact reference lists only on small fixtures.
4. Reconcile affected source contracts and explicit-import expectations before
   the targeted suite. Preserve the prior negative contracts and add mutations
   for omitted ports, duplicates, reordered ports and fallback ambient scans.
5. Rebuild changed dependency targets and the explicit root, then run exact
   declaration-type, axiom and bounded runtime checks from the compiled root.
6. Freeze source, generate inventory/status/publication/progress mirrors, derive
   all changed fields and update current documentation and exact expectations.
7. Run focused compiled/hostile/publication checks, documentation links and the
   deterministic report, followed by one deduplicated complete core test union.
8. Follow normal draft PR, all-checks, manual-merge, post-merge and exact-object
   independent reproduction gates. Reuse unchanged successful evidence only
   across the same source, inputs, toolchain and assertion boundary.

All processing runs on the configured remote builder. Temporary checkouts,
transport patches, helpers and logs remain only while needed for this cycle and
are removed at the recorded release/diagnosis cleanup point.

## Remaining obligations and progress policy

This closes unused-input enumeration in one concrete physical boundary
construction. It does not close the full manuscript carrier and obligation
calculus, all normalization rules, Package E, global routing, unconditional
SaturatePositive, BCELReady or ZeroSlack, exact polynomial PCCMin, deterministic
SAT or the eligible root theorem. Whole-span and proper support semantics remain
distinct. The proven zero/unary fixed point may still be nonminimal globally.

No fixed risk-weighted checkpoint or global gate is proposed to change.
Risk-weighted proof completion remains 40%, with uncertainty 20% to 40%;
global gates remain 0 of 5. Formal artefact coverage may increase only after this
general theorem and its required publication contracts are earned.

Publication decision: defer a separate PNPLabs cycle for M260. The already planned
M258 major batch remains independent; this bounded implementation refinement
alone does not alter the public mathematical bottom line.

## Inherited standard-axiom review

The initial library-sort candidate added standard Quot.sound dependencies to
28 inherited reviewed interfaces. After the structural ordering repair, the
complete compiled inventory comparison against the exact M259 merge finds only
five such changes. The other 23 retain their original propext-only closures,
including supportChoice_wire_mem. Every inherited reviewed kernel type,
defining module and publication fingerprint is unchanged.

The current inventory, status, exact workflow and module expectations are derived
from that repaired compiled evidence. The regression retains all 28 reviewed
interfaces and their exact current axiom lists, including the 23 restored
closures. Immutable historical coordinates are not rewritten. Standard Lean
quotient soundness was already within the audited foundational allowlist; no
earned row is revoked, project axiom or Classical.choice is introduced, or fixed
proof-progress checkpoint or global gate changes.

## Kernel-reducible source ordering repair

The inherited regression review exposed a distinction between executable and
kernel reduction. The imported library sort computes the correct boundary at
runtime, and its equations prove the same result, but direct kernel reduction
stops even on a two-element list. Changing ordinary decide to decide +kernel
repaired only some fixtures and did not repair dependent-width conversion.

The integrated correction uses structural insertion and sorting of the actual
finite source list. General permutation and ordering proofs re-establish the
same nine canonical-list interfaces with no added premise: exact ordered
reference equality for injective coordinate keys, membership, distinctness and
the source-length bound. It does not enumerate ambient inputs, use a supplied
certificate, change the manuscript route or introduce native proof authority.
The isolated complete proof and direct kernel fixtures passed; reference equality
and ordering use only propext and Quot.sound, and the length bound uses propext.

The superseded tactic-only edits to 26 inherited Lean fixtures are removed. Their
original propositions, expected values, valuation types and proofs are restored
byte-for-byte. The existing regression contract retains native-authority mutation
rejection. M260 adds direct kernel tests for a two-element sort, deduplication,
large unused input width and dependent valuation-width conversion.

Reconcile canonical-source shape, private helper names and hostile mutations
before verification. Rebuild the changed dependency chain and explicit root,
verify affected inherited regression commands, regenerate inventory, publication,
status and report identities, and derive changed expectations from those outputs.
The core input change requires new dependent evidence; independent unchanged
checks remain reusable. No fixed checkpoint, global gate, total-runtime claim or
website publication decision changes. Keep the same arbitrary-dimension theorem
targets, source-only construction and conservative M260 claim boundary.

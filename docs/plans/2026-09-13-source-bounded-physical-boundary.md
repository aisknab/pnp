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

The compiled inventory comparison found 28 previously reviewed interfaces whose
closures now also use Lean's standard Quot.sound dependency through canonical
sorting. Every inherited reviewed kernel type, defining module and publication
fingerprint is unchanged. No earned row is revoked, no project axiom returns and
no Classical.choice dependency is introduced in these interfaces.

The current inventory and status report this change explicitly. The M258 exact
expectation for supportChoice_wire_mem and its current module documentation are
updated from the compiled evidence; immutable historical coordinates are not
rewritten. M260 records all 28 exact transitions and unchanged fingerprints in
its hostile/compiled regression. Standard Lean quotient soundness was already
within the audited foundational allowlist, so this does not change a fixed
proof-progress checkpoint or global gate.

# M261: context-aware nested open-support and square transport

## Manuscript dependency and existing evidence

Reconstruct the computed boundary substitutions used by the support-square
transport of Sections 2.2 and 3 and the physical semantic comparison in Section
11.1, BN2-CoherentOptimum, of the manuscript pinned by
`archive/legacy-v0/ARCHIVE.json`.

Reuse the existing extraction, common-carrier optimum compatibility, local
coherence classifier and conditional side-tight completion. They are already
proved and must not be recreated as new milestones. Coordinate identity on the
ambient wire universe is distinct from substituting the value of a wire that
becomes internal in a larger support.

The existing classifier compares independently assigned ambient wire values.
Preserve its definition, theorem statements and hostile contracts. Do not call
its exact mismatch theorem false. This milestone must establish the physical
substitution relation on arbitrary open boundary assignments, then precisely
document how that relation differs from unconstrained ambient comparison.

Initial development used M260 tree
`42d00475e41e83b745347c3bb8c413526aa367a7`, commit
`80074c4798d1e465c200b9425ace8fa0ec1cabdf`. These are historical development
identifiers, not the final release authority. Current verification includes
the structural canonical-list repair while preserving the general transport
interfaces. Before publication, anchor the release on the actual verified M260
merge, not its feature tip or this historical development baseline.

Source-bound compiled and generated evidence may be prepared while the
prerequisite release checks run. After reanchoring, compare the exact source
inputs and toolchain before reusing that evidence; verify the new commit and
release binding separately. Do not regenerate unchanged proof outputs merely
because the same source acquired the correct merge parent.

## One general target, not a finite-prefix series

Let `candidate : Candidate inputs gates outputs`, with arbitrary dimensions,
and let `small`, `middle` and `large` be finite lists of terminal primitive
records. Gate inclusion is the ordinary mathematical condition

```lean
forall gate, terminalGateSelected small gate = true ->
  terminalGateSelected large gate = true
```

No caller supplies a boundary valuation map, transport certificate, replacement
correctness certificate, minimum, route-completeness premise or proof oracle.

Compute an open wire value from the larger support's existing open evaluator:
selected gates have their computed values; external wires use the actual
ordered boundary; constants remain literal constants. Restrict that computed
valuation to the smaller support's exact boundary. A boundary wire internalized
by the larger support must be evaluated there, not assigned independently.

The intended new interface is `terminalBoundaryPullback candidate small large`.
For every arbitrary valuation on the larger open boundary, prove

```lean
terminalOpenGateEvaluation candidate small
    (terminalBoundaryPullback candidate small large valuation) gate =
  terminalOpenGateEvaluation candidate large valuation gate
```

for every gate selected by `small`. Derive exact agreement at every retained
interface producer from this general selected-gate theorem.

For three nested supports, prove equality of the complete boundary valuation
functions:

```lean
terminalBoundaryPullback candidate small middle
    (terminalBoundaryPullback candidate middle large valuation) =
  terminalBoundaryPullback candidate small large valuation
```

Also prove the identity transport when the support is unchanged. The target is
arbitrary open boundary assignments, not only assignments obtained by executing
the original whole circuit. A failure of that general theorem stops the
milestone; do not substitute a whole-circuit-only theorem or a fixed example.

## Support-square and optimum integration

Derive the four leg maps from the actual computed support-square inclusions.
The two routes from join to meet must agree as valuation maps, not merely as
maps of coordinate names. Retain exact boundary/interface order, constants,
selected-source meanings and the empty-support cases.

Use the already-proved semantic equivalence of the full and quotient local
minimum realizers to transport their retained Boolean outputs along these
computed maps. The maps are derived from the original open carrier, not from
invented internal gates of a minimum realization. This is semantic comparison,
not a free materializer, a physical gluing of minimum circuits, or a claim of
shared charge ownership.

The complete milestone includes the general nested law and this four-corner
integration. Do not publish just one helper, a fixed transport leg, or a
finite counterexample as its completed theorem.

## Independent checks and claim boundaries

Prepare type, semantic and hostile expectations with the definitions. Include
empty and equal supports, retained primary inputs, a producer internalized by
the larger support, nonconsecutive gates, repeated consumers, and a genuine
two-path support square. Use small bounded executable fixtures only as tests;
the universal Lean theorems are the proof authority.

Where a small fixture separates unconstrained ambient comparison from physical
substitution, prove the distinction under the exact existing definitions.
Do not infer a global algorithmic counterexample or alter historical claims
from that observation. Reject a transport that reuses an independent value for
an internalized wire, reverses substitution order, omits a required boundary,
accepts a supplied correctness map, or asserts unrestricted full-profile
coherence.

This work does not derive the full manuscript profile/obligation dependency
system, preserve arbitrary implementation-dependent observers automatically,
glue four minimum circuits with coherent charge and obligation ownership, close
every global route, or prove unconditional SaturatePositive, BCELReady,
ZeroSlack, exact PCCMin, or complete encoded-size polynomial runtime, output or
certificate bounds. Reference minima remain specification/checked comparison
objects; no executable minimizer or runtime credit is inferred from them.

## Producer and consumer integration checklist

The mathematical source and explicit root are already verified. Reuse the frozen
Lean source evidence while completing these publication-boundary consumers.

| Producer | Consumers to reconcile in the same change | First rejecting check |
| --- | --- | --- |
| Nested and four-corner transport statements | Exact general-type regressions, source/hostile contracts and the root axiom transcript | Targeted source mutations; the compiled root, exact types and actual workflow block are already green |
| Reviewed theorem interface | Lean inventory name producer, JavaScript required-name set, publication row and fingerprint-key set | Exact name-set comparison and compiled type fingerprints before full inventory extraction |
| Publication claims and status fields | Publication map, reconstruction-status producer, generated outputs, focused status/claim/axiom/fingerprint mutations | Positive and hostile current-milestone cases after sealing |
| Package and test registration | package.json, CURRENT_PACKAGE_SCRIPTS0, conservative verifier and durable workflow | Independent package-field and package export/bin/script mutation tests before status-dependent surface checks |
| Current documentation and report | Status coordinate, progress history, roadmap/README/reviewer sources, TeX/PDF and current expectations | Generated-byte checks and documentation links after canonical outputs stabilize |

Source contract fixtures preserve the independently reviewed general statements
and computed-boundary behavior; they are not generated anew from a mutated source
during tests. Compiled type hashes are taken only from successful Lean output.
New status claims must cover physical substitution and retained output semantics
only. They must not upgrade arbitrary observers, charge/obligation gluing, global
routing or reference minimization into unconditional or polynomial results.

## Verification, progress and publication

Use an isolated remote checkout and an independently copied cache only after
matching the exact source tree and pinned toolchain. Compile bounded general
helper/declaration prefixes and inspect axiom closures before rebuilding the
changed dependency chain and explicit root.

Reconcile root imports, exact theorem-name/type and axiom contracts, package
script fixtures and durable workflow assertions before the relevant tests.
Only after the source is stable and compiled should generators emit inventory,
publication/status/progress evidence and reports. Derive all changed values
from that output and run the affected positive/hostile checks before the
deduplicated complete core verification.

No fixed weighted checkpoint or global gate is proposed to change. The verified
development baseline has a 40% risk-weighted estimate, uncertainty 20% to 40%,
and 0 of 5 global gates closed. Formal artefact coverage is separate and changes
only after this complete planned result earns its publication row.

Publication decision: defer a separate PNPLabs cycle for M261. The already verified M258
major site batch remains pinned and independent. Reuse unchanged proof and site
evidence at their proper boundaries. Keep meaningful verified-submilestone
notifications independent of website cadence.

Retain temporary checkouts, patches and logs only through the active verification
and release, then clean their exact recorded task paths.

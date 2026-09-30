# Growing-window candidate-universe boundary

## Why this substep matters

The unresolved objective is a source-derived, globally complete construction of
improving moves and terminal data with polynomial encoded size and runtime.
The manuscript's Section 16 ZeroSlack route and PCCMin complexity obligations
require both completeness and those bounds. A fixed-window search does not
provide global completeness, as the preceding guarded-spine result proves.

This substep tests the natural proposed repair of enlarging the existing
physical windows and retaining their complete explicit candidate enumeration.
It resolves that repair's object-size question, rather than adding another
fixed circuit, supplied-data sidecar or easy local milestone. It does not
construct the required global algorithm.

## Exact general result

The implementation is
[`NANDGrowingWindowUniverseBound.lean`](../lean/PNP/NANDGrowingWindowUniverseBound.lean).
For every `NatPolynomial`, it derives a source in the guarded nonminimum family
such that every accepted physical replacement has a complete
`PhysicalWindowSearch.candidateUniverse` longer than the polynomial evaluated
at the source query's actual encoded bit length.

The statement quantifies over every record width, arbitrary selected supports
(including disconnected or repeated records), and every valid offer. No
caller supplies coverage, global correctness, a minimum certificate or a
polynomial-size premise. The source has a previously proved strict equivalent
gain and positive residual slack.

Consequently there is no single polynomial and uniformly complete selection
of accepted windows/offers on this family whose complete materialized
candidate universes obey that polynomial bound in the encoded input size.

## Representation and argument

The query is the actual `encodeLockedInstance` representation of
`GuardedSpineFamily.candidate (n + 2)`, with baseline `n + 3`. Its declared
dimensions are `n + 3` inputs, `n + 4` gates and one output; the independently
equivalent shorter candidate has `n + 2` gates. This is a valid typed candidate
serialized by the general codec, not a claim that it is in the reduction
builder's image.

The proof reuses the general codec bound, including unary headers, gate/source
payloads, delimiters, threshold and four-bit tokens. It does not substitute
gate count or a unit-cost object parameter for bit length.

1. Every natural polynomial is bounded by a power of `n + 2`.
2. A tail of the real `allPrograms` enumerator contains at least the product
   contributed by its growing ordered-gate alphabet.
3. The exact-size branch remains in `smallerCandidates`, including its output
   words; no quotient or deduplication is invented.
4. Proper-support minimum forces every accepted improvement to require the
   source's full gate budget.
5. Substituting the actual encoding-size polynomial into an arbitrary proposed
   polynomial gives the contradiction.

Tiny executable fixtures count only zero-, one- and two-gate programs. The
large guarded searches are never executed as tests. Generality comes from
kernel-checked theorems, not exhaustive regression runs.

## Claim boundary and next direction

This is a materialized-list cardinality bound. It is not a lower bound on the
number of candidates visited, a raw-machine runtime lower bound, or a theorem
about every possible solver. Compressed, lazy, selective, context-sensitive and
different global constructions are not excluded. This does not decide P
versus NP or refute every manuscript route.

The next constructive obligation remains a source-derived globally complete
method whose full construction is polynomial in the encoded input size.
Do not repair the gap with a supplied optimizer, correctness premise,
unproved polynomial bound, project axiom or weakened target.

## Integration and validation order

The focused leaf theorem, six conclusion-axiom probes and nine regressions
passed before explicit-root integration. The conclusion closures contain only
`propext` and `Quot.sound`; the codec and small counting probes have narrower
closures. These are research results, not a merged-release claim.

Update the explicit root, frozen source/probe contracts, complete verifier
union and durable read-only workflow together. Then check those contracts and
the exact changed shell block before the root build. Regenerate the compiled
inventory and publication/report outputs only after source stabilization.
Check the resulting exact declaration sets and source closure before broader
verification. Reuse unchanged evidence; never repeat core proof builds as
website tests.

## Progress and publication decision

At the retained baseline
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-20-280`:

- Formal artefact coverage: 256 of 258 current scoped rows earned.
- Risk-weighted proof completion estimate: 40%.
- Uncertainty range: 20% to 40%.
- Global gates closed: 0 of 5.

No positive publication row or fixed checkpoint is awarded for this limitation.
The [canonical progress ledger](../status/PROOF_PROGRESS.json) remains the
authority. The score is neither confidence that the route is correct nor a
time estimate. Existing earned checkpoints do not claim the excluded global
enumeration bound; this result does not revoke them.

Defer a separate website update: the active publication already distinguishes
fixed-window completeness from global completeness and explicitly withholds a
polynomial bound for growing windows. This substep strengthens that existing
caution without changing a fixed checkpoint, global gate or the eligible
root theorem. Keep the site pinned coherently to its verified published core
commit until the next publication-worthy change. Preserve historical records.

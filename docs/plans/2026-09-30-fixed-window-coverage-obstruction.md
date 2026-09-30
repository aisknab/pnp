# Fixed-window coverage obstruction: core integration

## Impact and exact boundary

The source-derived bounded physical search is complete within its stated
support cap, but that is not a completeness theorem for global minimization.
The verified guarded-spine family now separates those statements uniformly:
for every fixed limit, a nonminimum circuit is quiet even under arbitrary,
possibly disconnected selected supports within that limit.

The substantive interface is:

```lean
theorem no_uniform_zero_slack_limit :
    ¬ ∃ limit : Nat, ∀ (inputs gates outputs : Nat)
      (source : Candidate inputs gates outputs),
      BoundedQuiet source limit → residualSlack source.toImplementation = 0
```

The explicit witness has an independently proved strict equivalent gain.
Every proper extracted support is minimum among all equivalent independent-
boundary NAND implementations, including replacements with sharing and
constants. The actual complete scheduled scan returns none by a symbolic
theorem, not by executing an exhaustive finite search.

The relevant downstream edge is the coverage needed by RW-BCELReady and
unconditional ZeroSlack. This refutes a fixed circuit-independent window cap
as sufficient for that edge. It does not refute every manuscript route, exclude
growing windows or global transformations, establish a polynomial solver, or
decide P versus NP. Preserve pinned historical manuscript artifacts.

## Main-based integration

Start from the latest fetched core main and preserve the research checkout.
The required import closure contains 81 modules. Import the 29 new dependency
modules and the necessary extraction, splice and output-cone source interfaces.
Do not copy unrelated research modules. Leave the unused compiler-scan and
physical-list-permutation additions out of this release.

The older constant-incidence, sharing-incidence and record-transport modules
are required dependencies but are not individually covered by the latest
research receipt. Verify them through the fresh integrated build and explicit
root axiom boundary; do not claim their evidence was already sealed there.

Carry the previously requested fallible-manuscript agent policy into this
current-main branch. Do not add private environment details. Preserve all
existing main-branch corrections and unrelated user work.

## Source and expectation chain

1. Reconcile the extraction and splice closed declaration lists in the same
   patch as their additive source interfaces. Do not expect the excluded
   compiler-scan APIs.
2. Add the explicit root import and update its import-closure contract.
3. Freeze the exact general minimum, all-cap quietness, strict gain and
   no-uniform-cap statements in focused positive and hostile source tests.
   Reject finite-cap substitutions, contiguous-only supports, supplied
   completeness/minimum authority, native proof authority and widened claims.
4. Bind the axiom audit and regression probes to the explicit root. Retain
   repeated-output-position, disconnected-selection and full-selection
   exclusion controls.
5. Extend only durable read-only verification and the current verifier test
   union. Update changed workflow block syntax/contracts before expensive work.
6. Regenerate inventory, publication, status and report artifacts only after
   proof sources stabilize. Derive every hash and count from those generators.
   Reconcile affected document and generated-output expectations before suites.

## Progress and publication decision

This is a correction/research result, not a new positive proof-completion
checkpoint or an additional earned roadmap row. The currently earned
foundations, reductions, strict-gain/stopping scaffolds and axiom removals do
not assert fixed-window completeness. None is invalidated merely by this
obstruction; the weighted estimate and earned-row baseline remain unchanged
unless the integrated dependency audit identifies a real conflict.

Retain the existing M280 status/progress coordinate as the last earned-row
baseline and date this subsequent finding separately. Record current evidence
coverage and risk-weighted completion separately using the canonical ledger.
Never award points just for adding declarations, tests or this correction.

A major PNPLabs publication is warranted after core integration and ordinary
release gates pass, because the general limitation changes what the bounded
search route establishes. Update the full active public surface then, from the
exact merged core commit, without rebuilding Lean as a website check.

## Verification and next research

Research leaf evidence is already green. This fresh current-main checkout
tests a different dependency and explicit-root boundary; it must pass the
required integrated build, axioms, inventory, hostile/publication checks,
normal PR checks and exact-merge reproduction. Reuse immutable evidence when
source, inputs, environment and boundary are unchanged. No ceremonial install,
unchanged exhaustive search or duplicate website proof suite.

After the verified correction is released, pursue a source-derived constructive
route that addresses the obstruction. Bounded quietness must not be promoted
to global ZeroSlack, and a supplied optimizer, correctness premise, coverage
certificate or unproved polynomial bound is not a repair.

## Integration preflight record

The root/source/workflow preflight and the changed documentation contracts
pass. Older extraction, arbitrary-splice, output-cone, unary/history and
context-aware transport contracts were reconciled before those tests ran.
All required annotated archive tags resolve to their pinned objects.

The fresh integrated dependency build runs serially before the explicit
library root, without a cache from the different research tree. A source
hash snapshot rejects proof-source changes during that build. Integrated
compiled audits and generated publication evidence are required before release.

The three npm lifecycle commands contain only explicit Node test-file lists
under both audits/ and test/. Their 208 distinct files and the current verifier's
301 files have a union of 308 files; 7 npm files are not in the verifier list.
Run that union once under bounded concurrency, then reuse that exact
successful file coverage for the verifier's unit-test step. This does not skip
its remaining status, publication, links, archive or integrity gates, nor
independent CI and exact-merge release boundaries. Refresh the union if any
producer list changes.

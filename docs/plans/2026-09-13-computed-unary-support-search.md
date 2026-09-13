# M258: source-derived complete search for proper unary R7 gains

## Named manuscript dependency

Reconstruct the support-discovery edge of section 6.1's unary cut realization
and VerifyDW soundness in the manuscript pinned by
`archive/legacy-v0/ARCHIVE.json`. Package E requires a proper physical support,
an explicit equivalent complete local word and strict physical saving.
Sections 2 and 3 define the actual incoming boundary and completed frontier.

M257 computes and compiles the minimum zero/unary word for any supplied finite
physical support. The missing edge is finding a successful support from the
actual carrier, without a supplied support family or an exhaustive powerset.
This milestone must complete that search edge, not merely add another chosen
support fixture or a sufficient-only recognizer.

## Baseline and safe integration point

Verified development parent: M257 commit
939b4bf66f6d8eec48b868972484083d041ee231, tree
b56cb11077faa9ed37a1c457905e7ce66fc23c24. Its explicit root, 31 reviewed
type/axiom interfaces, 16 guarded runtime fixtures, canonical inventory,
publication/progress/report and complete 1,681-test suite passed.

Cycle preflight found core main at M251 merge
a30c344869c66e4a04b12a1cc9fbfb190f5fe48e. Independent exact-merge verification
and three normal post-merge checks passed; the final Lean workflow is still
running. No core PR is open. M252 through M257 remain core-verified release
successors. PNPLabs main is unchanged at
3d62ceb5ab14d51b39bd1a89307dbfb8d5a55226, the coherent M231 publication.

Development formal artefact coverage is 233/235. The risk-weighted estimate is
40%, uncertainty 20% to 40%, with 0/5 global gates, no project-specific axioms,
an absent eligible root and a false publication gate. No M258 credit is awarded
before the complete selected obligation is proved.

## General construction

Keep original input count, gate count, output width, computational field count
and physical support arbitrary. All fields remain actual sources in the program.

Enumerate optional boundary choices from the sources actually consumed by the
program's gates, plus the empty-boundary choice. Do not enumerate all declared
primary inputs, all valuations, all subsets, all supports or all implementations.
At most two physical wires occur per gate; duplicates may remain in this search
list without affecting correctness or its size bound.

For each boundary choice and each omitted original gate, scan the program in
topological order. A gate is selected exactly when it is neither the omitted
gate nor the chosen boundary gate and both sources are constants, already
selected gates or the chosen boundary wire. The resulting maximal admissible
support has at most the selected boundary wire as its actual incoming boundary.
The omitted gate makes the support proper.

Also include every singleton physical gate support. These handle the
one-gate-to-zero-gate saving without requiring a stronger unproved
monotonicity theorem for different complete frontiers.

The family has at most

    (2 * g + 1) * g + g

entries for g original gates. Every entry has at most g gate records. This is
a physical candidate-count bound, not yet a complete encoded-size execution,
output-size or certificate-size theorem. The full compiler and every data
construction retain separate runtime obligations.

Run the existing actual M257 proper-gain checker on this computed family.
Return its actual support and proof-bearing compiled replacement when a candidate
succeeds. Do not accept a caller-supplied family, rank, completeness certificate,
agreement, replacement or successful compiler result.

## Required completeness argument

First prove that a support's physical extraction depends only on its selected
gate predicate. Duplicate gate records and non-gate records must not alter the
computed physical boundary, frontier, gate count or complete open function.
Preserve the full fields and exact canonical orders.

For any arbitrary support with at most one actual incoming boundary, choose
that boundary (or none) and an original gate outside the proper support.
Prove by program induction that the corresponding maximal scan contains every
selected gate of the original support, while remaining proper and zero/unary.

If the original support contains at least two gates, the containing candidate
also does, and M257's at-most-one-gate realization is a strict saving.
If the original support has one gate, its canonical singleton is in the family
and extraction congruence preserves the actual strict saving.
An empty support cannot admit a strictly smaller implementation.

The public theorem must have the following strength, with all dimensions
arbitrary:

    findGain_complete (carrier : WireCarrier inputs outputs fields)
      (records : List (TerminalPrimitiveRecord inputs
        carrier.implementation.gateCount (outputs + fields) 0))
      (small : (pulled carrier records).boundary.length <= 1)
      (proper : 0 < exteriorCharge carrier records)
      (other : Implementation (pulled carrier records).boundary.length
        (pulled carrier records).interface.length)
      (sameOpen : other.candidate.semantics =
        (pulled carrier records).extractedCandidate.semantics)
      (smaller : other.gateCount < (pulled carrier records).gateCount) :
      (findGain carrier).isSome = true

Here `pulled` and `exteriorCharge` refer to M257's actual construction.
The comparison implementation appears only in the mathematical completeness
theorem; neither it nor its agreement is an input to the executable search.

Prove the converse from an accepted result, and derive a precise no-result
statement excluding every proper zero/unary gain in this computational scope.
No-result must not be called ZeroSlack or global minimality.

## Sound result and downstream use

Every accepted result must identify an actual proper original support, preserve
every ordinary output and full computational field at every ambient valuation,
and have exact replacement-plus-original-exterior charge and strict saving.
Retain source-exact full-value R7 discharge for original R5 identities.
The support and replacement are both computed from the carrier.

This is complete computational R7 support discovery for actual zero/unary
boundaries. It is not the full manuscript carrier, noncomputational profile
semantics, arbitrary boundary width, every R5-R8 interaction, obligation DAGs,
all-trace N1-N10 normalization, complete Package E, global routing,
unconditional SaturatePositive/BCELReady/ZeroSlack or exact polynomial PCCMin.

If the completeness proof fails, stop this milestone at that boundary. Do not
publish only family soundness, a finite prefix, a supplied-family theorem or
an added completeness premise as the planned completed result.

## Source, expectations and verification

Prepare source signatures, exact claim boundaries and the positive/hostile
regression design with the implementation. If extraction congruence needs
private implementation access, use a focused append-only extension and preserve
all inherited definitions, statements and proof bodies.

Reconcile root imports, exact theorem-name producers and consumers, the axiom
audit, package-script fixture, verifier test list and exact workflow block before
expensive verification. Kernel fingerprints and generated counts come only
from successful compilation; never preselect them.

Regression coverage must include: no gates; no proper saving; a singleton
constant gain; a larger maximal candidate gain; whole-support-only gain;
the primary-boundary case requiring an omitted gate; a sole external-gate
boundary with early constant observations; hidden selected and exterior fields;
repeated/non-gate records; multiboundary supports; repeated source wires; and
unused declared primary inputs absent from the candidate enumeration.

Use guarded small exhaustive support comparisons only as regression evidence
for the general completeness theorem. The production search must not enumerate
the powerset. Runtime fixtures remain separate from proof authority.

Run focused source/root and axiom checks, then root/type/inventory/publication
seals, current documentation and report, one combined deduplicated core suite
and normal release/independent exact-object gates. Reuse unchanged evidence
when only commit parents change.

## Progress and publication decision

No fixed weighted checkpoint is expected to close: the complete R7 support
selector is only one part of terminal-derived families and the full PCCMin
construction. Candidate-count bounds alone do not earn polynomial-runtime
credit. Preserve the 40% estimate unless a fixed checkpoint actually changes.

Publication decision: publish a batched PNPLabs update if this complete
source-derived support-search-and-rewrite capability is earned and released.
It would complete a general executable R7 discovery path with full computational
field preservation, a substantial end-to-end change from the published M231
bottom line. The trigger is that capability, not the number of accumulated rows.
Until the final required proof and release checks pass, keep the published
source pin and coherent values unchanged.

Batch all pending earned core milestones from the latest exact verified merge.
Use the full site/publication audit, reuse the core Lean and report evidence,
then follow the authorized deployment and independent production verification.
Keep verified submilestone notifications independent of site cadence.

Retain temporary verification and release files only while their recorded work
is active. Remove the exact named task paths after their final release purpose
is complete.

# M262: total source-ordered, charged arbitrary-support expansion

## Manuscript anchor and dependency edge

Follow Sections 2, 4, 5 and 6.1–6.2 of the manuscript pinned by
[the legacy archive](../../archive/legacy-v0/ARCHIVE.json): actual compatible
replacement, full computational values, uniquely owned physical charges and the
construction prerequisites of Package E.

Close one general edge: construct an acyclic physical replacement at arbitrary
support and incoming-boundary widths, then prove its complete computational
semantics and exact copy cost. A caller must not supply a rank, a topological
schedule, compiler success or final-circuit correctness. This is a construction
prerequisite, not the complete matched-cost Pull/Expand law of the manuscript.

M249 already shows that equality of local open functions does not imply that a
literal splice is acyclic. Preserve that theorem and the old compiler's rejection
of its cyclic fixture. It is not a contradiction of the manuscript's still
unconstructed complete-carrier premises. Reuse the existing support extraction,
prefix noninterference, physical source ordering and raw-graph compiler. Do not
re-earn them, replace the manuscript route or add a supplied-DAG checker as the
milestone. Existing cone and unary constructions retain their better applicable
cost bounds.

Development was planned before implementation and subsequently anchored on the
verified M261 merge `ccb3f967a354f5d2188ee3a55f2f861d1ca01520`.

## General target

Use arbitrary natural-number candidate, support, replacement and computational
field dimensions. The implementation also permits arbitrary `profileWidth` in
selection records; this does not assert preservation of arbitrary semantic
profiles or implementation-dependent observers.

For `candidate : Candidate inputs gates outputs`, let `records` be a list of
terminal primitive records and let `replacement` have exactly the extracted
boundary and interface widths. Compute exterior count `E`, selected count `S`,
distinct retained physical producer count `K` and replacement gate count `R`.
The original count is `G = S + E`.

Allocate exactly `E + K * R` raw nodes. Retain each exterior gate once and allocate
one complete replacement copy per distinct retained producer, not per repeated
output or field reference. A copy anchored at original producer `g` keeps primary
boundary inputs and gate boundary inputs strictly before `g`; later gate-valued
ports are deliberately false. Internal replacement edges stay in that copy.
Every reference is resolved from actual source data.

Derive rank `(R + 1) * g + R` for an exterior gate and `(R + 1) * g + j` for the
copy's local gate `j`. Prove that every actual dependency decreases this rank,
including empty dimensions, and use the existing executable raw-graph compiler.
Compilation and construction have no semantic premise.

The precise local rewriting condition for semantic preservation is

```lean
replacement.semantics =
  (extractTerminalSupport candidate records).extractedCandidate.semantics
```

Under this full open-function equality, prove masked-output preservation for
**every open boundary valuation**, the actual graph equations and every original
ordered output. Expose all computational fields before expansion and unpack the
same compiled word afterwards. Preserve full field values, repeated literal
source sharing, the coordinate of an existing R5 creation and that creation's
original full source value.

Prove unique, disjoint physical ownership and coverage of every emitted gate.
The required size statement is

```text
expanded gate count = E + K * R
expanded gate count < G iff K * R < S
```

Proper support separately requires `S < G`. Do not replace paid saving by `R < S`,
infer properness from saving, or merge different physical producers merely
because their Boolean values coincide. The single-interface corollary applies
at arbitrary incoming width; it is a consequence of the general construction,
not a fallback to another fixed-size fixture.

## Verification and publication sequence

1. Keep exact general theorem interfaces and independent Lean examples. Run
   focused hostile mutations for unpaid copies, backwards or over-masked ports,
   wrong owners, supplied correctness, weakened full-field agreement and lost
   ownership. Update changed expectations before broad validation.
2. Build the changed dependency chain and explicit root, then run the permanent
   root-imported axiom audit and constructor/carrier regressions. Execute the
   exact new durable workflow block after its syntax check. Runtime fixtures
   are regressions, not proof authority.
3. Synchronize reviewed names, publication rows and fingerprint keys before the
   compiled inventory. Seal generated inventory, status, progress and report
   outputs; derive counts and hashes rather than preselect them. Run focused,
   full, PR, post-merge and exact-merge validation at their distinct boundaries.
4. After the verified core release, publish the pending earned core milestones
   in one batched PNPLabs publication audit. The general physical-construction
   boundary is materially new; preserve the paid-copy and global non-claims.
   PNPLabs must not repeat the core Lean build.

A failure of the general theorem stops this milestone. Never substitute a fixed
boundary width, supplied ordering, correctness certificate or project axiom.

## Remaining obligations and scoring

Matched-kappa Pull/Expand, global CompatibleReplacement/SlackLaw from local gain,
arbitrary observers and profile histories, the full R5–R8 dependency calculus,
complete Package E, global route coverage, unconditional SaturatePositive,
BCELReady and ZeroSlack, exact PCCMin and complete encoded polynomial bounds
remain open. The root theorem is not established.

This checkpoint does not close a fixed weighted proof-progress checkpoint.
Keep formal artefact coverage separate from risk-weighted proof completion,
using [the canonical progress ledger](../../status/PROOF_PROGRESS.json).
At the verified M261 planning baseline: formal artefact coverage was 237 of 239
current scoped rows earned; risk-weighted proof completion was 40%, with an
uncertainty range of 20% to 40%; global gates closed were 0 of 5. No percentage
increase is planned merely for adding this construction or its evidence row.

Publication decision: publish one batched PNPLabs update after the M262 core release gates pass. The source-derived physical constructor now covers arbitrary supports and incoming-boundary widths, materially extending the previous scoped construction boundary. The public account must retain the paid-copy condition and all global non-claims; this is not a score increase or a publication triggered merely by another evidence row.

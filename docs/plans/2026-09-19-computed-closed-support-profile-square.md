# Computed closed-support observations and profile-compatible squares

Status: the four general modules, incremental explicit-root build, exact
24-declaration axiom audit, 14 general type contracts, 25 kernel guards and
10 runtime checks pass. The compiled inventory has been extracted and its
reviewed theorem pins are sealed. Canonical publication validation, normal
review checks and exact-merge verification remain required.

Integration starts from the actual M276 merge, whose tree matches the reviewed
feature tree. Its remaining post-merge checks may run alongside source work,
but the next PR is not published before those checks and M276’s exact-merge
reproduction pass. No fixed checkpoint is earned merely by this integration.

## Legacy anchor and precise dependency

The manuscript pinned by
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`, Section 3, requires
saturated support squares with compatible profile data. The source-derived
profile observation is also a prerequisite of RW-SaturatePositive. Existing
structural square and profile-locality theorems do not by themselves identify
the concrete computational-field observations of their actual extracted
supports.

Derive that missing computational-field interface from a circuit, an ordinary
keep mask and seed records. Reuse the existing exact extraction, unary
dependency closure, square laws and arbitrary-context profile-locality
theorems. Do not count those existing results as new progress.

## General statements checked

- For every circuit, projection, seed and field, availability in its computed
  closed support is equivalent to retaining some original source that matches
  the field uniformly over all input valuations. The matching table and the
  support are computed, not supplied correctness data.
- For arbitrary seed pairs, observations of their computed union are the
  Boolean union of the separate observations. The law extends to arbitrary
  finite families and to monotonicity under seed inclusion. An empty family
  starts from the empty support's observation, not an unconditional false bit.
- Seeding the requested profile records preserves the requested field values.
  This uses the existing influence-locality theorem with the concrete observer;
  it does not inject every field's literal original gate.
- A square constructed from two such seeds preserves the requested field
  values at its actual meet, left, right and join supports. Every pair of
  corners consequently agrees on those fields for every ambient valuation.

The source modules are
[`NANDClosedSupportObservation`](../../lean/PNP/NANDClosedSupportObservation.lean),
[`NANDClosedSupportUnion`](../../lean/PNP/NANDClosedSupportUnion.lean),
[`NANDClosedSupportProfile`](../../lean/PNP/NANDClosedSupportProfile.lean) and
[`NANDClosedSupportSquare`](../../lean/PNP/NANDClosedSupportSquare.lean).

## Verified claim boundaries

The regression family includes missing and constant/input-equivalent fields,
alternate semantically equal original sources, empty dimensions, arbitrary
finite seed families, and different physical sizes at compatible corners.
It also rejects these invalid inferences:

- A raw unclosed support cannot use the closed-support source table or union
  law. A missing predecessor can turn an apparent table match into a free
  ambient input with the wrong semantics.
- Field preservation is not ordinary-output equivalence.
- Forgotten fields need not agree between square corners.
- A requested field can force the entire support; preservation does not imply
  properness, minimality or positive improvement.

The stronger positive-slack obstruction is checked in
[`ClosedSupportPositiveObstruction`](../../lean-regression/PNPClosedSupportProfileSquare.lean).
Two duplicate binary NAND gates have a one-gate full-profile-equivalent
witness, hence positive full-profile slack. In the actual computed
wire-profile model, either gate influences the profile coordinate. The
bidirectional dependency edges couple both gate records through that
coordinate. For **every seed**, the saturated support therefore selects
either no gate or both gates. There is no proper seed, and consequently no
proper-positive seed, for this candidate/model.

This is an obstruction to a stronger claim about this construction, not a
counterexample to a manuscript theorem under additional terminal or
admissibility hypotheses. It does not rule out the explicit whole-circuit
gain or another route. A normalization review checks that the existing
sharing pass saves one gate on this example, the candidate is not
three-pass-quiescent, and the existing normalizer returns one gate.
Consequently this example gives no evidence against a theorem restricted
to normalized terminal candidates. The older zero/unary search obstruction
is narrower and is not substituted for this new quantified seed statement.

## Next research direction, not an established replacement

The source-table theorem records alternatives: one matching retained source
can suffice for a field. The current influence-based closure instead retains
every influencing gate. The duplicate example shows why those two requirements
must not be confused.

First determine which support-generation obligations remain after the existing
physical normalizer and the manuscript's terminal/admissibility hypotheses.
The duplicate example alone does not justify a replacement construction.
If a remaining obstruction is demonstrated, investigate a deterministic,
source-derived choice among matching alternatives followed by physical
dependency closure. Before adopting it, prove uniform
field preservation, source closure, ordinary-output compatibility where
claimed, physical size accounting, and any required square or route laws.
Record which manuscript dependencies this candidate implements and which
remain open. Do not transfer the present square theorem automatically to a
different closure rule. Semantic source matching remains exhaustive unless a
separate encoded-input polynomial theorem is established.

## Integration and verification order

1. Complete the M276 review/merge boundary, fetch its exact main commit, and
   start a new branch from that merge. Preserve the current release checkout.
   Its source tree matches the fully reviewed feature tree. Integration may
   overlap final post-merge checks, but publication of the next PR requires
   all M276 post-merge checks and its exact-merge reproduction to pass.
2. Promote this coherent bundle without weakening any checked statement.
   Consolidate the research audit entrypoints into one permanent explicit-root
   audit retaining all reviewed names; consolidate regression entrypoints only
   if every type contract, kernel guard and runtime assertion is preserved.
3. Reconcile the explicit root, closed import contract, reviewed theorem-name
   producer/consumer sets, publication milestone and fingerprint keys together.
   Search older consumers by every changed existing source path as well as
   declaration name. No old proof module needs a speculative rewrite.
4. Freeze source-shape and hostile mutation contracts from the successfully
   checked source, then run the cheapest applicable source/workflow preflight.
   Keep the durable workflow below its existing review budget; do not add
   temporary workflows or relax guards.
5. Refresh the changed dependency chain and explicit root before root-importing
   regressions or axiom audits. Extract the compiled inventory once. Derive
   hashes, counts and documentation expectations from that output.
6. Reconcile canonical status, progress and current documentation before
   focused publication checks. The progress ledger, not a row count, owns
   proof-completion estimates.
7. Compute the exact required test union, including npm lifecycle hooks and
   verifier-only files. Reuse unchanged valid evidence and run uncovered
   assertions once. Retain required PR, post-merge and exact-object boundaries.
8. Perform normal draft review, complete checks, manual ready/merge and exact
   merged-object verification. Do not rebuild the core proof in PNPLabs.

## Remaining obligations and publication decision

Only computational wire fields are treated. The complete manuscript profile
grammar, terminal-derived governed families, ordinary-output reconstruction
where required, legitimate full projection squares, proper positive supports,
forced-cost transparency, global route coverage and rank decrease remain open.
So do unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial
PCCMin, encoded runtime/output/certificate bounds, deterministic CNFSAT in P
and the eligible root theorem.

Source matching and profile influence still perform finite exhaustive
computations. No polynomial runtime, semantic minimum or global proof
completion follows. The positive-slack obstruction invalidates no earned
fixed checkpoint: the stronger proper-positive guarantee was already open.

Publication decision: defer. This is a bounded computational-profile
compatibility result with explicit limitations, not a completed end-to-end
route or a changed global-proof bottom line. Keep the coherent published
source pin unchanged and batch this evidence when a major publication is
warranted. Formal artefact coverage and risk-weighted proof completion remain
separate; this research phase changes neither public metric.

See the [canonical progress ledger](../../status/PROOF_PROGRESS.json) and
[pinned archive](../../archive/legacy-v0/ARCHIVE.json).

# Source-derived zero-cost exposure and materializer cost: research plan

Status: general component implemented and kernel checked; exact compiled pins
and coordinated release inputs are prepared. Release validation and merge remain
pending. This is not a proof of the global route.

## Legacy dependency

The pinned report's sections on charge ownership, traceable normalization and
RW-SaturatePositive distinguish physical charge accounting from preservation of
the full semantic minimum. In the pinned TeX, lines 776-804 require transparent
steps to add the same **forced** cost to support size and every full realization.
Interface exposure must instead route to Package E unless it is a zero-cost
retract. The missing dependency is a construction that establishes that condition,
not a Boolean flag naming it.

The document coordinate is
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`; current source baseline is
`9c58ce7dd90122e816bff5b4f2273c270b5dd0b6`.
See [the archive](../../archive/legacy-v0/ARCHIVE.json).

## Research decision and nonduplication

No additional source notes are assumed to exist. Fill missing definitions through
explicit constructions and checked mathematics, while distinguishing proposed
reconstructions from the historical manuscript.

A literal repeated-prefix sharing pass would duplicate the existing constructive
NAND sharing normalizer. A charged prefix-block representation alone would
account for its implementation cost, but would not force the same semantic
minimum increase. Do not publish either as resolution of R3/N5 or global
saturation.

Existing finite terminal exposure routing accepts an explicit finite observer
and projection and classifies a supplied finite model. Its zero-cost retract
branch does not provide the concrete all-circuit construction proposed here.
Reuse that classifier later; do not republish it.

## General target

For arbitrary input, existing-output and new-field widths, define an exposure
layout whose new fields reference only an input, a constant or an existing
ordered output. Build the extended output word from those references without
allocating gates. Build the projection that recovers the original output word.

Prove for every concrete circuit C and every such layout a:

- All old outputs remain unchanged for every valuation.
- Each exposed field equals its selected input, constant or old output.
- The actual gate count is unchanged.
- Every realization of C can be extended at zero gate cost.
- Every realization of the extended function projects back at zero gate cost.
- Consequently, mu(extend(C,a)) = mu(C), and physical residual slack is unchanged.

The semantic minimum is used only in specification theorems. The constructor must
not enumerate implementations or valuations, execute a reference minimum, or
accept correctness evidence from the caller.

Add a source-derived recognizer for concrete field wires: constants and inputs
are immediate; a gate source must match an existing output source. A field's
mere presence as an internal gate is not enough. Failure is an unresolved
exposure obligation, not automatically a valid Package E gain or descent.

The construction and its exact syntactic acceptance/refusal boundary are now
kernel checked. They establish the literal input/constant/old-output alias branch
of zero-cost exposure, not all semantically free exposures, the positive-cost
transparent branch, full carrier derivation, global route coverage or
unconditional SaturatePositive. A semantically redundant but distinct internal
wire may still be refused; refusal is not a Package E routing theorem.

## Falsification and regression expectations

Before implementing the general proof, run a small independent truth-table
enumerator for the concrete NAND basis.

1. A one-gate NOT output and two separately allocated copies exposed as a pair
   have the same semantic minimum. Unique ownership and one extra physical
   charge do not alone force a one-gate minimum increase.
2. A circuit computing an unused NOT but outputting its input has positive
   slack. Exposing that hidden NOT adds no physical gates but increases the
   semantic minimum and can destroy that slack. The syntactic recognizer must
   reject this as a zero-cost retract.
3. Input, constant and existing-output aliases, including duplicates and empty
   dimensions, preserve the independently enumerated minimum in bounded cases.
4. Invalid references, hidden non-output gate fields and altered layouts fail
   closed. Accepted data are interpreted from the actual circuit.

The first case tests an insufficient proposed inference, not the stronger
manuscript premise that the added cost is genuinely forced. Finite experiments
are falsification/regression evidence, never general proof authority.

## Implementation and verification order

1. Update the research policy and record this plan. Keep status and scores intact.
2. Run the bounded semantic probe; record actual outcomes and resource use.
3. Add the general concrete Lean construction and proofs, together with focused
   expected types and hostile cases. Compile only its changed dependency chain
   first. Reuse existing minimum and output-word interfaces.
4. Integrate raw recognition and the relevant source-derived carrier interface;
   state exactly which full-profile obligations remain unresolved.
5. Only after the general boundary is proved, choose the milestone interface,
   reconcile root imports, axiom/inventory name sets and every consuming test,
   then perform the normal core release checks. Do not generate premature
   fingerprints, counts, or publication evidence.
6. Review whether any positive-cost transparency criterion can be derived.
   Do not promote a charged block into a semantic lower-bound certificate.

## Current research evidence

The explicit root build now checks the general extension/projection theorem,
equality of the concrete semantic minimum, preservation of residual slack, exact
syntactic recognition/refusal, and the actual wire-carrier exposure contract.
See [the construction](../../lean/PNP/NANDZeroCostExposure.lean) and
[the carrier integration](../../lean/PNP/NANDWireCarrierZeroCostExposure.lean).

The bounded independent probe confirms both planned counterexamples: a separately
charged duplicate NOT output has no additional semantic minimum cost; exposing an
unused internal NOT while retaining its input output increases the minimum even
though no physical gate is added. Input/constant/old-output aliases passed the
bounded checks, and non-output internal gates were refused. Those experiments
remain regression evidence, not a proof of the manuscript or its stronger forced
positive-cost premise.

The new [Lean regressions](../../lean-regression/PNPZeroCostExposure.lean) also
kernel-check both counterexamples and the general interfaces. The
[axiom probe](../../lean-audit/PNPZeroCostExposureAxiomAudit.lean) finds no
project-specific axiom or `Classical.choice` dependency in the new claims. The
minimum/slack and carrier-preservation theorems have empty axiom closures; some
recognizer equivalence proofs use only standard `propext` and `Quot.sound`.

Successful checks, reused when their inputs and boundary are unchanged:

- `lake build PNP.NANDZeroCostExposure`
- `lake build PNP.NANDWireCarrierZeroCostExposure`
- `node --test audits/lean-root-target0.test.mjs`
- `lake build PNP`
- `lake env lean -DwarningAsError=true lean-audit/PNPZeroCostExposureAxiomAudit.lean`
- `lake env lean -DwarningAsError=true lean-regression/PNPZeroCostExposure.lean`
- `node --test audits/lean-zero-cost-exposure0.test.mjs`

This is not yet an inventory/publication seal, the full core release suite, a
verified PR or merge, an earned milestone, or a publication release. Prepare the
reviewed theorem-name contract, current documentation, generator inputs and
release workflow expectations before the normal release checks.

## Baseline and publication decision

At PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-18-272:

- Formal artefact coverage: 248 of 250 scoped publication rows earned.
- Risk-weighted proof completion estimate: 40%.
- Uncertainty range: 20% to 40%.
- Global gates closed: 0 of 5.

These are baseline values from the [canonical ledger](../../status/PROOF_PROGRESS.json),
not credit for this research. The eligible root is absent. No score or gate
changes for a plan, experiment, or additional local theorem alone.

Publication decision: defer. Preserve the coherent published site pin. Publish
a major update only if a fixed checkpoint/global gate changes, the general
end-to-end capability changes the public bottom line, or a published claim needs
correction. This research does not yet establish any of those transitions.

## Current contract and regression consumers

| Producer | Expectations and cheapest check | Release boundary |
| --- | --- | --- |
| Zero-cost references and tuple compiler | General minimum/slack transfer, literal-alias completeness and exact gate-refusal types in `lean-regression/PNPZeroCostExposure.lean` | Root-import axiom probe and reviewed inventory |
| Actual `WireCarrier.exposed` integration | Same gate count, minimum and slack for source-checked tuples; no supplied observer | Concrete carrier theorem in `NANDWireCarrierZeroCostExposure.lean` |
| Explicit root imports | Existing dynamic all-source closure in `audits/lean-root-target0.test.mjs` | Run source-only root checks before the root build |
| Counterexample fixtures | Distinct duplicate producers do not force extra minimum; hidden NOT exposure destroys slack; semantic duplicates can be refused syntactically | Tiny kernel-checked regression, not progress credit |
| Eventual publication pins | Reconcile Lean inventory names, required theorem names, fingerprints, status and publication tests together | No generated seal or earned row before compiled evidence |

The checker completeness/refusal proofs and concrete carrier integration compile,
and the explicit-root audit and prepared Lean regressions pass. The
regression expectations include input and both constant aliases, repeated output
aliases, no fields, no ordinary outputs, completely empty dimensions, internal
gate refusal and an intentionally refused semantically redundant gate.

Reuse the existing M240 independent-materializer theorem:
`appendIndependentNandMaterializers_referenceMinimum` already proves an exact
positive-cost shift for a genuinely fresh independent input bank. Do not reprove
or re-award that result. It does not justify charging arbitrary existing-input
duplicates or exposing arbitrary hidden internal wires. The new duplicate fixture
tests this boundary more directly; it is not a new positive-cost milestone.

## M273 release preparation

The reviewed milestone ID is `source-derived-zero-cost-exposure`. Its general
interface consists of the exact theorem names in
[the axiom probe](../../lean-audit/PNPZeroCostExposureAxiomAudit.lean).
Register this same set in the Lean inventory producer, JavaScript required-name
contract, publication row and fingerprint-key set before exporting the inventory.
Every fingerprint has now been derived from the compiled environment and sealed
with its exact defining module and axiom closure. The temporary null-pin state
was not earned evidence and is not part of the release.

Prepare `audit:m273`, its closed package-script fixture, the aggregate verifier
and the durable Lean workflow together. The new compiled-publication regression
will pin every exact type, defining module and axiom closure, and reject weakened
types, supplied conclusions, missing evidence, extra authority and widened claims.
Its status-field mutations must cover both positive claims and explicit non-claims.
Update current summaries and progress history before generated checks; reuse the
unchanged root and focused proof evidence.

Publication decision: defer. This establishes a source-derived literal-alias branch with exact minimum and slack preservation, not all semantic exposure, full manuscript profiles or global route coverage. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.

## Pre-review verification

The explicit root build, focused axiom audit and kernel regressions passed.
The compiled inventory supplies the exact 22 theorem pins. The focused M273
release contracts passed all 16 tests, including weakened-type, extra-authority,
status-field and progress-boundary mutations. The normal package lifecycle
passed 153 pre-tests, 497 main tests and 660 post-tests, with no failures or
skips. The conservative verifier, documentation links and deterministic report
build with rendering checks also passed.

The conservative verifier uses its documented skip-unit-tests option after
the normal suite, matching durable CI and avoiding a duplicate test launch.
No unchanged Lean root or inventory build is repeated for these release edits.

The previous successful full Lean CI run took about 110 minutes under a
120-minute limit. The durable limit is now 150 minutes to retain headroom for
the added checks and ordinary runner variance; no proof check is removed.

Independent PR checks and the normal reviewed merge sequence remain pending.
The proof estimate and all fixed checkpoints are unchanged.

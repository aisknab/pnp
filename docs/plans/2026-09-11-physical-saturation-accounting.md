# M235 plan: actual physical saturation accounting

This plan records the pre-implementation specification, not current release
status; the canonical formal reconstruction status records earned milestones.
Isolated preparation starts from the verified
M234 feature commit `f79d876090461225202aa7ef6c490a9b2328644f`, tree
`79cd2c956e2acc85a597751bba7ca9af262bed0f`. M234 is awaiting its durable PR
checks. Re-anchor the release branch to the actual M234 merge and complete its
post-merge verification before publishing M235.

## Legacy anchor and dependency edge

The manuscript pinned by [the archive manifest](../../archive/legacy-v0/ARCHIVE.json)
requires actual computed support saturation in section 3. Section 4 charges one
unit for each physical NAND gate and requires genuine charge ownership.
Section 10, RW-SaturatePositive, compares support size, the full minimum and the
quotient minimum along the deterministic saturation chain. Its named obligations
include `transparentSaturationCostBalanced` and
`firstNontransparentStepRecorded`.

M234 connects the replay endpoint to canonical saturation and proves metadata
cost balance. The remaining structural edge is that every generated physical
event adds a genuinely new gate, from an already active dependent. Without
this edge, the raw classifier can report a missing owner or a support-cost
mismatch without those reports being distinguished from genuine minimum-cost
or nonunique-ownership obstructions.

Prove the structural facts for the actual executor, then refine its first
nontransparent result. Preserve the executor, support extractor, observer,
reference minima and existing classifier. Do not introduce a replacement
algorithm or a supplied correctness certificate.

The finite dependency path is: actual saturation trace; fresh physical insertion
and active dependency; exact unit support charge; first genuine ownership or
minimum-cost obstruction; globally routed saturation; BCELReady; ZeroSlack.
This milestone addresses the two structural accounting edges and the resulting
exact obstruction boundary, not the missing global routing theorem.

## General interfaces

All statements quantify over arbitrary finite input, gate, output and profile
dimensions, systems or executable models, seeds and actual generated events.
Event membership is a domain condition, not a supplied validity certificate.

1. `terminalSaturateTrace_event_context`:
   for any system, seed and event in its computed trace,
   `event.dependent ∈ event.beforeRecords ∧ event.required ∉ event.beforeRecords`.

2. `terminalCandidateSaturateTrace_supportCostBalanced`:
   for any candidate-derived generated event, its actual computed support size
   after the event equals the size before it plus
   `terminalSaturationEventCost event`. This is one for a gate and zero for
   metadata; it is derived from the real extractor, not stipulated.

3. `terminalCandidateSaturateTrace_event_owner`:
   some rule equal to the event's recorded rule, paired with its actual dependent,
   belongs to `terminalSaturationEventOwners` for that event and the
   candidate-derived system. This proves existence, not uniqueness.

4. `terminalCandidateSaturateTrace_physicalObstruction`:
   every generated event which is not transparent requires a physical gate and
   has a genuine remaining obstruction: its derived owner count is not one,
   its full minimum does not increase by one, or its quotient minimum increases
   by more than one. Missing-rule and support-cost defects cannot substitute
   for these conclusions on an actual trace.

5. `terminalCandidateSaturateTrace_balance_or_physicalObstruction`:
   the canonical computed saturation either preserves the normalized seed's
   full slack and does not decrease its projection defect, or the existing
   classifier identifies a first nontransparent event, with its transparent
   prefix, whose required record is a gate and whose genuine obstruction
   satisfies the preceding disjunction.

The last interface must consume the existing total classifier internally.
It must not accept an all-transparent history, replay equality, charge balance,
owner certificate or preselected route as an input. It does not assert that
the obstruction is already a global named route, a verified gain or descent.

## Proof sequence

1. Reuse the trace erasure and the existing duplicate-free work-state invariant.
   Show that generated pending records are absent from current cost records.
   Preserve active-dependency membership through the pending queue and emitted
   events. Derive the general public event-context theorem.
2. Prove that adding a fresh gate increases the canonical selected-gate count
   exactly once. Transfer that fact through the actual support extractor and
   ambient implementation to the cost snapshot. Reuse M234 for metadata.
3. Combine actual rule validity and active-dependent membership to prove
   membership in the computed owner list. Do not confuse an active owner with
   a unique owner.
4. Eliminate the metadata and structural-failure alternatives from a generated
   nontransparent event. Retain the remaining semantic/ownership disjunction.
5. Connect the existing total trace classifier to the canonical endpoint using
   M234's snapshot equality. Preserve the exact first event and transparent
   prefix rather than selecting an arbitrary failed event.

Stop a proposed general claim if the kernel or a concrete counterexample rejects
it. Do not weaken the claim to a fixed instance or add a correctness premise.

## Regression and validation plan

Use arbitrary-dimension applications for every public interface. Include
permanent executed regressions with empty and duplicate seeds, cycles,
competing rule/dependent owners, all metadata constructors, and physical gates.
Reject malformed raw events with absent dependents or already present required
records as purported generated events. Preserve the constant-output NAND
counterexample: unit physical growth need not force unit full-minimum growth.
Preserve the open-obligation example: cost transparency is not closure safety.

Update current declaration/name-set expectations, the explicit root, permanent
Lean regressions, axiom audits, the two reviewed-theorem producers, publication
pins, package-script contracts and durable CI in the same source change.
Check changed workflow shell blocks exactly. Run small proof and hostile
contracts before compiled inventory generation and the deduplicated complete
test union. Do not repeat unchanged successful evidence at the same boundary.

Regenerate current status, progress history, documentation and the report only
after the source and expected interfaces stabilize. Preserve immutable archive
coordinates, inherited theorem fingerprints and historical progress entries.
Run exact-head and exact-merge source-bound reproduction at their respective
release boundaries.

## Remaining obligations and publication decision

The executable observer/profile model remains supplied data. Influence and
semantic minimization are finite exhaustive reference procedures, not
polynomial constructions. An active owner need not be unique. Physical
support growth does not prove full-minimum growth, a quotient bound, obligation
discharge, mode safety or global routing. No unconditional SaturatePositive,
BCELReady, ZeroSlack, exact polynomial PCCMin, deterministic SAT theorem or
eligible root theorem is claimed.

Baseline at M234: formal artefact coverage 210 of 212 current scoped rows earned;
risk-weighted proof completion estimate 40%; uncertainty 20% to 40%; global gates
closed 0 of 5. No fixed weighted checkpoint change is anticipated.

Publication decision: defer. Keep PNPLabs at its coherent M231 publication
unless the actual mathematical result changes the public bottom line.
Continue meaningful core submilestone and release notifications independently.

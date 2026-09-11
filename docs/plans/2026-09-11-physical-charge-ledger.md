# M236 plan: exact physical-charge partition of computed saturation

This is the pre-implementation specification, not a current release verdict.
Preparation starts from the verified M235 source commit
`ad85647555e645421bea5aa70cd0f490a0648047`, tree
`4a031614cd84758e0f4d73278de67a710649f816`.
Re-anchor to its actual merge and finish the parent release verification before
publishing M236. Preserve M235's source, theorem types and publication pins.

## Manuscript anchor and missing edge

The manuscript pinned by [the archive manifest](../../archive/legacy-v0/ARCHIVE.json)
requires computed saturation in section 3. Section 4's charge soundness uses an
exact partition of computational charges; physical NAND gates have unit weight.
RW-SaturatePositive in section 10 uses those exact physical charges alongside
separate full-minimum and quotient-cost obligations.

M235 proves freshness and active dependency context for each actual event, and
its exact unit support charge. The next edge is a whole-execution partition:
every physical gate in the actual computed saturated support occurs exactly once
in a computed charge ledger, with verifiable introduction provenance. The ledger
must be generated from the actual system and seed, not supplied by a caller.

This closes the finite path from event-level physical accounting to a complete
physical-charge partition. Materializer grouping, manuscript-wide ownership,
full-minimum growth and global routing remain downstream obligations; this is
not another fixed gate, seed or schedule-prefix milestone.

## Ownership distinction and formal diagnostic

Section 4 uses an assigned function `own_C : Ch(C) -> Own(C)`.
The existing `terminalSaturationEventOwners` instead enumerates every currently
active rule/dependent pair which could request one record. These are different
interfaces, and their cardinalities must not be conflated.

A checked diagnostic over a nonconstant NAND gate with two dependent outputs
has two active requesting pairs, while support size, full minimum and quotient
minimum each grow from zero to one. The current classifier consequently reports
`nonuniqueMaterializerOwner` despite all three numeric cost conditions holding.
The existing classifier and M235 theorems are correct under their stated
active-requester definition. The example is not a contradiction of the
manuscript's assigned-ownership function or a global proof result.

Preserve that distinction in a permanent regression. Do not weaken or replace
the existing transparency predicate, relabel its requester list as the global
ownership function, or award credit merely for choosing an arbitrary owner.

The proposed ledger records physical charge identity and introduction
provenance. A provenance value can depend on the seed and traversal; it is
explicitly not the fixed manuscript-wide ownership map. Seed charges and
generated charges must remain distinguishable.

## Computed objects and exact universal contracts

Use a new module `PNP.ResidualTerminalPhysicalChargeLedger`, importing the
verified physical-accounting module. Keep the executor, support extractor,
observer, semantic minima and old classifier unchanged.

Define:

- `TerminalPhysicalChargeProvenance`: either an inherited seed charge, or
  a generated charge carrying its actual rule and dependent record.
- `TerminalPhysicalCharge`: a physical gate identifier plus provenance.
- `terminalSaturatePhysicalCharges system seed`: the selected gates of the
  normalized initial records, followed by the physical gate insertions of the
  actual trace, with their recorded introduction provenance.
- `terminalSaturatePhysicalChargeProvenance? system seed gate`: a deterministic
  lookup in that computed ledger, returning no value exactly when the gate is
  absent from the computed saturated support.

All interfaces quantify over arbitrary finite input, gate, output and profile
dimensions, systems and seeds. Candidate size accounting additionally quantifies
over arbitrary candidates and executable candidate models.

Required theorem obligations:

1. `terminalSaturatePhysicalCharges_nodup`:
   `((terminalSaturatePhysicalCharges system seed).map
   TerminalPhysicalCharge.gate).Nodup`.

2. `terminalSaturatePhysicalCharges_complete`:
   for every physical gate `gate`,
   `gate ∈ (terminalSaturatePhysicalCharges system seed).map
   TerminalPhysicalCharge.gate ↔
   TerminalPrimitiveRecord.gate gate ∈ terminalSaturateRecords system seed`.

3. `terminalSaturatePhysicalCharges_provenance`:
   for every ledger entry, inherited provenance comes from the normalized
   initial seed, or generated provenance identifies an event in the actual
   trace with exactly that required gate, rule and dependent. The dependent
   was already active, the gate was fresh, and the recorded rule holds.
   No supplied event-validity, freshness or charge-coverage certificate is an
   input to the public theorem.

4. `terminalSaturatePhysicalChargeProvenance?_iff`:
   for every gate and provenance,
   `terminalSaturatePhysicalChargeProvenance? system seed gate =
   some provenance ↔
   { gate := gate, provenance := provenance } ∈
   terminalSaturatePhysicalCharges system seed`.
   Together with completeness, this establishes total coverage of physical
   charges and a unique returned provenance for each charge.

5. `terminalCandidateSaturatePhysicalCharges_size`:
   `(terminalSaturationCostSnapshot candidate model
   (terminalSaturateRecords
   (terminalCandidateSaturationSystem candidate model) seed)).supportSize =
   (terminalSaturatePhysicalCharges
   (terminalCandidateSaturationSystem candidate model) seed).length`.
   This is the exact unit-charge size identity for the entire computed support,
   not only a per-event equality or a supplied charge list.

Do not substitute uniqueness of a lookup implementation alone for the no-
duplicate and complete-partition theorems. Do not count proof-only metadata as
physical charges. Retain all seed gates, including ones with no generated event.

## Proof sequence

1. Use the actual trace's linked replay, valid event shape and freshness to
   derive a no-duplicate sequence of physical insertions, disjoint from the
   initial selected gates. Do not reimplement the work queue.
2. Prove the generated ledger's gate membership equals gate membership in the
   replay endpoint, then transport through M234's exact replay/closure theorem.
3. Recover introduction provenance from the real event, and derive rule,
   active-dependent and freshness evidence using M234 and M235.
4. Prove the deterministic lookup specification using the no-duplicate gate
   identity theorem, not an assumed uniqueness field.
5. Compare the complete ledger with the unchanged extractor's selected-gate
   list. Derive the exact support-size equation from their no-duplicate,
   extensional equality.

A failure of a general theorem stops its proposed credit. Do not replace it by
the fixed diagnostic, add a correctness premise, or broaden a mathematical claim.

## Verification and publication

Update source-shape expectations, reviewed theorem names, explicit root,
strict axiom audit, permanent regression, fingerprint producers and consumers,
status fields, package-script contract and durable workflow together.
Run focused checks before inventory generation and the full deduplicated suite.

The consumer preflight is:

| Producer | Consumers to update together | First check |
| --- | --- | --- |
| New ledger module and five general interfaces | New source contracts, permanent arbitrary-dimension/hostile Lean regression, explicit root and strict axiom audit | Exact new module build, source-shape rejection cases, then imported regression/audit |
| Reviewed theorem-name set | Lean inventory producer, JavaScript required names, publication row and fingerprint-key set | Name-set comparison before compiled inventory |
| New npm audit script | Closed package-script fixture and durable verification test list | Focused public package-script contract |
| New earned status fields and coordinate | Both exact status contracts, every boolean-mutation list, generator coordinates and publication-map validator | Current/hostile status and publication tests |
| Actual compiled hashes and generated status | Canonical/public mirrors, progress history, current docs and generated report | Structured field delta, new compiled hostile tests and generator check |
| Added durable shell blocks | Exact extracted workflow script and its prerequisites | Remote shell syntax check, then execute that exact block |

Permanent regressions must exercise inherited seed gates, multiple generated
gates, repeated seeds, cyclic dependencies, metadata-only and empty traces,
several requesters for one gate, and absent-gate lookup. Include arbitrary-
dimension applications of every public interface. Keep the nonconstant
two-requester cost diagnostic separate from general theorem credit.

After source and expectations stabilize, regenerate the current canonical
status, progress history, documentation and report. Preserve all historical
rows and pins. Reuse unchanged exact-source evidence; do not run a second
complete core proof suite merely for a website boundary. Complete independent
exact-head and exact-merge source-bound release checks.

## Explicit remaining limits

This is a computed physical-NAND charge partition and provenance ledger.
It does not construct the complete manuscript charge universe, group charged
materializers, prove cross-support ownership transport, or establish
`own_C` for all computational profile objects. Several charge entries may
share a requesting dependency; unique charge identity does not mean every
requester owns at most one gate.

The observer/profile model remains supplied. Reference influence and semantic
minimization remain exhaustive. No complete encoded-size polynomial theorem,
full-minimum growth, unconditional SaturatePositive, BCELReady, ZeroSlack,
global routing, exact polynomial PCCMin, deterministic SAT theorem or eligible
root theorem is earned by this ledger alone.

Baseline M235: formal artefact coverage 211 of 213 current scoped rows earned;
risk-weighted proof completion estimate 40%; uncertainty 20% to 40%; global gates
closed 0 of 5. No fixed weighted checkpoint change is anticipated.

Publication decision: defer. Keep PNPLabs at its coherent M231 source pin until
a major result changes the public bottom line. Continue meaningful core
submilestone and release notifications independently.

## Integration provenance

The working branch was fast-forwarded to the actual M235 merge
`64af7f4c0661bfa07e4acf574518d01b2748b52b`, whose tree is the identical
`4a031614cd84758e0f4d73278de67a710649f816` used for preparation.
M235's post-merge verification remains a release prerequisite for publishing
M236; no feature-tip coordinate substitutes for the parent merge.

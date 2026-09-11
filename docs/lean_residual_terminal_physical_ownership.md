# Support-independent physical ownership and exact materializer charges

M241 assigns physical gates before any support is chosen and derives charges
from actual extracted NAND candidates. Arbitrary overlaps, repeated requests
and unrequested gates are covered by one general construction, without
supplied partition proofs or numerical weights.

## Construction and exact identity

The [ownership module](../lean/PNP/ResidualTerminalPhysicalOwnership.lean)
takes raw finite requests `Fin ownerCount -> List (Fin gates)`.
`terminalPhysicalOwner` chooses the first requesting owner in canonical
finite-index order. No request means the fixed remainder `none`.
The owner assignment takes no support, seed or insertion trace.

For any terminal record list, `terminalOwnedPhysicalGates` restricts this
ambient assignment to the canonically selected physical gates.
`terminalOwnedPhysicalRecords` maps them back to gate records, and
`terminalOwnedPhysicalMaterializer` uses the existing physical support
extractor. Its weight is the actual extracted NAND gate count.

```text
((terminalPhysicalOwners ownerCount).map (fun owner =>
  (terminalOwnedPhysicalMaterializer candidate requests records owner).gateCount)).sum
  = (extractTerminalSupport candidate records).gateCount
```

The ten arbitrary-dimension interfaces are:

- `terminalPhysicalOwner_none_iff`: the fixed remainder contains exactly
  the gates no owner requests.
- `terminalPhysicalOwner_first`: a named owner requests the gate and no
  earlier canonical owner does.
- `terminalOwnedPhysicalGates_partition`: exact selected-gate and assigned-owner
  membership, covering every selected gate.
- `terminalOwnedPhysicalGates_disjoint`: distinct buckets cannot double-charge
  a physical gate.
- `terminalOwnedPhysicalGates_restrict`: support restriction cannot reassign
  a retained gate.
- `terminalOwnedPhysicalMaterializer_gateCount`: each charge equals the actual
  extracted physical gate count.
- `terminalOwnedPhysicalMaterializer_chargeIdentity`: exact total cost for
  every finite support and raw request family.
- `terminalOwnedPhysicalMaterializer_semantics`: complete open semantics of
  every extracted piece for arbitrary boundary valuations.
- `terminalOwnedPhysicalMaterializer_induced`: induced boundary values recover
  the original circuit's ordered interface gate values.
- `terminalOwnedPhysicalMaterializer_wholeCharge`: the complete circuit's
  physical charge total is exactly its number of gates.

Duplicates are removed by canonical physical gate selection. Overlaps resolve
to the first requester, and uncovered gates remain charged in the remainder.
Boundary, interface and profile metadata do not become physical NAND gates.
Different pieces may exchange computed values through their derived physical
boundaries; this does not make those values free primary inputs in the whole
circuit.

## Manuscript linkage and claim boundary

The [plan](plans/2026-09-12-support-independent-physical-ownership.md) records
the pinned [manuscript](../archive/legacy-v0/ARCHIVE.json) section 4
ChargeSoundness dependency and section 2.2 open-support semantics.
M236's insertion provenance depends on the seed. This assignment is fixed
before support selection, closing a physical ownership/cost partition edge
without confusing insertion history with ambient ownership.

This is a support-independent physical ownership and charge partition kernel,
not the complete manuscript computational-record universe or proof of
admissible materializer ownership. The raw finite request family is supplied
data. A canonical assignment does not discharge unique active ownership,
carrier, frontier or obligation conditions.

The existing production nonunique-owner rejection is unchanged. In particular,
two active materializer requesters can still make a saturation event fail
transparency even though the physical partition chooses one canonical owner.
No assumption of disjoint or exhaustive requests is hidden in the theorem.

The result does not establish HN assembly, forced full-profile minimum growth,
quotient bounds, terminal-family derivation or complete rank-decreasing routes.
M240's independent forced-cost theorem remains a separate physical subcase.
Reference minima remain exhaustive finite constructions, not a polynomial-time
algorithm. Neither finiteness nor this exact charge sum proves complete PCCMin
runtime or encoded-size bounds.

## Regression and assumption evidence

The [permanent regressions](../lean-regression/PNPResidualTerminalPhysicalOwnership.lean)
apply all ten interfaces at arbitrary dimensions. Small cases include zero
owners, zero gates, empty supports, overlapping and duplicated requests,
uncovered gates, metadata-only records and reordered/repeated gate records.
A cross-owner dependency checks derived boundaries and induced semantics.

A general regression proves that assigning a canonical owner does not
override the existing ambiguous-active-owner rejection. A bounded execution
check confirms exact piece counts and the empty-support case.
Runtime execution is test evidence, not theorem authority. No exhaustive
semantic-minimum evaluation is needed for this partition result.

The [explicit-root axiom audit](../lean-audit/PNPResidualTerminalPhysicalOwnershipAxiomAudit.lean)
checks all ten interfaces. Partition membership, disjointness and restriction
use only `propext`; the other seven use only `propext` and `Quot.sound`.
No project-specific axiom, classical choice or native-execution proof
authority is introduced.

The [source and compiled contracts](../audits/lean-residual-terminal-physical-ownership0.test.mjs)
reject support-dependent ownership, supplied partition authority, fixed-instance
or weakened types, dropped remainder charges, guessed weights, metadata
charges, incorrect extraction, assumption-backed declarations and exact
compiled-type drift.

## Remaining proof burden and progress

Complete admissible materializers, obligation discharge and global routing
remain open. No unconditional SaturatePositive, BCELReady or ZeroSlack,
complete polynomial PCCMin, deterministic CNFSAT in P or eligible root follows.
The publication gate remains false. No fixed checkpoint or global gate closes.

Formal artefact coverage: 217 of 219 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

Both measures come from the [canonical progress ledger](../status/PROOF_PROGRESS.json).
Neither is confidence that `P = NP` is true, a probability of success or a
time-remaining estimate.

Publication decision: defer. Preserve the coherent M231 PNPLabs source pin.
This internal partition kernel alone does not change the published global
bottom line. Meaningful verified core submilestone and release notifications
continue independently.

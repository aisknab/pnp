# M186 concrete legacy locked-NAND compatibility

## Evidence-led selection

The checked all-bitstring theorem `PNP.Main.locked_nand_threshold` already
constructs a polynomial reduction from concrete `CNFSAT` to the concrete
`EncodedLockedNANDThreshold` predicate.  The report-facing bridge still does
not consume that theorem: `PNP.Complexity` indexes string-only witness records
by name-only language handles, `PNP.LockedNANDThreshold` is a project axiom,
and `CheckerTrustModel` asks callers to supply a second abstract locked-NAND
reduction.  This leaves a genuine compatibility gap even though the concrete
reduction itself is compiled and audited.

M186 removes that duplicate abstract trust edge.  The report-facing
complexity API will reuse the existing concrete finite-pipeline language,
decider, verifier, reduction, and class definitions.  Its `SAT` and
locked-NAND endpoints will be definitionally the checked concrete `CNFSAT`
and `EncodedLockedNANDThreshold` predicates.  The bridge will consume the
existing concrete reduction theorem directly rather than a caller field.

## Legacy anchor and unbounded abstraction

- Legacy anchor: the pinned manuscript's locked-NAND SAT embedding and final
  complexity transport, Sections 17--19 and the `G.LockedNANDThreshold`
  dependency in the final bridge.
- Closed edge: concrete all-bitstring `CNFSAT`-to-locked-NAND polynomial
  reduction -> report-facing SAT/locked-NAND compatibility -> removal of the
  duplicate project axiom and caller-supplied reduction field.
- Unbounded abstraction: arbitrary bitstring inputs and arbitrary concrete
  languages in the existing finite-pipeline P, NP, and polynomial-reduction
  interfaces.  No fixed circuit, input, formula, token, or schedule position
  is used.

## Exact theorem target

Make `PNP.Language`, `PClass`, `NPClass`, `ReducesToPoly`, and `PEqualsNP`
compatibility names for their already-checked `PNP.Concrete` counterparts.
Define:

```text
PNP.SAT = PNP.Concrete.CNFSAT
PNP.LockedNANDThreshold =
  PNP.Concrete.LockedNAND.EncodedLockedNANDThreshold
```

Then prove, without a premise:

```text
PNP.sat_reduces_to_locked_nand_checked :
  ReducesToPoly SAT LockedNANDThreshold
```

by reusing `PNP.Main.locked_nand_threshold`.  Refactor
`sat_in_p_from_locked_nand_in_p` and `CheckerTrustModel` so the active bridge
uses this theorem and no longer accepts `lockedNANDReduction` as caller trust.
Reuse the compiled concrete `CNFSAT ∈ NP` verifier for the report-facing SAT
membership theorem.

## Claim boundary and downstream blockers

M186 does not provide a locked-NAND decider, residual-band reduction,
PCCMin/ZeroSlack soundness, concrete SAT NP-hardness, checker reflection,
project-package generation or checking, the eligible root theorem, or
`P = NP`.  `PNP.ResidualBandExactMinimization`, `PNP.GeneratePCCPack`, and
`PNP.CheckPCCPackexp` remain project-specific assumptions.  The concrete SAT
global gate remains open because NP-hardness and a deterministic decider are
still absent.

This closes two existing fixed checkpoints only: final concrete
SAT-to-target compatibility in the reductions track and removal of
`PNP.LockedNANDThreshold` from the project-axiom closure.  The risk-weighted
score changes from 30 to 32 percent; the 20--40 percent uncertainty range does
not change.  Formal artefact coverage advances only through the new M186
publication row.

## Required evidence

- focused Lean compilation and axiom transcripts for the compatibility API,
  SAT layer, locked-NAND layer, bridge, and root import;
- regression proving the exact language identities, concrete reduction
  reuse, concrete SAT verifier reuse, and three-field checker trust boundary;
- hostile checks rejecting a restored name-only language structure, a
  project axiom for `LockedNANDThreshold`, string-only complexity witnesses,
  a caller-supplied locked-NAND reduction field, or widened final claims;
- compiled theorem-inventory and formal-status updates showing three project
  axioms, the absent eligible root, and the still-false publication gate;
- a fixed-checkpoint score transition recording both checkpoint IDs, exact
  compiled evidence, remaining limitations, old/new totals, and unchanged
  uncertainty; and
- complete core and PNPLabs publication, review, clean-merge reproduction,
  deployment, provenance, route, and service verification gates.

## Verification and deduplication

Run source-contract checks first.  Compile changed Lean dependencies and the
root once on the capped remote builder, then run focused regression and axiom
audits.  After stabilization, regenerate the inventory, progress ledger, and
publication artifacts and run the complete core suite once.  PNPLabs consumes
the exact merged core artifacts and validates publication and production
surfaces without rebuilding the already-verified Lean project.

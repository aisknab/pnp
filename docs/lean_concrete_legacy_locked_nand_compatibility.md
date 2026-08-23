# Concrete report-facing locked-NAND compatibility

M186 removes a duplicate trust boundary between the report-facing bridge and
the already checked finite-pipeline SAT-to-locked-NAND reduction.

## What is now exact

`PNP.Language`, the proof-bearing decider and verifier interfaces, polynomial
many-one reductions, `PClass`, `NPClass`, and `PEqualsNP` are compatibility
names for their `PNP.Concrete` counterparts. In the same model:

- `PNP.SAT` is definitionally `PNP.Concrete.CNFSAT`;
- `PNP.LockedNANDThreshold` is definitionally
  `PNP.Concrete.LockedNAND.EncodedLockedNANDThreshold`;
- `PNP.satVerifierWitness` reuses the compiled concrete CNF verifier;
- `PNP.sat_reduces_to_locked_nand_checked` reuses
  `PNP.Main.locked_nand_threshold`; and
- the active bridge derives SAT membership in P from target membership in P
  without accepting a separate locked-NAND reduction trust field.

The named endpoint
`PNP.concrete_legacy_locked_nand_compatibility_checked_complete` packages the
two exact language identities, concrete NP membership, the all-bitstring
polynomial reduction, and the resulting deterministic-P transport. Its
compiled axiom closure contains only `propext` and `Quot.sound`.

`PNP.LockedNANDThreshold` is now a definition rather than project-specific
proof authority. The compiled inventory therefore retains three
project-specific axioms: `PNP.GeneratePCCPack`, `PNP.CheckPCCPackexp`, and
`PNP.ResidualBandExactMinimization`.

## What this does not prove

M186 does not construct a deterministic polynomial-time decider for the
locked-NAND target, a residual-band reduction, PCCMin or ZeroSlack soundness,
concrete SAT NP-hardness, the complete Cook--Levin formula builder, or the
eligible root theorem `PNP.Main.p_eq_np`. All five global gates remain open and
the publication gate remains false.

The canonical fixed-checkpoint ledger records two one-point changes:
`reductions-final-target-compatibility` and
`axiom-remove-locked-nand-threshold`. This moves the risk-weighted estimate
from 30 to 32 percent without changing the 20-to-40-percent uncertainty range.
Formal artefact coverage changes independently to 162 of 164 current scoped
rows.

## Verification surfaces

- Source: `lean/PNP/ConcreteLegacyLockedNANDCompatibility.lean`
- Axiom transcript:
  `lean-audit/PNPConcreteLegacyLockedNANDCompatibilityAxiomAudit.lean`
- Regression:
  `lean-regression/PNPConcreteLegacyLockedNANDCompatibility.lean`
- Hostile contract:
  `audits/lean-concrete-legacy-locked-nand-compatibility0.test.mjs`
- Progress authority: `status/PROOF_PROGRESS.json`

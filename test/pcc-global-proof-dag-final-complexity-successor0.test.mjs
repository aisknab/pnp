import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from '../pcc-global-proof-dag0.mjs';

import {
  makeGlobalFinalPrefixSemanticSuite0,
} from '../pcc-global-final-prefix-semantic0.mjs';

import {
  makeGlobalFinalSATReductionSemanticSuite0,
} from '../pcc-global-final-sat-reduction-semantic0.mjs';

import {
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  makeGlobalFinalComplexitySemanticSuite0,
} from '../pcc-global-final-complexity-semantic0.mjs';

import {
  CheckGlobalProofDAGFinalComplexityFinalTheoremReadiness0,
  CheckGlobalProofDAGFinalComplexitySuccessor0,
  makeGlobalProofDAGFinalComplexitySuccessor0,
} from '../pcc-global-proof-dag-final-complexity-successor0.mjs';

import {
  STANDARD_COMPLEXITY_BASIS0,
} from '../pcc-complexity-bridge0.mjs';

import {
  makeFinalPrefixSurfaces0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

function makeCheckFinalAcceptedSurfaces0() {
  const surfaces = makeFinalPrefixSurfaces0();
  const finalTheorem = {
    ...surfaces.PCCPack.FinalTheorem,
    NoHiddenMinCert: {
      ...surfaces.PCCPack.FinalTheorem.NoHiddenMinCert,
      occurrences: surfaces.PCCPack.FinalTheorem.NoHiddenMinCert.occurrences
        .map((entry) => (
          entry.identifier === 'PCCMin'
            ? { ...entry, occurrenceClass: 'AssumeOnly' }
            : entry
        )),
    },
  };
  const PCCPack = {
    ...surfaces.PCCPack,
    FinalTheorem: finalTheorem,
    RowFamFinal: {
      ...surfaces.PCCPack.RowFamFinal,
      FinalTheorem: finalTheorem,
    },
  };
  const FinalPrefixSemanticDerivations = makeGlobalFinalPrefixSemanticSuite0({
    LegacyGlobalProofDAG: surfaces.LegacyGlobalProofDAG,
    PCCPack,
  });
  const SATReductionSemanticDerivations =
    makeGlobalFinalSATReductionSemanticSuite0({
      LegacyGlobalProofDAG: surfaces.LegacyGlobalProofDAG,
      PCCPack,
    });
  return {
    ...surfaces,
    PCCPack,
    FinalPrefixSemanticDerivations,
    SATReductionSemanticDerivations,
  };
}

function makeInput0({ Purpose = 'development' } = {}) {
  const surfaces = makeCheckFinalAcceptedSurfaces0();
  return makeGlobalProofDAGFinalComplexitySuccessor0({
    ...surfaces,
    ComplexityBasis: STANDARD_COMPLEXITY_BASIS0,
    ComplexitySemanticDerivations:
      makeGlobalFinalComplexitySemanticSuite0({
        LegacyGlobalProofDAG: surfaces.LegacyGlobalProofDAG,
        PCCPack: surfaces.PCCPack,
        SATReductionSemanticDerivations:
          surfaces.SATReductionSemanticDerivations,
        ComplexityBasis: STANDARD_COMPLEXITY_BASIS0,
      }),
    Purpose,
  });
}

test('final complexity successor completes bounded final coverage but keeps all final nodes quarantined', async () => {
  const out = await CheckGlobalProofDAGFinalComplexitySuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAGFinalComplexitySuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorGlobalSATReductionReady, true);
  assert.equal(out.NF.predecessorGlobalComplexityReady, false);
  assert.equal(out.NF.globalFinalComplexitySemanticReady, true);
  assert.equal(out.NF.globalFinalComplexityImplicationRefinementReady, true);
  assert.equal(out.NF.globalFinalComplexityImplicationReady, true);
  assert.equal(out.NF.allGlobalFinalCoordinatesBoundedRefined, true);
  assert.equal(out.NF.guardedComplexityRefinementOnly, true);
  assert.equal(out.NF.unrestrictedFinalSoundnessReady, false);
  assert.equal(out.NF.globalFinalDerivationsReady, false);

  assert.deepEqual(
    out.NF.semanticOverlay.semanticFinalComplexityNodeIds,
    [GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
  );
  assert.deepEqual(out.NF.semanticOverlay.blockedFinalNodeIds, []);
  assert.equal(
    out.NF.semanticOverlay.semanticNodeIds.includes(
      GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    ),
    true,
  );
  assert.deepEqual(out.NF.computedGlobalGate.blockerCoordinates, [
    'GlobalDAG.UnrestrictedFinalSoundness',
  ]);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.deepEqual(out.NF.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('final complexity successor rejects final purpose while unrestricted soundness is blocked', async () => {
  const out = await CheckGlobalProofDAGFinalComplexitySuccessor0(
    makeInput0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFinalComplexitySuccessor0.semanticReadiness',
  );
  assert.deepEqual(out.Path, ['ComputedGlobalGate']);
  assert.equal(out.Witness.blockers.filter((entry) => !entry.ready).length, 1);
  assert.deepEqual(out.Witness.remainingBlockedFinalNodeIds, []);
  assert.deepEqual(out.Witness.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0);
});

test('explicit final complexity readiness gate rejects a development-purpose record', async () => {
  const out = await CheckGlobalProofDAGFinalComplexityFinalTheoremReadiness0(
    makeInput0(),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckGlobalProofDAGFinalComplexityFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
});

test('final complexity successor rejects caller-supplied readiness assertions', async () => {
  const input = makeInput0();
  input.unrestrictedFinalSoundnessReady = true;
  const out = await CheckGlobalProofDAGFinalComplexitySuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalComplexitySuccessor0.input');
  assert.deepEqual(out.Path, ['unrestrictedFinalSoundnessReady']);
});

test('final complexity overlay binds the complexity node to the checked derivation', async () => {
  const out = await CheckGlobalProofDAGFinalComplexitySuccessor0(makeInput0());

  assert.equal(out.tag, 'accept');
  const binding = out.NF.semanticOverlay.semanticFinalComplexityBinding;
  const derivation = out.NF.complexityDerivation;
  assert.equal(binding.nodeId, GLOBAL_FINAL_COMPLEXITY_NODE_ID0);
  assert.equal(binding.derivationDigest.hex, derivation.derivationDigest.hex);
  assert.equal(binding.globalNodeDigest.hex, derivation.globalNodeDigest.hex);
  assert.equal(
    binding.dependencyDerivationDigest.hex,
    derivation.dependencyDerivationDigest.hex,
  );
  assert.equal(
    binding.complexityBasisDigest.hex,
    derivation.complexityBasisDigest.hex,
  );
  assert.equal(
    binding.complexityBridgeRecordDigest.hex,
    derivation.complexityBridgeRecordDigest.hex,
  );
  assert.equal(binding.publiclyActive, false);
});

import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckFinal0 } from '../pcc-final0.mjs';

import {
  makeGlobalFinalPrefixSemanticSuite0,
} from '../pcc-global-final-prefix-semantic0.mjs';

import {
  makeGlobalFinalSATReductionSemanticSuite0,
} from '../pcc-global-final-sat-reduction-semantic0.mjs';

import {
  CheckGlobalFinalComplexitySemantic0,
  makeGlobalFinalComplexitySemanticInput0,
  makeGlobalFinalComplexitySemanticSuite0,
} from '../pcc-global-final-complexity-semantic0.mjs';

import {
  STANDARD_COMPLEXITY_BASIS0,
} from '../pcc-complexity-bridge0.mjs';

import {
  makeFinalPrefixSurfaces0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

function makeSurfaces0() {
  const surfaces = makeFinalPrefixSurfaces0();
  const finalTheorem = {
    ...surfaces.PCCPack.FinalTheorem,
    NoHiddenMinCert: {
      ...surfaces.PCCPack.FinalTheorem.NoHiddenMinCert,
      occurrences: surfaces.PCCPack.FinalTheorem.NoHiddenMinCert.occurrences.map(
        (entry) => (entry.identifier === 'PCCMin'
          ? { ...entry, occurrenceClass: 'AssumeOnly' }
          : entry),
      ),
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

function compact0(record) {
  return JSON.stringify({
    coord: record.Coord,
    path: record.Path,
    witness: record.Witness,
  });
}

test('diagnose CheckFinal0 acceptance for phase 39 fixture', async () => {
  const surfaces = makeSurfaces0();
  const record = await CheckFinal0(surfaces.PCCPack.FinalTheorem);
  assert.equal(record.tag, 'accept', compact0(record));
});

test('diagnose final complexity semantic acceptance for phase 39 fixture', async () => {
  const surfaces = makeSurfaces0();
  const input = makeGlobalFinalComplexitySemanticInput0({
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
  });
  const record = await CheckGlobalFinalComplexitySemantic0(input);
  assert.equal(record.tag, 'accept', compact0(record));
});

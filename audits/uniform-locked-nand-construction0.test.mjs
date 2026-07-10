import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  BuildLockedNANDConstruction0,
  CheckUniformLockedNANDConstruction0,
  NormalizeLockedNANDInput0,
} from '../pcc-uniform-locked-nand-construction0.mjs';

async function currentManifest() {
  return JSON.parse(await readFile(new URL('../proof-obligations/UNIFORM_LOCKED_NAND_CONSTRUCTION.json', import.meta.url), 'utf8'));
}

test('uniform locked NAND construction checker accepts the current construction surface', async () => {
  const out = await CheckUniformLockedNANDConstruction0({ historicalReplay: true, writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-UNIFORM-LOCKED-NAND-CONSTRUCTION-2026-07-04-01');
  assert.equal(out.ufsObligationId, 'UFS-002-LockedNANDConstructionUniformPolynomial');
  assert.equal(out.lockedNANDConstructionAccepted, true);
  assert.equal(out.ufs002LockedNANDConstructionDischarged, true);
  assert.equal(out.totalOnInputFamily, true);
  assert.equal(out.uniformAcrossSizes, true);
  assert.equal(out.finiteInstanceList, false);
  assert.equal(out.boundedEnumerationOnly, false);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});

test('locked NAND builder computes the one-gate example baseline exactly', () => {
  const circuit = {
    kind: 'NANDCircuit0',
    version: 0,
    inputCount: 2,
    gates: [
      { op: 'NAND', left: { kind: 'input', index: 0 }, right: { kind: 'input', index: 1 } },
    ],
    output: { kind: 'gate', index: 0 },
  };
  const out = BuildLockedNANDConstruction0(circuit);
  assert.equal(out.tag, 'accept');
  assert.equal(out.normalizedGateCount, 1);
  assert.equal(out.equalityMacroCount, 2);
  assert.equal(out.traceMacroCount, 1);
  assert.equal(out.prefixNodeCount, 2);
  assert.equal(out.baseline, 42);
  assert.equal(out.fullWordSize, 46);
  assert.equal(out.residualSlackBound, 4);
});

test('locked NAND builder normalizes input-output circuits uniformly', () => {
  const circuit = {
    kind: 'NANDCircuit0',
    version: 0,
    inputCount: 1,
    gates: [],
    output: { kind: 'input', index: 0 },
  };
  const normalized = NormalizeLockedNANDInput0(circuit);
  assert.equal(normalized.tag, 'accept');
  assert.equal(normalized.addedGateCount, 2);
  assert.equal(normalized.normalizedCircuit.gates.length, 2);
  assert.deepEqual(normalized.normalizedCircuit.output, { kind: 'gate', index: 1 });

  const out = BuildLockedNANDConstruction0(circuit);
  assert.equal(out.tag, 'accept');
  assert.equal(out.normalizedGateCount, 2);
  assert.equal(out.equalityMacroCount, 3);
  assert.equal(out.constantOneMacroCount, 1);
  assert.equal(out.baseline, 78);
  assert.equal(out.fullWordSize, 82);
});

test('locked NAND builder rejects inputs outside UFS-001 input family', () => {
  const out = BuildLockedNANDConstruction0({
    kind: 'NANDCircuit0',
    version: 0,
    inputCount: 1,
    gates: [],
    output: { kind: 'input', index: 4 },
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformInputFamily.SourceInputOutOfRange');
});

test('uniform locked NAND checker rejects finite-list-only construction overclaim', async () => {
  const manifest = await currentManifest();
  manifest.construction.finiteInstanceList = true;
  manifest.construction.uniformAcrossSizes = false;
  const out = await CheckUniformLockedNANDConstruction0({ historicalReplay: true, writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformLockedNANDConstruction.ConstructionBoolean');
});

test('uniform locked NAND checker rejects theorem activation by construction alone', async () => {
  const manifest = await currentManifest();
  manifest.uniformFinalSoundnessProved = true;
  const out = await CheckUniformLockedNANDConstruction0({ historicalReplay: true, writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformLockedNANDConstruction.BooleanField');
  assert.deepEqual(out.path, ['uniformFinalSoundnessProved']);
});

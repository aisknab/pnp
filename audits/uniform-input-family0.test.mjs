import assert from 'node:assert/strict';
import { test } from 'node:test';
import { readFile } from 'node:fs/promises';

import {
  CheckNANDCircuitInputFamilyMember0,
  CheckUniformInputFamily0,
} from '../pcc-uniform-input-family0.mjs';

async function currentManifest() {
  return JSON.parse(await readFile(new URL('../proof-obligations/UNIFORM_INPUT_FAMILY.json', import.meta.url), 'utf8'));
}

test('uniform input family checker accepts the current all-size NAND input schema', async () => {
  const out = await CheckUniformInputFamily0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-UNIFORM-INPUT-FAMILY-2026-07-04-01');
  assert.equal(out.ufsObligationId, 'UFS-001-InputFamilyUniformity');
  assert.equal(out.inputFamilyUniformityAccepted, true);
  assert.equal(out.ufs001InputFamilyUniformityDischarged, true);
  assert.equal(out.allFiniteSizesCovered, true);
  assert.equal(out.schemaUniformAcrossSizes, true);
  assert.equal(out.finiteInstanceList, false);
  assert.equal(out.boundedEnumerationOnly, false);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});

test('NANDCircuit0 member checker accepts arbitrary topological finite circuits', () => {
  const circuit = {
    kind: 'NANDCircuit0',
    version: 0,
    inputCount: 3,
    gates: [
      { op: 'NAND', left: { kind: 'input', index: 0 }, right: { kind: 'input', index: 1 } },
      { op: 'NAND', left: { kind: 'gate', index: 0 }, right: { kind: 'const', value: 1 } },
      { op: 'NAND', left: { kind: 'gate', index: 1 }, right: { kind: 'input', index: 2 } },
    ],
    output: { kind: 'gate', index: 2 },
  };
  const out = CheckNANDCircuitInputFamilyMember0(circuit);
  assert.equal(out.tag, 'accept');
  assert.equal(out.gateCount, 3);
});

test('NANDCircuit0 member checker rejects future gate references', () => {
  const circuit = {
    kind: 'NANDCircuit0',
    version: 0,
    inputCount: 1,
    gates: [
      { op: 'NAND', left: { kind: 'gate', index: 0 }, right: { kind: 'input', index: 0 } },
    ],
    output: { kind: 'gate', index: 0 },
  };
  const out = CheckNANDCircuitInputFamilyMember0(circuit);
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformInputFamily.SourceFutureGate');
});

test('uniform input family checker rejects finite-list-only overclaim', async () => {
  const manifest = await currentManifest();
  manifest.inputFamily.finiteInstanceList = true;
  manifest.inputFamily.allFiniteSizesCovered = false;
  const out = await CheckUniformInputFamily0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformInputFamily.FamilyBoolean');
});

test('uniform input family checker rejects theorem activation by input-family proof alone', async () => {
  const manifest = await currentManifest();
  manifest.uniformFinalSoundnessProved = true;
  const out = await CheckUniformInputFamily0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformInputFamily.BooleanField');
  assert.deepEqual(out.path, ['uniformFinalSoundnessProved']);
});

test('uniform input family checker rejects bounded enumeration only', async () => {
  const manifest = await currentManifest();
  manifest.inputFamily.boundedEnumerationOnly = true;
  const out = await CheckUniformInputFamily0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformInputFamily.FamilyBoolean');
});

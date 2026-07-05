import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  BruteForceNANDSat0,
  CheckLockedNANDThresholdExample0,
  CheckUniformLockedNANDThreshold0,
  EvaluateNANDCircuit0,
} from '../pcc-uniform-locked-nand-threshold0.mjs';

async function currentManifest() {
  return JSON.parse(await readFile(new URL('../proof-obligations/UNIFORM_LOCKED_NAND_THRESHOLD.json', import.meta.url), 'utf8'));
}

test('uniform locked NAND threshold checker accepts current threshold surface', async () => {
  const out = await CheckUniformLockedNANDThreshold0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-UNIFORM-LOCKED-NAND-THRESHOLD-2026-07-04-01');
  assert.equal(out.ufsObligationId, 'UFS-003-ThresholdEquivalenceAllInputs');
  assert.equal(out.lockedNANDThresholdAccepted, true);
  assert.equal(out.ufs003ThresholdEquivalenceDischarged, true);
  assert.equal(out.allFiniteInputsCovered, true);
  assert.equal(out.thresholdEquivalenceParametric, true);
  assert.equal(out.residualSlackBound, 4);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});

test('NAND evaluator and example threshold helper classify constant-zero as unsat', () => {
  const circuit = { kind: 'NANDCircuit0', version: 0, inputCount: 0, gates: [], output: { kind: 'const', value: 0 } };
  assert.deepEqual(EvaluateNANDCircuit0(circuit, []).value, 0);
  assert.deepEqual(BruteForceNANDSat0(circuit), { tag: 'accept', satisfiable: false, witness: null });
  const out = CheckLockedNANDThresholdExample0(circuit);
  assert.equal(out.tag, 'accept');
  assert.equal(out.satisfiable, false);
  assert.equal(out.baseline, 26);
  assert.equal(out.fullWordSize, 30);
  assert.equal(out.muEqualsBaselineInUnsatCase, true);
  assert.equal(out.thresholdPredicate, false);
  assert.equal(out.residualSlackBound, 4);
});

test('NAND evaluator and example threshold helper classify constant-one as sat', () => {
  const circuit = { kind: 'NANDCircuit0', version: 0, inputCount: 0, gates: [], output: { kind: 'const', value: 1 } };
  const out = CheckLockedNANDThresholdExample0(circuit);
  assert.equal(out.tag, 'accept');
  assert.equal(out.satisfiable, true);
  assert.equal(out.baseline, 28);
  assert.equal(out.fullWordSize, 32);
  assert.equal(out.muLowerBoundInSatCase, 29);
  assert.equal(out.muUpperBoundInSatCase, 32);
  assert.equal(out.thresholdPredicate, true);
  assert.equal(out.residualSlackBound, 4);
});

test('NAND evaluator and example threshold helper classify two-input NAND as sat', () => {
  const circuit = {
    kind: 'NANDCircuit0',
    version: 0,
    inputCount: 2,
    gates: [{ op: 'NAND', left: { kind: 'input', index: 0 }, right: { kind: 'input', index: 1 } }],
    output: { kind: 'gate', index: 0 },
  };
  assert.equal(EvaluateNANDCircuit0(circuit, [1, 1]).value, 0);
  assert.equal(EvaluateNANDCircuit0(circuit, [1, 0]).value, 1);
  const out = CheckLockedNANDThresholdExample0(circuit);
  assert.equal(out.tag, 'accept');
  assert.equal(out.satisfiable, true);
  assert.equal(out.baseline, 42);
  assert.equal(out.fullWordSize, 46);
  assert.equal(out.residualSlackBound, 4);
});

test('uniform threshold checker rejects finite-list-only theorem overclaim', async () => {
  const manifest = await currentManifest();
  manifest.thresholdTheorem.finiteInstanceList = true;
  manifest.thresholdTheorem.allFiniteInputsCovered = false;
  const out = await CheckUniformLockedNANDThreshold0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformLockedNANDThreshold.TheoremBoolean');
});

test('uniform threshold checker rejects theorem activation by threshold proof alone', async () => {
  const manifest = await currentManifest();
  manifest.uniformFinalSoundnessProved = true;
  const out = await CheckUniformLockedNANDThreshold0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformLockedNANDThreshold.BooleanField');
  assert.deepEqual(out.path, ['uniformFinalSoundnessProved']);
});

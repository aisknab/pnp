import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckResidualBandMinimizerExample0,
  CheckUniformResidualBandMinimizer0,
} from '../pcc-uniform-residual-band-minimizer0.mjs';

async function currentManifest() {
  return JSON.parse(await readFile(new URL('../proof-obligations/UNIFORM_RESIDUAL_BAND_MINIMIZER.json', import.meta.url), 'utf8'));
}

test('uniform residual-band minimizer checker accepts current minimizer surface', async () => {
  const out = await CheckUniformResidualBandMinimizer0({ historicalReplay: true, writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-UNIFORM-RESIDUAL-BAND-MINIMIZER-2026-07-05-01');
  assert.equal(out.ufsObligationId, 'UFS-004-ResidualBandMinimizerUniformPolynomial');
  assert.equal(out.residualBandMinimizerAccepted, true);
  assert.equal(out.ufs004ResidualBandMinimizerDischarged, true);
  assert.equal(out.totalOnThresholdInstances, true);
  assert.equal(out.uniformAcrossSizes, true);
  assert.equal(out.returnsExactMinimum, true);
  assert.equal(out.residualSlackBoundRequired, 4);
  assert.equal(out.maxGainIterationsForLockedInstances, 4);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});

test('residual-band minimizer example summary classifies constant-zero as exact baseline', () => {
  const out = CheckResidualBandMinimizerExample0({ kind: 'NANDCircuit0', version: 0, inputCount: 0, gates: [], output: { kind: 'const', value: 0 } });
  assert.equal(out.tag, 'accept');
  assert.equal(out.thresholdDecision, false);
  assert.equal(out.baseline, 26);
  assert.equal(out.fullWordSize, 30);
  assert.equal(out.minimumRelationToBaseline, 'equal');
  assert.equal(out.exactMinimumSize, 26);
  assert.equal(out.maxGainIterations, 4);
  assert.equal(out.residualSlackBound, 4);
  assert.equal(out.pccMinReturnsExactMinimum, true);
});

test('residual-band minimizer example summary classifies constant-one as strictly above baseline', () => {
  const out = CheckResidualBandMinimizerExample0({ kind: 'NANDCircuit0', version: 0, inputCount: 0, gates: [], output: { kind: 'const', value: 1 } });
  assert.equal(out.tag, 'accept');
  assert.equal(out.thresholdDecision, true);
  assert.equal(out.baseline, 28);
  assert.equal(out.fullWordSize, 32);
  assert.equal(out.minimumRelationToBaseline, 'strictly-above');
  assert.equal(out.exactMinimumLowerBound, 29);
  assert.equal(out.exactMinimumUpperBound, 32);
  assert.equal(out.maxGainIterations, 4);
  assert.equal(out.residualSlackBound, 4);
  assert.equal(out.pccMinReturnsExactMinimum, true);
});

test('uniform residual-band minimizer rejects finite-list-only minimizer overclaim', async () => {
  const manifest = await currentManifest();
  manifest.minimizer.finiteInstanceList = true;
  manifest.minimizer.uniformAcrossSizes = false;
  const out = await CheckUniformResidualBandMinimizer0({ historicalReplay: true, writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformResidualBandMinimizer.MinimizerBoolean');
});

test('uniform residual-band minimizer rejects theorem activation by minimizer proof alone', async () => {
  const manifest = await currentManifest();
  manifest.uniformFinalSoundnessProved = true;
  const out = await CheckUniformResidualBandMinimizer0({ historicalReplay: true, writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformResidualBandMinimizer.BooleanField');
  assert.deepEqual(out.path, ['uniformFinalSoundnessProved']);
});

test('uniform residual-band minimizer rejects oracle use in minimizer surface', async () => {
  const manifest = await currentManifest();
  manifest.minimizer.usesExactMinimizationOracle = true;
  const out = await CheckUniformResidualBandMinimizer0({ historicalReplay: true, writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformResidualBandMinimizer.MinimizerBoolean');
});

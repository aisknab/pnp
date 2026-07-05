import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckUniformZeroSlackClosure0,
  CheckZeroSlackClosureExample0,
} from '../pcc-uniform-zeroslack-closure0.mjs';

async function currentManifest() {
  return JSON.parse(await readFile(new URL('../proof-obligations/UNIFORM_ZEROSLACK_CLOSURE.json', import.meta.url), 'utf8'));
}

test('uniform ZeroSlack closure checker accepts current closure surface', async () => {
  const out = await CheckUniformZeroSlackClosure0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-UNIFORM-ZEROSLACK-CLOSURE-2026-07-05-01');
  assert.equal(out.ufsObligationId, 'UFS-005-ZeroSlackContradictionUniform');
  assert.equal(out.zeroSlackClosureAccepted, true);
  assert.equal(out.ufs005ZeroSlackContradictionDischarged, true);
  assert.equal(out.zeroSlackSound, true);
  assert.equal(out.rankParametricClosure, true);
  assert.equal(out.selectorSilenceRankComplete, true);
  assert.equal(out.hnBudBlockerGraphAcyclic, true);
  assert.equal(out.positiveSlackContradictionComplete, true);
  assert.equal(out.certificateEncodingPolynomial, true);
  assert.equal(out.certificateSizePolynomial, true);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});

test('ZeroSlack example summary accepts an already-zero branch', () => {
  const out = CheckZeroSlackClosureExample0({
    residualSlackAssumption: 0,
    earlierRoutesExcluded: true,
    selectorSilenceComplete: true,
    hnBudClosureComplete: true,
  });
  assert.equal(out.tag, 'accept');
  assert.equal(out.zeroSlackSound, true);
  assert.equal(out.lambdaEqualsZero, true);
  assert.equal(out.contradictionNeeded, false);
  assert.equal(out.certificatePolynomialSize, true);
});

test('ZeroSlack example summary turns positive slack into contradiction', () => {
  const out = CheckZeroSlackClosureExample0({
    residualSlackAssumption: 1,
    earlierRoutesExcluded: true,
    selectorSilenceComplete: true,
    hnBudClosureComplete: true,
  });
  assert.equal(out.tag, 'accept');
  assert.equal(out.zeroSlackSound, true);
  assert.equal(out.lambdaEqualsZero, true);
  assert.equal(out.contradictionNeeded, true);
  assert.equal(out.positiveSlackForcesBCELReady, true);
  assert.equal(out.positivePacketForcesFaithfulSelector, true);
  assert.equal(out.faithfulSelectorForcesGainOrTypedBot, true);
  assert.equal(out.typedBotImpossibleByHBClosure, true);
});

test('uniform ZeroSlack closure rejects finite-list-only closure overclaim', async () => {
  const manifest = await currentManifest();
  manifest.zeroSlackClosure.finiteInstanceList = true;
  manifest.zeroSlackClosure.uniformAcrossRanks = false;
  const out = await CheckUniformZeroSlackClosure0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformZeroSlackClosure.ClosureBoolean');
});

test('uniform ZeroSlack closure rejects theorem activation by ZeroSlack proof alone', async () => {
  const manifest = await currentManifest();
  manifest.uniformFinalSoundnessProved = true;
  const out = await CheckUniformZeroSlackClosure0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformZeroSlackClosure.BooleanField');
  assert.deepEqual(out.path, ['uniformFinalSoundnessProved']);
});

test('uniform ZeroSlack closure rejects circular HN/BUD closure overclaim', async () => {
  const manifest = await currentManifest();
  manifest.zeroSlackClosure.hnBudBlockerGraphAcyclic = false;
  const out = await CheckUniformZeroSlackClosure0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformZeroSlackClosure.ClosureBoolean');
});

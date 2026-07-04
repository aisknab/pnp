import assert from 'node:assert/strict';
import { test } from 'node:test';

import { CheckUniformFinalSoundnessTarget0 } from '../pcc-uniform-final-soundness-target0.mjs';

async function currentManifest() {
  const { readFile } = await import('node:fs/promises');
  return JSON.parse(await readFile(new URL('../proof-obligations/UNIFORM_FINAL_SOUNDNESS_TARGET.json', import.meta.url), 'utf8'));
}

async function currentGapLedger() {
  const { readFile } = await import('node:fs/promises');
  return JSON.parse(await readFile(new URL('../proof-obligations/GAP_LEDGER.json', import.meta.url), 'utf8'));
}

test('uniform final soundness target accepts the current theorem target surface', async () => {
  const out = await CheckUniformFinalSoundnessTarget0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-UNIFORM-FINAL-SOUNDNESS-TARGET-2026-07-04-01');
  assert.equal(out.uniformFinalSoundnessTargetReady, true);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.finiteToUnboundedUniformityDischarged, false);
  assert.equal(out.externalReviewIsMathematicalPremise, false);
  assert.equal(out.codeBoundUniformProofRequired, true);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});

test('uniform target rejects premature theorem discharge', async () => {
  const manifest = await currentManifest();
  manifest.uniformFinalSoundnessProved = true;
  const out = await CheckUniformFinalSoundnessTarget0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformFinalSoundnessTarget.ActivationOverclaim');
  assert.deepEqual(out.path, ['uniformFinalSoundnessProved']);
});

test('uniform target rejects missing all-input obligation', async () => {
  const manifest = await currentManifest();
  manifest.requiredUniformObligations = manifest.requiredUniformObligations.filter((entry) => entry.id !== 'UFS-003-ThresholdEquivalenceAllInputs');
  const out = await CheckUniformFinalSoundnessTarget0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformFinalSoundnessTarget.ObligationIds');
});

test('uniform target rejects external review as a mathematical premise', async () => {
  const manifest = await currentManifest();
  manifest.activationDiscipline.externalReviewIsPremise = true;
  const out = await CheckUniformFinalSoundnessTarget0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformFinalSoundnessTarget.ExternalReviewPremise');
});

test('uniform target rejects cleared finite-to-unbounded gap before proof', async () => {
  const gapLedger = await currentGapLedger();
  const gap = gapLedger.gaps.find((entry) => entry.id === 'GAP-004-FiniteToUnboundedUniformity');
  gap.status = 'discharged';
  const out = await CheckUniformFinalSoundnessTarget0({ writeOutput: false, gapLedgerOverride: gapLedger });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformFinalSoundnessTarget.GapStatus');
});

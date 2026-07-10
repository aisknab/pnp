import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  MakePNPVerifyStepPlan0,
  ValidateLegacyStatus0,
} from '../pnp-verify-formal-reset0.mjs';

async function legacyStatus0() {
  return JSON.parse(await readFile(new URL('../PNP_STATUS.json', import.meta.url), 'utf8'));
}

test('legacy status is accepted only as a superseded checker replay', async () => {
  const out = ValidateLegacyStatus0(await legacyStatus0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.legacyCheckerReplayOnly, true);
  assert.equal(out.mathematicalTheoremEstablished, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
});

for (const [field, unsafeValue] of [
  ['authorityStatus', 'current'],
  ['supersededBy', null],
  ['mathematicalTheoremEstablished', true],
  ['externalReviewIsMathematicalPremise', true],
  ['publicTheoremEmissionAllowed', true],
  ['finalTheoremReady', true],
]) {
  test(`legacy status rejects unsafe ${field}`, async () => {
    const status = await legacyStatus0();
    status[field] = unsafeValue;

    const out = ValidateLegacyStatus0(status);

    assert.equal(out.tag, 'reject');
    assert.equal(out.coord, 'LegacyStatusFile.ValidationFailed');
    assert.deepEqual(out.path, [field]);
  });
}

test('default verifier plan excludes all historical audit pipelines', () => {
  const defaultIds = MakePNPVerifyStepPlan0().map((step) => step.id);
  const staleOptionIds = MakePNPVerifyStepPlan0({ includeReleaseAudit: true }).map((step) => step.id);

  assert.deepEqual(defaultIds, []);
  assert.deepEqual(staleOptionIds, []);
  assert.equal(defaultIds.includes('legacy-release-audit'), false);
  assert.equal(staleOptionIds.includes('legacy-release-audit'), false);
});

test('historical audit pipeline requires explicit opt-in', () => {
  const ids = MakePNPVerifyStepPlan0({ includeHistoricalAuditPipeline: true }).map((step) => step.id);

  assert.equal(ids.includes('theorem-binding-ledger-audit'), true);
  assert.equal(ids.includes('regeneration-ledger-audit'), true);
  assert.equal(ids.includes('legacy-release-audit'), false);
});

test('legacy release audit requires the explicit opt-in option', () => {
  const ids = MakePNPVerifyStepPlan0({ includeLegacyReleaseAudit: true }).map((step) => step.id);

  assert.equal(ids.includes('legacy-release-audit'), true);
});

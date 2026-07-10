import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckActivatedPNPStatus0 } from '../pcc-activated-pnp-status0.mjs';

async function currentStatus() {
  return JSON.parse(await readFile(new URL('../status/ACTIVATED_PNP_STATUS.json', import.meta.url), 'utf8'));
}

test('activated PNP status checker accepts the historical payload only with explicit opt-in', async () => {
  const status = await currentStatus();
  const out = await CheckActivatedPNPStatus0({
    writeOutput: false,
    historicalReplay: true,
    statusOverride: status,
    siteOverride: status,
  });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-ACTIVATED-STATUS-2026-07-05-01');
  assert.equal(out.activatedPNPStatusAccepted, true);
  assert.equal(out.publicTheoremEmissionAllowed, true);
  assert.equal(out.publicTheoremStatement, 'P = NP');
  assert.equal(out.publicTheoremConclusion, 'P = NP');
  assert.equal(out.publicTheoremUnderCheckerTrustModel, true);
  assert.equal(out.finalTheoremReady, true);
  assert.equal(out.internalFinalTheoremReady, true);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, true);
  assert.equal(out.uniformFinalSoundnessProved, true);
  assert.deepEqual(out.remainingBlockers, []);
  assert.equal(out.externalReviewAcceptanceRequiredForEmission, false);
  assert.equal(out.externalReviewIsMathematicalPremise, false);
  assert.match(out.activationDigestSha256, /^[0-9a-f]{64}$/);
  assert.match(out.statusSha256, /^[0-9a-f]{64}$/);
  assert.match(out.siteStatusSha256, /^[0-9a-f]{64}$/);
});

test('activated PNP status checker rejects the default current-authority route', async () => {
  const out = await CheckActivatedPNPStatus0({ writeOutput: false });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CheckActivatedPNPStatus0.HistoricalReplayRequired');
  assert.equal(out.mathematicalTheoremEstablished, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.publicTheoremStatement, null);
  assert.equal(out.finalTheoremReady, false);
});

test('activated PNP status rejects disabled public theorem emission', async () => {
  const status = await currentStatus();
  status.publicTheoremEmissionAllowed = false;
  const out = await CheckActivatedPNPStatus0({ writeOutput: false, historicalReplay: true, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ActivatedPNPStatus.Field');
  assert.deepEqual(out.path, ['status/ACTIVATED_PNP_STATUS.json', 'publicTheoremEmissionAllowed']);
});

test('activated PNP status rejects external review as theorem premise', async () => {
  const status = await currentStatus();
  status.externalReviewIsMathematicalPremise = true;
  const out = await CheckActivatedPNPStatus0({ writeOutput: false, historicalReplay: true, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ActivatedPNPStatus.Field');
  assert.deepEqual(out.path, ['status/ACTIVATED_PNP_STATUS.json', 'externalReviewIsMathematicalPremise']);
});

test('activated PNP status rejects non-empty remaining blockers', async () => {
  const status = await currentStatus();
  status.remainingBlockers = ['ExternalReview.Acceptance'];
  const out = await CheckActivatedPNPStatus0({ writeOutput: false, historicalReplay: true, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ActivatedPNPStatus.RemainingBlockers');
});

test('activated PNP status rejects site payload drift', async () => {
  const status = await currentStatus();
  const site = { ...status, status: 'stale' };
  const out = await CheckActivatedPNPStatus0({ writeOutput: false, historicalReplay: true, statusOverride: status, siteOverride: site });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ActivatedPNPStatus.Field');
  assert.deepEqual(out.path, ['public/pnp-status.json', 'status']);
});

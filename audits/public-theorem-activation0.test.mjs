import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckPublicTheoremActivation0,
  EvaluatePublicTheoremActivationExample0,
} from '../pcc-public-theorem-activation0.mjs';

async function currentManifest() {
  return JSON.parse(await readFile(new URL('../proof-obligations/PUBLIC_THEOREM_ACTIVATION.json', import.meta.url), 'utf8'));
}

test('public theorem activation checker accepts current activation surface', async () => {
  const out = await CheckPublicTheoremActivation0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01');
  assert.equal(out.publicTheoremActivationAccepted, true);
  assert.equal(out.publicTheoremEmissionAllowed, true);
  assert.equal(out.publicTheoremStatement, 'P = NP');
  assert.equal(out.publicTheoremConclusion, 'P = NP');
  assert.equal(out.publicTheoremUnderCheckerTrustModel, true);
  assert.equal(out.finalTheoremReady, true);
  assert.equal(out.internalFinalTheoremReady, true);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, true);
  assert.equal(out.uniformFinalSoundnessProved, true);
  assert.equal(out.externalReviewAcceptanceRequiredForEmission, false);
  assert.equal(out.externalReviewIsMathematicalPremise, false);
  assert.equal(out.historicalReportProseIsMathematicalPremise, false);
  assert.equal(out.publicSiteWordingIsMathematicalPremise, false);
  assert.deepEqual(out.clearedBlockers, ['ExternalReview.Acceptance']);
  assert.deepEqual(out.remainingBlockers, []);
});

test('activation example permits public theorem emission from accepted proof stack', () => {
  const out = EvaluatePublicTheoremActivationExample0({
    unrestrictedFinalSoundnessDischarged: true,
    internalFinalTheoremReady: true,
    pEqualsNPConclusionAccepted: true,
    usesExternalReviewAsPremise: false,
    usesHistoricalReportProseAsPremise: false,
  });
  assert.deepEqual(out, {
    tag: 'accept',
    publicTheoremEmissionAllowed: true,
    publicTheoremStatement: 'P = NP',
    remainingBlockers: [],
  });
});

test('activation example rejects external review as premise', () => {
  const out = EvaluatePublicTheoremActivationExample0({
    unrestrictedFinalSoundnessDischarged: true,
    internalFinalTheoremReady: true,
    pEqualsNPConclusionAccepted: true,
    usesExternalReviewAsPremise: true,
    usesHistoricalReportProseAsPremise: false,
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicTheoremActivation.ExamplePremise');
});

test('public theorem activation rejects external review as policy premise', async () => {
  const manifest = await currentManifest();
  manifest.activationPolicy.usesExternalReviewAsPremise = true;
  const out = await CheckPublicTheoremActivation0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicTheoremActivation.PolicyBoolean');
});

test('public theorem activation rejects missing theorem emission flag', async () => {
  const manifest = await currentManifest();
  manifest.publicTheoremEmissionAllowed = false;
  const out = await CheckPublicTheoremActivation0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicTheoremActivation.BooleanField');
  assert.deepEqual(out.path, ['publicTheoremEmissionAllowed']);
});

test('public theorem activation rejects nonempty remaining blockers after activation', async () => {
  const manifest = await currentManifest();
  manifest.claimBoundaryAfterActivation.remainingBlockers = ['ExternalReview.Acceptance'];
  const out = await CheckPublicTheoremActivation0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicTheoremActivation.AfterBoundary');
});

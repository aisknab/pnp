import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckUnrestrictedFinalSoundnessRelease0,
  EvaluateUnrestrictedFinalSoundnessReleaseExample0,
} from '../pcc-unrestricted-final-soundness-release0.mjs';

async function currentManifest() {
  return JSON.parse(await readFile(new URL('../proof-obligations/UNRESTRICTED_FINAL_SOUNDNESS_RELEASE.json', import.meta.url), 'utf8'));
}

test('unrestricted final soundness release checker accepts current UFS release surface', async () => {
  const out = await CheckUnrestrictedFinalSoundnessRelease0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-UNRESTRICTED-FINAL-SOUNDNESS-RELEASE-2026-07-05-01');
  assert.equal(out.ufsObligationId, 'UFS-008-ReleaseTransitionFromProofOnly');
  assert.equal(out.releaseTransitionAccepted, true);
  assert.equal(out.ufs008ReleaseTransitionDischarged, true);
  assert.equal(out.releaseUnrestrictedFinalSoundnessCleared, true);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, true);
  assert.equal(out.uniformFinalSoundnessProved, true);
  assert.equal(out.internalFinalTheoremReady, true);
  assert.equal(out.satInPConclusionAccepted, true);
  assert.equal(out.pEqualsNPConclusionAccepted, true);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, true);
  assert.deepEqual(out.clearedBlockers, ['Release.UnrestrictedFinalSoundness']);
  assert.deepEqual(out.remainingBlockers, ['ExternalReview.Acceptance']);
  assert.equal(out.externalReviewIsMathematicalPremise, false);
  assert.equal(out.dependencyCount, 8);
  assert.match(out.dependencyDigestSha256, /^[0-9a-f]{64}$/);
});

test('release example clears unrestricted final soundness from accepted proof chain', () => {
  const out = EvaluateUnrestrictedFinalSoundnessReleaseExample0({
    allUFSDependenciesAccepted: true,
    allUFSDependencyCoordinatesHashBound: true,
    ufs007ComplexityConclusionAccepted: true,
    usesExternalReviewAsPremise: false,
    usesHistoricalReportProseAsPremise: false,
    activatesPublicTheoremEmission: false,
  });
  assert.deepEqual(out, {
    tag: 'accept',
    releaseUnrestrictedFinalSoundnessCleared: true,
    unrestrictedFinalSoundnessDischarged: true,
    internalFinalTheoremReady: true,
    publicTheoremEmissionAllowed: false,
  });
});

test('unrestricted release rejects external review as release proof premise', async () => {
  const manifest = await currentManifest();
  manifest.releaseTransition.usesExternalReviewAsPremise = true;
  const out = await CheckUnrestrictedFinalSoundnessRelease0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UnrestrictedFinalSoundnessRelease.TransitionBoolean');
});

test('unrestricted release rejects historical report prose as release proof premise', async () => {
  const manifest = await currentManifest();
  manifest.releaseTransition.usesHistoricalReportProseAsPremise = true;
  const out = await CheckUnrestrictedFinalSoundnessRelease0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UnrestrictedFinalSoundnessRelease.TransitionBoolean');
});

test('unrestricted release rejects premature public theorem emission activation', async () => {
  const manifest = await currentManifest();
  manifest.publicTheoremEmissionAllowedByRelease = true;
  const out = await CheckUnrestrictedFinalSoundnessRelease0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UnrestrictedFinalSoundnessRelease.BooleanField');
  assert.deepEqual(out.path, ['publicTheoremEmissionAllowedByRelease']);
});

test('unrestricted release rejects clearing external review in this proof-only transition', async () => {
  const manifest = await currentManifest();
  manifest.releaseTransition.clearsExternalReviewAcceptance = true;
  const out = await CheckUnrestrictedFinalSoundnessRelease0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UnrestrictedFinalSoundnessRelease.TransitionBoolean');
});

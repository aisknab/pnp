import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckUniformComplexityConclusion0,
  EvaluateComplexityConclusionExample0,
} from '../pcc-uniform-complexity-conclusion0.mjs';

async function currentManifest() {
  return JSON.parse(await readFile(new URL('../proof-obligations/UNIFORM_COMPLEXITY_CONCLUSION.json', import.meta.url), 'utf8'));
}

test('uniform complexity conclusion checker accepts current conclusion surface', async () => {
  const out = await CheckUniformComplexityConclusion0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-UNIFORM-COMPLEXITY-CONCLUSION-2026-07-05-01');
  assert.equal(out.ufsObligationId, 'UFS-007-ComplexityConclusionUniform');
  assert.equal(out.complexityConclusionAccepted, true);
  assert.equal(out.ufs007ComplexityConclusionDischarged, true);
  assert.equal(out.satInPConclusionAccepted, true);
  assert.equal(out.pEqualsNPConclusionAccepted, true);
  assert.equal(out.constructedSATAlgorithmPolynomial, true);
  assert.equal(out.satInP, true);
  assert.equal(out.satNPCompleteImpliesPEqualsNP, true);
  assert.equal(out.releaseGateStillSeparate, true);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});

test('complexity conclusion example composes accepted proof surfaces into SAT in P', () => {
  const out = EvaluateComplexityConclusionExample0({
    inputFamilyAccepted: true,
    lockedConstructionPolynomial: true,
    thresholdEquivalenceAccepted: true,
    exactMinimizerPolynomial: true,
    noHiddenOracleSemanticAccepted: true,
    satNPComplete: true,
  });
  assert.deepEqual(out, {
    tag: 'accept',
    satDecisionPolynomial: true,
    satInP: true,
    pEqualsNPConclusionAccepted: true,
    releaseGateStillSeparate: true,
  });
});

test('uniform complexity conclusion rejects missing no-hidden-oracle premise', () => {
  const out = EvaluateComplexityConclusionExample0({
    inputFamilyAccepted: true,
    lockedConstructionPolynomial: true,
    thresholdEquivalenceAccepted: true,
    exactMinimizerPolynomial: true,
    noHiddenOracleSemanticAccepted: false,
    satNPComplete: true,
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformComplexityConclusion.ExamplePremise');
});

test('uniform complexity conclusion rejects external review as a proof premise', async () => {
  const manifest = await currentManifest();
  manifest.complexityConclusion.usesExternalReviewAsPremise = true;
  const out = await CheckUniformComplexityConclusion0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformComplexityConclusion.ComplexityBoolean');
});

test('uniform complexity conclusion rejects historical report prose as a proof premise', async () => {
  const manifest = await currentManifest();
  manifest.complexityConclusion.usesHistoricalReportProseAsPremise = true;
  const out = await CheckUniformComplexityConclusion0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformComplexityConclusion.ComplexityBoolean');
});

test('uniform complexity conclusion rejects theorem activation by complexity proof alone', async () => {
  const manifest = await currentManifest();
  manifest.publicTheoremEmissionAllowedByComplexity = true;
  const out = await CheckUniformComplexityConclusion0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'UniformComplexityConclusion.BooleanField');
  assert.deepEqual(out.path, ['publicTheoremEmissionAllowedByComplexity']);
});

import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';
import { CheckPublicTheoremActivation0, EvaluatePublicTheoremActivationExample0 } from '../pcc-public-theorem-activation0.mjs';

async function currentManifest0() { return JSON.parse(await readFile(new URL('../proof-obligations/PUBLIC_THEOREM_ACTIVATION.json', import.meta.url), 'utf8')); }

test('public theorem activation checker accepts the withdrawal state', async () => {
  const out = await CheckPublicTheoremActivation0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PUBLIC-THEOREM-ACTIVATION-WITHDRAWAL-2026-07-09-01');
  assert.equal(out.publicTheoremActivationAccepted, false);
  assert.equal(out.publicTheoremActivationWithdrawn, true);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.publicTheoremStatement, null);
  assert.equal(out.publicTheoremConclusion, null);
  assert.equal(out.publicTheoremUnderCheckerTrustModel, false);
  assert.equal(out.finalTheoremReady, false);
  assert.equal(out.formalReleaseGatePassed, false);
  assert.equal(out.externalReviewIsMathematicalPremise, false);
  assert.equal(out.humanReviewRequiredForMathematicalValidity, false);
  assert.equal(out.supersedesCoordinate, 'PNP-PUBLIC-THEOREM-ACTIVATION-2026-07-05-01');
});

test('activation example keeps theorem emission disabled while formal requirements are incomplete', () => {
  const out = EvaluatePublicTheoremActivationExample0({ closedLeanRootTheorem: false, concreteMachineSemantics: false, noProjectSpecificAxioms: false, noSorryOrAdmit: true, formalPolynomialRuntimeProof: false, paperTheoremInventoryMatch: false, generatedSiteStatus: true, usesJsonBooleanActivation: false, usesJavaScriptCheckerAcceptanceAsTheoremEvidence: false, requiresHumanReview: false });
  assert.equal(out.formalReleaseGatePassed, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.publicTheoremStatement, null);
});

test('activation example can pass only from the complete mechanical formal gate', () => {
  const out = EvaluatePublicTheoremActivationExample0({ closedLeanRootTheorem: true, concreteMachineSemantics: true, noProjectSpecificAxioms: true, noSorryOrAdmit: true, formalPolynomialRuntimeProof: true, paperTheoremInventoryMatch: true, generatedSiteStatus: true, usesJsonBooleanActivation: false, usesJavaScriptCheckerAcceptanceAsTheoremEvidence: false, requiresHumanReview: false });
  assert.equal(out.formalReleaseGatePassed, true);
  assert.equal(out.publicTheoremEmissionAllowed, true);
  assert.equal(out.publicTheoremStatement, 'P = NP');
});

test('withdrawal checker rejects JSON reactivation', async () => {
  const manifest = await currentManifest0();
  manifest.publicTheoremEmissionAllowed = true;
  const out = await CheckPublicTheoremActivation0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicTheoremActivation.WithdrawalBoolean');
});

test('withdrawal checker rejects JavaScript checker acceptance as theorem evidence', async () => {
  const manifest = await currentManifest0();
  manifest.withdrawalPolicy.allowsJavaScriptCheckerAcceptanceAsTheoremEvidence = true;
  const out = await CheckPublicTheoremActivation0({ writeOutput: false, manifestOverride: manifest });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'PublicTheoremActivation.PolicyBoolean');
});

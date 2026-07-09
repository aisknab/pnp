import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckFormalReconstructionStatus0,
  EvaluateFormalReleaseGateExample0,
} from '../pcc-formal-reconstruction-status0.mjs';

async function currentStatus0() {
  return JSON.parse(await readFile(new URL('../status/FORMAL_RECONSTRUCTION_STATUS.json', import.meta.url), 'utf8'));
}

async function legacyStatus0() {
  return JSON.parse(await readFile(new URL('../status/ACTIVATED_PNP_STATUS.json', import.meta.url), 'utf8'));
}

test('formal reconstruction status accepts the current non-activation boundary', async () => {
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-09-01');
  assert.equal(out.formalReconstructionStatusAccepted, true);
  assert.equal(out.targetTheorem, 'P = NP');
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.publicTheoremStatement, null);
  assert.equal(out.finalTheoremReady, false);
  assert.equal(out.rootLeanTheoremPresent, false);
  assert.equal(out.closedLeanTheoremPresent, false);
  assert.equal(out.formalReleaseGatePassed, false);
  assert.equal(out.projectSpecificAxiomsRemaining, true);
  assert.equal(out.legacyActivationSuperseded, true);
  assert.equal(out.humanReviewRequiredForMathematicalValidity, false);
  assert.equal(out.remainingFormalObligations.length, 8);
  assert.match(out.statusSha256, /^[0-9a-f]{64}$/);
  assert.match(out.siteStatusSha256, /^[0-9a-f]{64}$/);
});

test('formal reconstruction status rejects attempted theorem reactivation', async () => {
  const status = await currentStatus0();
  status.publicTheoremEmissionAllowed = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'publicTheoremEmissionAllowed']);
});

test('formal reconstruction status rejects site mirror drift', async () => {
  const status = await currentStatus0();
  const site = { ...status, claimStatus: 'stale' };
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: site });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['public/pnp-status.json', 'claimStatus']);
});

test('formal reconstruction status rejects a non-superseded legacy activation path', async () => {
  const legacy = await legacyStatus0();
  legacy.superseded = false;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, legacyStatusOverride: legacy });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.LegacyField');
  assert.deepEqual(out.path, ['status/ACTIVATED_PNP_STATUS.json', 'superseded']);
});

test('formal release gate remains closed when formal obligations are missing', () => {
  const out = EvaluateFormalReleaseGateExample0({
    closedLeanRootTheorem: false,
    concreteMachineSemantics: false,
    noProjectSpecificAxioms: false,
    noSorryOrAdmit: true,
    formalPolynomialRuntimeProof: false,
    paperTheoremInventoryMatch: false,
    generatedSiteStatus: true,
    usesJsonBooleanActivation: false,
    usesJavaScriptCheckerAcceptanceAsTheoremEvidence: false,
    requiresHumanReview: false,
  });
  assert.equal(out.tag, 'accept');
  assert.equal(out.formalReleaseGatePassed, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.missing.includes('closedLeanRootTheorem'), true);
});

test('complete declarations still cannot activate without verified Lean artifacts', () => {
  const out = EvaluateFormalReleaseGateExample0({
    closedLeanRootTheorem: true,
    concreteMachineSemantics: true,
    noProjectSpecificAxioms: true,
    noSorryOrAdmit: true,
    formalPolynomialRuntimeProof: true,
    paperTheoremInventoryMatch: true,
    generatedSiteStatus: true,
    usesJsonBooleanActivation: false,
    usesJavaScriptCheckerAcceptanceAsTheoremEvidence: false,
    requiresHumanReview: false,
  });
  assert.equal(out.tag, 'accept');
  assert.equal(out.requirementsDeclaredComplete, true);
  assert.equal(out.formalReleaseGatePassed, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.requiresLeanArtifactVerification, true);
  assert.deepEqual(out.missing, []);
  assert.deepEqual(out.forbidden, []);
});

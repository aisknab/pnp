import assert from 'node:assert/strict';
import { readFile, readdir } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckFormalReconstructionStatus0,
  FORMAL_RECONSTRUCTION_BLOCKERS0,
} from '../pcc-formal-reconstruction-status0.mjs';

async function currentStatus0() {
  return JSON.parse(await readFile(new URL('../status/FORMAL_RECONSTRUCTION_STATUS.json', import.meta.url), 'utf8'));
}

test('formal reconstruction status accepts the current source and public mirrors', async () => {
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-FORMAL-RECONSTRUCTION-STATUS-2026-07-10-01');
  assert.equal(out.formalReconstructionStatusAccepted, true);
  assert.equal(out.mathematicalTheoremEstablished, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.publicTheoremStatement, null);
  assert.equal(out.finalTheoremReady, false);
  assert.equal(out.internalFinalTheoremReady, false);
  assert.equal(out.unrestrictedFinalSoundnessDischarged, false);
  assert.equal(out.uniformFinalSoundnessProved, false);
  assert.equal(out.satInPConclusionAccepted, false);
  assert.equal(out.pEqualsNPConclusionAccepted, false);
  assert.equal(out.rootLeanTheoremPresent, false);
  assert.equal(out.rootLeanTheoremBuilt, false);
  assert.equal(out.rootLeanTheoremAxiomAuditPassed, false);
  assert.equal(out.projectSpecificAxiomsRemaining, true);
  assert.equal(out.externalReviewIsMathematicalPremise, false);
  assert.deepEqual(out.remainingBlockers, FORMAL_RECONSTRUCTION_BLOCKERS0);
  assert.match(out.statusSha256, /^[0-9a-f]{64}$/u);
  assert.match(out.siteStatusSha256, /^[0-9a-f]{64}$/u);
});

test('formal status inventories every active core workflow', async () => {
  const status = await currentStatus0();
  const names = (await readdir(new URL('../.github/workflows/', import.meta.url)))
    .filter((name) => name.endsWith('.yml'))
    .sort()
    .map((name) => `.github/workflows/${name}`);

  assert.deepEqual([...status.activeCoreWorkflows].sort(), names);
});

test('formal status does not advertise an unpinned current-tree legacy replay', async () => {
  const status = await currentStatus0();
  assert.equal(status.legacyCheckerReplayCommand, null);
  assert.equal(status.nonClaims.some((entry) => entry.includes('No current-tree command')), true);
});

test('formal reconstruction status rejects theorem emission activation', async () => {
  const status = await currentStatus0();
  status.publicTheoremEmissionAllowed = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'publicTheoremEmissionAllowed']);
});

test('formal reconstruction status rejects an unearned root theorem', async () => {
  const status = await currentStatus0();
  status.rootLeanTheoremPresent = true;
  status.rootLeanTheoremBuilt = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'rootLeanTheoremPresent']);
});

test('formal reconstruction status rejects external review as a theorem premise', async () => {
  const status = await currentStatus0();
  status.externalReviewIsMathematicalPremise = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Field');
  assert.deepEqual(out.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', 'externalReviewIsMathematicalPremise']);
});

test('formal reconstruction status rejects hidden formal blockers', async () => {
  const status = await currentStatus0();
  status.remainingBlockers = [];
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Blockers');
});

test('formal reconstruction status rejects a drifting public mirror', async () => {
  const status = await currentStatus0();
  const site = { ...status, nonClaims: [...status.nonClaims, 'drift'] };
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: site });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.NonClaims');
  assert.deepEqual(out.path, ['public/pnp-status.json', 'nonClaims']);
});

test('formal reconstruction status rejects formatting-only public mirror drift', async () => {
  const status = await currentStatus0();
  const statusText = `${JSON.stringify(status, null, 2)}\n`;
  const siteText = JSON.stringify(status);
  const out = await CheckFormalReconstructionStatus0({
    writeOutput: false,
    statusBytesOverride: statusText,
    siteBytesOverride: siteText,
  });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.SiteMirrorMismatch');
  assert.deepEqual(out.path, ['public/pnp-status.json']);
});

test('formal reconstruction status rejects unknown theorem authority fields', async () => {
  const status = await currentStatus0();
  status.publicTheoremEmissionAllowedByLegacyRoute = true;
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Keys');
  assert.deepEqual(out.witness.extraKeys, ['publicTheoremEmissionAllowedByLegacyRoute']);
});

test('formal reconstruction status rejects reintroduced upload commands', async () => {
  const status = await currentStatus0();
  status.verificationCommands.push('npm run pnp:verify:upload');
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.Commands');
});

test('formal reconstruction status rejects contradictory non-claims', async () => {
  const status = await currentStatus0();
  status.nonClaims.push('P = NP is established by another route.');
  const out = await CheckFormalReconstructionStatus0({ writeOutput: false, statusOverride: status, siteOverride: status });
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'FormalReconstructionStatus.NonClaims');
});

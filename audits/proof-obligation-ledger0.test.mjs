import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckProofObligationLedger0 } from '../pcc-proof-obligation-ledger0.mjs';

async function loadLedger0() {
  return JSON.parse(await readFile(new URL('../proof-obligations/OBLIGATION_LEDGER.json', import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('proof obligation ledger accepts current source ledger', async () => {
  const out = await CheckProofObligationLedger0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-PROOF-OBLIGATION-LEDGER-2026-06-27-01');
  assert.equal(out.proofObligationLedgerReady, true);
  assert.equal(out.fullProofObligationDischargeProved, false);
  assert.equal(out.publicTheoremEmissionAllowedByLedger, false);
  assert.equal(out.obligationCount, 19);
  assert.ok(out.obligationIds.includes('OBL-015-FiniteToUnboundedFamilyAudit'));
  assert.ok(out.obligationIds.includes('OBL-016-BaseDirectBindingSeed'));
  assert.ok(out.obligationIds.includes('OBL-017-CHGDirectBindingSeed'));
  assert.ok(out.obligationIds.includes('OBL-018-ModeDirectBindingSeed'));
  assert.ok(out.obligationIds.includes('OBL-019-EDirectBindingSeed'));
  assert.ok(out.sourceFileCount > 0);
  assert.ok(out.testFileCount > 0);
  assert.equal(out.obligationDigestLedgerSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('proof obligation ledger rejects public theorem activation', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckProofObligationLedger0({ ledgerOverride: ledger, writeOutput: false });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ProofObligationLedger.PublicEmission');
});

test('proof obligation ledger rejects full discharge overclaim', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.fullProofObligationDischargeProved = true;

  const out = await CheckProofObligationLedger0({ ledgerOverride: ledger, writeOutput: false });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ProofObligationLedger.FullDischargeFlag');
});

test('proof obligation ledger rejects changed obligation ordering', async () => {
  const ledger = clone0(await loadLedger0());
  const temp = ledger.obligations[1];
  ledger.obligations[1] = ledger.obligations[2];
  ledger.obligations[2] = temp;

  const out = await CheckProofObligationLedger0({ ledgerOverride: ledger, writeOutput: false });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ProofObligationLedger.ObligationIds');
});

test('proof obligation ledger rejects forward dependencies', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.obligations[1].dependencies.push('OBL-014-UnrestrictedFinalSoundnessBlocked');

  const out = await CheckProofObligationLedger0({ ledgerOverride: ledger, writeOutput: false });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ProofObligationLedger.ForwardDependency');
});

test('proof obligation ledger rejects missing source files', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.obligations[0].sourceFiles.push('missing/proof-obligation-source.json');

  const out = await CheckProofObligationLedger0({ ledgerOverride: ledger, writeOutput: false });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ProofObligationLedger.PathMissing');
});

test('proof obligation ledger rejects missing test files', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.obligations[0].testFiles.push('missing/proof-obligation-test.mjs');

  const out = await CheckProofObligationLedger0({ ledgerOverride: ledger, writeOutput: false });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ProofObligationLedger.PathMissing');
});

test('proof obligation ledger rejects activated hash mode or unknown status', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.obligations[0].status = 'activated-final-theorem';

  const out = await CheckProofObligationLedger0({ ledgerOverride: ledger, writeOutput: false });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ProofObligationLedger.ObligationStatus');
});

import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { AuditRegenerationLedger0 } from '../scripts/audit-regeneration-ledger.mjs';

async function loadLedger0() {
  return JSON.parse(await readFile(new URL('../artifacts/regeneration/REGENERATION_LEDGER.json', import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('regeneration ledger audit accepts current source ledger', async () => {
  const out = await AuditRegenerationLedger0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-REGENERATION-LEDGER-2026-06-27-01');
  assert.equal(out.regenerationLedgerReady, true);
  assert.equal(out.fullArtifactRegenerationProved, false);
  assert.equal(out.publicTheoremEmissionAllowedByLedger, false);
  assert.ok(out.recordCount >= 10);
  assert.ok(out.deterministicRecordCount > 0);
  assert.ok(out.runtimeGeneratedRecordCount > 0);
  assert.ok(out.sourceDigestLedgerSha256.length === 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('regeneration ledger audit rejects public theorem activation', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await AuditRegenerationLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RegenerationLedger.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('regeneration ledger audit rejects full regeneration overclaim', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.fullArtifactRegenerationProved = true;

  const out = await AuditRegenerationLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RegenerationLedger.FullProofFlag');
});

test('regeneration ledger audit rejects changed record order or missing record', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.records.pop();

  const out = await AuditRegenerationLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RegenerationLedger.RecordIds');
});

test('regeneration ledger audit rejects duplicate record ids', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.records[1].id = ledger.records[0].id;

  const out = await AuditRegenerationLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RegenerationLedger.RecordIds');
});

test('regeneration ledger audit rejects missing source file', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.records[0].sourceFiles.push('missing/regeneration-source.json');

  const out = await AuditRegenerationLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RegenerationLedger.PathMissing');
});

test('regeneration ledger audit rejects committed output that is missing', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.records[0].outputCommitted = true;
  ledger.records[0].generatedAtRuntime = false;
  ledger.records[0].outputPath = 'missing/committed-output.json';

  const out = await AuditRegenerationLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RegenerationLedger.PathMissing');
});

import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckGapLedger0 } from '../pcc-gap-ledger0.mjs';

async function loadLedger0() {
  return JSON.parse(await readFile(new URL('../proof-obligations/GAP_LEDGER.json', import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('gap ledger checker accepts current ledger', async () => {
  const out = await CheckGapLedger0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-GAP-LEDGER-2026-06-27-01');
  assert.equal(out.gapLedgerReady, true);
  assert.equal(out.allKnownGapsRepresented, true);
  assert.equal(out.gapLedgerClaimsNoRemainingGaps, false);
  assert.equal(out.fullGapClosureProved, false);
  assert.equal(out.publicTheoremEmissionAllowedByLedger, false);
  assert.equal(out.gapCount, 12);
  assert.ok(out.activationBlockingGapCount >= 4);
  assert.ok(out.externalTrustGapCount >= 2);
  assert.ok(out.evidenceFileCount > 0);
  assert.equal(out.gapEvidenceDigestLedgerSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('gap ledger checker rejects public theorem activation', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckGapLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'GapLedger.PublicEmission');
});

test('gap ledger checker rejects no-gaps overclaim', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.gapLedgerClaimsNoRemainingGaps = true;

  const out = await CheckGapLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'GapLedger.NoRemainingGapsOverclaim');
});

test('gap ledger checker rejects full closure overclaim', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.fullGapClosureProved = true;

  const out = await CheckGapLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'GapLedger.FullClosureOverclaim');
});

test('gap ledger checker rejects changed gap ordering', async () => {
  const ledger = clone0(await loadLedger0());
  const temp = ledger.gaps[1];
  ledger.gaps[1] = ledger.gaps[2];
  ledger.gaps[2] = temp;

  const out = await CheckGapLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'GapLedger.GapIds');
});

test('gap ledger checker rejects activation-blocking gap without blocker', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.gaps[0].blocker = null;

  const out = await CheckGapLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'GapLedger.ActivationGapNeedsBlocker');
});

test('gap ledger checker rejects external trust gap with wrong severity', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.gaps.find((gap) => gap.id === 'GAP-006-JavaScriptRuntimeTrust').severity = 'hardening';

  const out = await CheckGapLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'GapLedger.ExternalTrustSeverity');
});

test('gap ledger checker rejects missing evidence files', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.gaps[0].evidenceFiles.push('missing/gap-evidence.json');

  const out = await CheckGapLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'GapLedger.PathMissing');
});

test('gap ledger checker rejects individual gap public emission', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.gaps[0].publicTheoremEmissionAllowedByGap = true;

  const out = await CheckGapLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'GapLedger.GapPublicEmission');
});

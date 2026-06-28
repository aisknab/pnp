import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckComplexityLedger0,
} from '../pcc-complexity-ledger0.mjs';

async function loadLedger0() {
  const text = await readFile(new URL('../complexity/COMPLEXITY_LEDGER.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('complexity ledger checker accepts current ledger', async () => {
  const out = await CheckComplexityLedger0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-COMPLEXITY-LEDGER-2026-06-27-01');
  assert.equal(out.complexityLedgerReady, true);
  assert.equal(out.fullComplexityImplicationDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByLedger, false);
  assert.equal(out.proofObjectCount, 6);
  assert.equal(out.derivedConditionalConclusionCount, 2);
  assert.ok(out.evidenceFileCount >= 1);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('complexity ledger checker rejects public theorem activation', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckComplexityLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ComplexityLedger.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('complexity ledger checker rejects full implication discharge overclaim', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.fullComplexityImplicationDischarged = true;

  const out = await CheckComplexityLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ComplexityLedger.FullDischargeFlag');
  assert.deepEqual(out.path, ['fullComplexityImplicationDischarged']);
});

test('complexity ledger checker rejects derived conclusion activation', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.derivedConditionalConclusions[0].currentlyActivated = true;

  const out = await CheckComplexityLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ComplexityLedger.DerivedActivation');
  assert.deepEqual(out.path, ['derivedConditionalConclusions', 0, 'currentlyActivated']);
});

test('complexity ledger checker rejects forward premise edges', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.proofObjects[1].premiseIds.push('Complexity.PublicEmissionBoundary.NonActivation');

  const out = await CheckComplexityLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ComplexityLedger.ForwardPremise');
});

test('complexity ledger checker rejects missing evidence files', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.proofObjects[0].evidenceFiles.push('missing/complexity-evidence.json');

  const out = await CheckComplexityLedger0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ComplexityLedger.EvidencePathMissing');
  assert.deepEqual(out.path, ['missing/complexity-evidence.json']);
});

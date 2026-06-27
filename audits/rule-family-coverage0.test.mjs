import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import {
  CheckRuleFamilyCoverage0,
} from '../pcc-rule-family-coverage0.mjs';

async function loadLedger0() {
  const text = await readFile(new URL('../semantic-kernel/RULE_FAMILY_COVERAGE.json', import.meta.url), 'utf8');
  return JSON.parse(text);
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('rule-family coverage checker accepts current ledger', async () => {
  const out = await CheckRuleFamilyCoverage0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-RULE-FAMILY-COVERAGE-2026-06-27-01');
  assert.equal(out.coverageLedgerReady, true);
  assert.equal(out.fullRuleFamilyCoverageProved, false);
  assert.equal(out.ruleFamilyCount, 7);
  assert.deepEqual(out.ruleFamilyIds, ['DPInd', 'GlobalFinalPrefix', 'SATReduction', 'Complexity', 'PublicEmission', 'SuccessorSeal', 'TrustBase']);
  assert.ok(out.totalPositiveTestCount >= 1);
  assert.ok(out.totalNegativeTestCount >= 1);
  assert.ok(out.totalMutationTestCount >= 1);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('rule-family coverage checker rejects public theorem activation', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckRuleFamilyCoverage0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RuleFamilyCoverage.PublicEmission');
  assert.deepEqual(out.path, ['claimBoundary', 'publicTheoremEmissionAllowed']);
});

test('rule-family coverage checker rejects premature full coverage claim', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.fullRuleFamilyCoverageProved = true;

  const out = await CheckRuleFamilyCoverage0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RuleFamilyCoverage.FullCoverageFlag');
  assert.deepEqual(out.path, ['fullRuleFamilyCoverageProved']);
});

test('rule-family coverage checker rejects missing family id', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.ruleFamilies = ledger.ruleFamilies.slice(1);

  const out = await CheckRuleFamilyCoverage0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RuleFamilyCoverage.FamilyIds');
  assert.deepEqual(out.path, ['ruleFamilies']);
});

test('rule-family coverage checker rejects covered seed without mutation tests', async () => {
  const ledger = clone0(await loadLedger0());
  const covered = ledger.ruleFamilies.find((family) => family.coverageStatus === 'covered-seed');
  covered.mutationTestCount = 0;

  const out = await CheckRuleFamilyCoverage0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RuleFamilyCoverage.NoMutationTests');
});

test('rule-family coverage checker rejects missing evidence files', async () => {
  const ledger = clone0(await loadLedger0());
  ledger.ruleFamilies[0].evidenceFiles.push('missing/rule-family-evidence.txt');

  const out = await CheckRuleFamilyCoverage0({
    ledgerOverride: ledger,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'RuleFamilyCoverage.EvidencePathMissing');
  assert.deepEqual(out.path, ['missing/rule-family-evidence.txt']);
});

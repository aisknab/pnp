import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckHNDirectBindingSeed0 } from '../pcc-direct-bind-hereditary-normal-forms0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

async function baseOptions0(overrides = {}) {
  return {
    manifestOverride: await json0('report-bindings/direct-bindings/HN_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    totalityOverride: await json0('checker-totality/CHECKER_TOTALITY_AUDIT.json'),
    mutationsOverride: await json0('checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json'),
    ruleCoverageOverride: await json0('semantic-kernel/RULE_FAMILY_COVERAGE.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
    ...overrides,
  };
}

test('HN direct-binding seed accepts current manifest and linked ledgers', async () => {
  const out = await CheckHNDirectBindingSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-HN-HEREDITARY-NORMAL-FORMS-SEED-2026-06-27-01');
  assert.equal(out.hnDirectBindingSeedReady, true);
  assert.equal(out.boundInventoryEntryId, 'TL-010-HN');
  assert.equal(out.boundCoverageEntryId, 'COV-010-HN');
  assert.equal(out.boundClosureEntryId, 'DCC-010-HN');
  assert.deepEqual(out.coveredHNComponents, [
    'HN.HereditaryShapeRecognitionSurface',
    'HN.BWLExactnessSurface',
    'HN.LNConfluenceSurface',
    'HN.ParseOrExitSurface',
    'HN.LeafTightnessSurface',
    'HN.CheckerHardeningSurface',
    'HN.ActivationBoundary',
  ]);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalHNTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.ok(out.evidenceFileCount > 0);
  assert.equal(out.evidenceDigestSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});

test('HN direct-binding seed rejects public theorem activation', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/HN_DIRECT_BINDING_SEED.json'));
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;
  const out = await CheckHNDirectBindingSeed0(await baseOptions0({ manifestOverride: manifest }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HNDirectBindingSeed.PublicEmission');
});

test('HN direct-binding seed rejects direct binding completion overclaim', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/HN_DIRECT_BINDING_SEED.json'));
  manifest.directCheckerBindingComplete = true;
  const out = await CheckHNDirectBindingSeed0(await baseOptions0({ manifestOverride: manifest }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HNDirectBindingSeed.Manifest.directCheckerBindingComplete');
});

test('HN direct-binding seed rejects HN inventory mismatch', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.inventoryEntries.find((entry) => entry.id === 'TL-010-HN').sourceLabel = 'NotHN';
  const out = await CheckHNDirectBindingSeed0(await baseOptions0({ inventoryOverride: inventory }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HNDirectBindingSeed.InventoryHNMismatch');
});

test('HN direct-binding seed rejects coverage row direct-binding flip', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries.find((entry) => entry.id === 'COV-010-HN').directCheckerBindingComplete = true;
  const out = await CheckHNDirectBindingSeed0(await baseOptions0({ matrixOverride: matrix }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HNDirectBindingSeed.MatrixHNMismatch');
});

test('HN direct-binding seed rejects closure row surface mismatch', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-010-HN').nextDirectBindingSurface = 'wrong-checker.mjs';
  const out = await CheckHNDirectBindingSeed0(await baseOptions0({ closureOverride: closure }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HNDirectBindingSeed.ClosureHNMismatch');
});

test('HN direct-binding seed rejects unexpected closure gap', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-010-HN').blockingGaps = ['GAP-001-UnrestrictedFinalSoundness'];
  const out = await CheckHNDirectBindingSeed0(await baseOptions0({ closureOverride: closure }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HNDirectBindingSeed.ClosureHNMismatch');
});

test('HN direct-binding seed rejects missing proof obligation entry', async () => {
  const obligations = clone0(await json0('proof-obligations/OBLIGATION_LEDGER.json'));
  obligations.obligations = obligations.obligations.filter((entry) => entry.id !== 'OBL-025-HNDirectBindingSeed');
  const out = await CheckHNDirectBindingSeed0(await baseOptions0({ obligationsOverride: obligations }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HNDirectBindingSeed.ObligationMissing');
});

test('HN direct-binding seed rejects hardening ledger overclaim', async () => {
  const ruleCoverage = clone0(await json0('semantic-kernel/RULE_FAMILY_COVERAGE.json'));
  ruleCoverage.fullRuleFamilyCoverageProved = true;
  const out = await CheckHNDirectBindingSeed0(await baseOptions0({ ruleCoverageOverride: ruleCoverage }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HNDirectBindingSeed.RuleCoverageMismatch');
});

test('HN direct-binding seed rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.hnDirectBindingSeedCoordinate;
  const out = await CheckHNDirectBindingSeed0(await baseOptions0({ statusOverride: status }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HNDirectBindingSeed.StatusCoordinate');
});

import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckHResolveDirectBindingSeed0 } from '../pcc-direct-bind-hresolve0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

async function baseOptions0(overrides = {}) {
  return {
    manifestOverride: await json0('report-bindings/direct-bindings/HRESOLVE_DIRECT_BINDING_SEED.json'),
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

test('HResolve direct-binding seed accepts current manifest and linked ledgers', async () => {
  const out = await CheckHResolveDirectBindingSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-HRESOLVE-GLOBAL-HEREDITARY-RESOLVER-SEED-2026-06-27-01');
  assert.equal(out.hresolveDirectBindingSeedReady, true);
  assert.equal(out.boundInventoryEntryId, 'TL-011-HResolve');
  assert.equal(out.boundCoverageEntryId, 'COV-011-HResolve');
  assert.equal(out.boundClosureEntryId, 'DCC-011-HResolve');
  assert.deepEqual(out.coveredHResolveComponents, [
    'HResolve.GlobalResolverSurface',
    'HResolve.ExactMinimumRouteSurface',
    'HResolve.GainRouteSurface',
    'HResolve.StrongNoHereditarySidecarSurface',
    'HResolve.HDisjointFamilySurface',
    'HResolve.CheckerHardeningSurface',
    'HResolve.ActivationBoundary',
  ]);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalHResolveTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.ok(out.evidenceFileCount > 0);
  assert.equal(out.evidenceDigestSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, ['Release.UnrestrictedFinalSoundness', 'ExternalReview.Acceptance']);
});

test('HResolve direct-binding seed rejects public theorem activation', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/HRESOLVE_DIRECT_BINDING_SEED.json'));
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;
  const out = await CheckHResolveDirectBindingSeed0(await baseOptions0({ manifestOverride: manifest }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HResolveDirectBindingSeed.PublicEmission');
});

test('HResolve direct-binding seed rejects direct binding completion overclaim', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/HRESOLVE_DIRECT_BINDING_SEED.json'));
  manifest.directCheckerBindingComplete = true;
  const out = await CheckHResolveDirectBindingSeed0(await baseOptions0({ manifestOverride: manifest }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HResolveDirectBindingSeed.Manifest.directCheckerBindingComplete');
});

test('HResolve direct-binding seed rejects inventory mismatch', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.inventoryEntries.find((entry) => entry.id === 'TL-011-HResolve').sourceLabel = 'NotHResolve';
  const out = await CheckHResolveDirectBindingSeed0(await baseOptions0({ inventoryOverride: inventory }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HResolveDirectBindingSeed.InventoryHResolveMismatch');
});

test('HResolve direct-binding seed rejects coverage row direct-binding flip', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries.find((entry) => entry.id === 'COV-011-HResolve').directCheckerBindingComplete = true;
  const out = await CheckHResolveDirectBindingSeed0(await baseOptions0({ matrixOverride: matrix }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HResolveDirectBindingSeed.MatrixHResolveMismatch');
});

test('HResolve direct-binding seed rejects closure row surface mismatch', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-011-HResolve').nextDirectBindingSurface = 'wrong-checker.mjs';
  const out = await CheckHResolveDirectBindingSeed0(await baseOptions0({ closureOverride: closure }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HResolveDirectBindingSeed.ClosureHResolveMismatch');
});

test('HResolve direct-binding seed rejects unexpected closure gap', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-011-HResolve').blockingGaps = ['GAP-001-UnrestrictedFinalSoundness'];
  const out = await CheckHResolveDirectBindingSeed0(await baseOptions0({ closureOverride: closure }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HResolveDirectBindingSeed.ClosureHResolveMismatch');
});

test('HResolve direct-binding seed rejects missing proof obligation entry', async () => {
  const obligations = clone0(await json0('proof-obligations/OBLIGATION_LEDGER.json'));
  obligations.obligations = obligations.obligations.filter((entry) => entry.id !== 'OBL-026-HResolveDirectBindingSeed');
  const out = await CheckHResolveDirectBindingSeed0(await baseOptions0({ obligationsOverride: obligations }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HResolveDirectBindingSeed.ObligationMissing');
});

test('HResolve direct-binding seed rejects hardening ledger overclaim', async () => {
  const totality = clone0(await json0('checker-totality/CHECKER_TOTALITY_AUDIT.json'));
  totality.fullCheckerTotalityProved = true;
  const out = await CheckHResolveDirectBindingSeed0(await baseOptions0({ totalityOverride: totality }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HResolveDirectBindingSeed.TotalityLedgerMismatch');
});

test('HResolve direct-binding seed rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.hresolveDirectBindingSeedCoordinate;
  const out = await CheckHResolveDirectBindingSeed0(await baseOptions0({ statusOverride: status }));
  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'HResolveDirectBindingSeed.StatusCoordinate');
});

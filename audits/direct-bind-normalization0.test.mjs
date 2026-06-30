import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckNDirectBindingSeed0 } from '../pcc-direct-bind-normalization0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

async function baseOptions0(overrides = {}) {
  return {
    manifestOverride: await json0('report-bindings/direct-bindings/N_DIRECT_BINDING_SEED.json'),
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

test('N direct-binding seed accepts current manifest and linked ledgers', async () => {
  const out = await CheckNDirectBindingSeed0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-N-NORMALIZATION-SEED-2026-06-27-01');
  assert.equal(out.nDirectBindingSeedReady, true);
  assert.equal(out.boundInventoryEntryId, 'TL-005-N');
  assert.equal(out.boundCoverageEntryId, 'COV-005-N');
  assert.equal(out.boundClosureEntryId, 'DCC-005-N');
  assert.deepEqual(out.coveredNComponents, [
    'N.TraceableNormalizationSurface',
    'N.WitnessTransportSurface',
    'N.NormalizationCheckerHardeningSurface',
    'N.NormalizationActivationBoundary',
  ]);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalNTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.ok(out.evidenceFileCount > 0);
  assert.equal(out.evidenceDigestSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('N direct-binding seed rejects public theorem activation', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/N_DIRECT_BINDING_SEED.json'));
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckNDirectBindingSeed0(await baseOptions0({ manifestOverride: manifest }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NDirectBindingSeed.PublicEmission');
});

test('N direct-binding seed rejects direct binding completion overclaim', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/N_DIRECT_BINDING_SEED.json'));
  manifest.directCheckerBindingComplete = true;

  const out = await CheckNDirectBindingSeed0(await baseOptions0({ manifestOverride: manifest }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NDirectBindingSeed.Manifest.directCheckerBindingComplete');
});

test('N direct-binding seed rejects N inventory mismatch', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.inventoryEntries.find((entry) => entry.id === 'TL-005-N').sourceLabel = 'NotN';

  const out = await CheckNDirectBindingSeed0(await baseOptions0({ inventoryOverride: inventory }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NDirectBindingSeed.InventoryNMismatch');
});

test('N direct-binding seed rejects coverage row direct-binding flip', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries.find((entry) => entry.id === 'COV-005-N').directCheckerBindingComplete = true;

  const out = await CheckNDirectBindingSeed0(await baseOptions0({ matrixOverride: matrix }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NDirectBindingSeed.MatrixNMismatch');
});

test('N direct-binding seed rejects closure row surface mismatch', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-005-N').nextDirectBindingSurface = 'wrong-checker.mjs';

  const out = await CheckNDirectBindingSeed0(await baseOptions0({ closureOverride: closure }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NDirectBindingSeed.ClosureNMismatch');
});

test('N direct-binding seed rejects unexpected closure gap', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-005-N').blockingGaps = ['GAP-001-UnrestrictedFinalSoundness'];

  const out = await CheckNDirectBindingSeed0(await baseOptions0({ closureOverride: closure }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NDirectBindingSeed.ClosureNMismatch');
});

test('N direct-binding seed rejects missing proof obligation entry', async () => {
  const obligations = clone0(await json0('proof-obligations/OBLIGATION_LEDGER.json'));
  obligations.obligations = obligations.obligations.filter((entry) => entry.id !== 'OBL-020-NDirectBindingSeed');

  const out = await CheckNDirectBindingSeed0(await baseOptions0({ obligationsOverride: obligations }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NDirectBindingSeed.ObligationMissing');
});

test('N direct-binding seed rejects hardening ledger overclaim', async () => {
  const totality = clone0(await json0('checker-totality/CHECKER_TOTALITY_AUDIT.json'));
  totality.fullCheckerTotalityProved = true;

  const out = await CheckNDirectBindingSeed0(await baseOptions0({ totalityOverride: totality }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NDirectBindingSeed.TotalityLedgerMismatch');
});

test('N direct-binding seed rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.nDirectBindingSeedCoordinate;

  const out = await CheckNDirectBindingSeed0(await baseOptions0({ statusOverride: status }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'NDirectBindingSeed.StatusCoordinate');
});

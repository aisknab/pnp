import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckEDirectBindingSeed0 } from '../pcc-direct-bind-verifydw-soundness0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

async function baseOptions0(overrides = {}) {
  return {
    manifestOverride: await json0('report-bindings/direct-bindings/E_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    oracleOverride: await json0('oracle-audit/NO_HIDDEN_ORACLE_AUDIT.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
    ...overrides,
  };
}

test('E direct-binding seed accepts current manifest and linked ledgers', async () => {
  const out = await CheckEDirectBindingSeed0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-E-VERIFYDW-SOUNDNESS-SEED-2026-06-27-01');
  assert.equal(out.eDirectBindingSeedReady, true);
  assert.equal(out.boundInventoryEntryId, 'TL-004-E');
  assert.equal(out.boundCoverageEntryId, 'COV-004-E');
  assert.equal(out.boundClosureEntryId, 'DCC-004-E');
  assert.deepEqual(out.coveredEComponents, [
    'E.VerifyDWSoundnessSurface',
    'E.ObligationFlatteningSurface',
    'E.NoHiddenOracleExecutableBoundary',
    'E.NoHiddenOracleSemanticCompletenessGap',
  ]);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalETheoremDischarged, false);
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

test('E direct-binding seed rejects public theorem activation', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/E_DIRECT_BINDING_SEED.json'));
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckEDirectBindingSeed0(await baseOptions0({ manifestOverride: manifest }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'EDirectBindingSeed.PublicEmission');
});

test('E direct-binding seed rejects direct binding completion overclaim', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/E_DIRECT_BINDING_SEED.json'));
  manifest.directCheckerBindingComplete = true;

  const out = await CheckEDirectBindingSeed0(await baseOptions0({ manifestOverride: manifest }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'EDirectBindingSeed.Manifest.directCheckerBindingComplete');
});

test('E direct-binding seed rejects E inventory mismatch', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.inventoryEntries.find((entry) => entry.id === 'TL-004-E').sourceLabel = 'NotE';

  const out = await CheckEDirectBindingSeed0(await baseOptions0({ inventoryOverride: inventory }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'EDirectBindingSeed.InventoryEMismatch');
});

test('E direct-binding seed rejects coverage row direct-binding flip', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries.find((entry) => entry.id === 'COV-004-E').directCheckerBindingComplete = true;

  const out = await CheckEDirectBindingSeed0(await baseOptions0({ matrixOverride: matrix }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'EDirectBindingSeed.MatrixEMismatch');
});

test('E direct-binding seed rejects closure row surface mismatch', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-004-E').nextDirectBindingSurface = 'wrong-checker.mjs';

  const out = await CheckEDirectBindingSeed0(await baseOptions0({ closureOverride: closure }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'EDirectBindingSeed.ClosureEMismatch');
});

test('E direct-binding seed rejects missing no-hidden-oracle gap on closure row', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-004-E').blockingGaps = [];

  const out = await CheckEDirectBindingSeed0(await baseOptions0({ closureOverride: closure }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'EDirectBindingSeed.ClosureGapMissing');
});

test('E direct-binding seed rejects missing proof obligation entry', async () => {
  const obligations = clone0(await json0('proof-obligations/OBLIGATION_LEDGER.json'));
  obligations.obligations = obligations.obligations.filter((entry) => entry.id !== 'OBL-019-EDirectBindingSeed');

  const out = await CheckEDirectBindingSeed0(await baseOptions0({ obligationsOverride: obligations }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'EDirectBindingSeed.ObligationMissing');
});

test('E direct-binding seed rejects no-hidden-oracle audit overclaim', async () => {
  const oracle = clone0(await json0('oracle-audit/NO_HIDDEN_ORACLE_AUDIT.json'));
  oracle.fullNoHiddenOracleProved = true;

  const out = await CheckEDirectBindingSeed0(await baseOptions0({ oracleOverride: oracle }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'EDirectBindingSeed.NoHiddenOracleAuditMismatch');
});

test('E direct-binding seed rejects GAP-005 closure overclaim', async () => {
  const gaps = clone0(await json0('proof-obligations/GAP_LEDGER.json'));
  gaps.gaps.find((entry) => entry.id === 'GAP-005-NoHiddenOracleSemanticCompleteness').status = 'closed';

  const out = await CheckEDirectBindingSeed0(await baseOptions0({ gapsOverride: gaps }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'EDirectBindingSeed.Gap005Mismatch');
});

test('E direct-binding seed rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.eDirectBindingSeedCoordinate;

  const out = await CheckEDirectBindingSeed0(await baseOptions0({ statusOverride: status }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'EDirectBindingSeed.StatusCoordinate');
});

import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckReportTheoremCoverageMatrix0 } from '../pcc-report-theorem-coverage-matrix0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('report theorem coverage matrix accepts current matrix and linked ledgers', async () => {
  const out = await CheckReportTheoremCoverageMatrix0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-REPORT-THEOREM-COVERAGE-MATRIX-2026-06-27-01');
  assert.equal(out.coverageMatrixReady, true);
  assert.equal(out.allInventoryEntriesHaveCoverageRows, true);
  assert.equal(out.releaseCriticalEntriesHaveBoundaryRows, true);
  assert.equal(out.allInventoryEntriesDirectCheckerBound, false);
  assert.equal(out.fullHistoricalReportTheoremCoverageProved, false);
  assert.equal(out.publicTheoremEmissionAllowedByCoverage, false);
  assert.equal(out.inventoryEntryCount, 27);
  assert.equal(out.coverageEntryCount, 27);
  assert.equal(out.directCheckerBindingCompleteCount, 0);
  assert.equal(out.releaseCriticalCoverageEntryCount, 2);
  assert.ok(out.evidenceFileCount > 0);
  assert.equal(out.coverageDigestSha256.length, 64);
  assert.equal(out.evidenceDigestSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('report theorem coverage matrix rejects public theorem activation', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckReportTheoremCoverageMatrix0({
    matrixOverride: matrix,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageMatrix.PublicEmission');
});

test('report theorem coverage matrix rejects direct checker binding overclaim', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries[0].directCheckerBindingComplete = true;

  const out = await CheckReportTheoremCoverageMatrix0({
    matrixOverride: matrix,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageMatrix.DirectBindingOverclaim');
});

test('report theorem coverage matrix rejects full historical coverage overclaim', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.fullHistoricalReportTheoremCoverageProved = true;

  const out = await CheckReportTheoremCoverageMatrix0({
    matrixOverride: matrix,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageMatrix.Flag');
});

test('report theorem coverage matrix rejects changed coverage row ordering', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  const tmp = matrix.coverageEntries[0];
  matrix.coverageEntries[0] = matrix.coverageEntries[1];
  matrix.coverageEntries[1] = tmp;

  const out = await CheckReportTheoremCoverageMatrix0({
    matrixOverride: matrix,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageMatrix.CoverageIds');
});

test('report theorem coverage matrix rejects source label mismatch with inventory', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries[0].sourceLabel = 'NotBase';

  const out = await CheckReportTheoremCoverageMatrix0({
    matrixOverride: matrix,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageMatrix.SourceLabelMismatch');
});

test('report theorem coverage matrix rejects release-critical rows without boundary coverage', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries.find((entry) => entry.inventoryEntryId === 'TL-026-Final').coverageClass = 'inventory-ledger-surface';

  const out = await CheckReportTheoremCoverageMatrix0({
    matrixOverride: matrix,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageMatrix.ReleaseCriticalCoverage');
});

test('report theorem coverage matrix rejects coverage rows that discharge public theorem', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries[0].dischargesPublicTheorem = true;

  const out = await CheckReportTheoremCoverageMatrix0({
    matrixOverride: matrix,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageMatrix.EntryPublicEmission');
});

test('report theorem coverage matrix rejects missing evidence files', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries[0].evidenceFiles.push('missing/theorem-coverage-evidence.json');

  const out = await CheckReportTheoremCoverageMatrix0({
    matrixOverride: matrix,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageMatrix.PathMissing');
});

test('report theorem coverage matrix rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.reportTheoremCoverageMatrixCoordinate;

  const out = await CheckReportTheoremCoverageMatrix0({
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageMatrix.StatusCoordinate');
});

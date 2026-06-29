import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckReportTheoremCoverageClosurePlan0 } from '../pcc-report-theorem-coverage-closure-plan0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('report theorem coverage closure plan accepts current plan and matrix linkage', async () => {
  const out = await CheckReportTheoremCoverageClosurePlan0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-REPORT-THEOREM-COVERAGE-CLOSURE-PLAN-2026-06-27-01');
  assert.equal(out.closurePlanReady, true);
  assert.equal(out.allCoverageRowsHaveClosureEntries, true);
  assert.equal(out.allInventoryRowsDirectCheckerBound, false);
  assert.equal(out.directCheckerBindingCompleteCount, 0);
  assert.equal(out.fullHistoricalReportTheoremCoverageProved, false);
  assert.equal(out.publicTheoremEmissionAllowedByClosurePlan, false);
  assert.equal(out.closureEntryCount, 27);
  assert.equal(out.directBindingTargetCount, 27);
  assert.ok(out.unrestrictedFinalSoundnessBlockedCount > 0);
  assert.equal(out.releaseBoundaryBlockedCount, 2);
  assert.ok(out.evidenceFileCount > 0);
  assert.equal(out.closureDigestSha256.length, 64);
  assert.equal(out.evidenceDigestSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('report theorem coverage closure plan rejects public theorem activation', async () => {
  const plan = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  plan.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckReportTheoremCoverageClosurePlan0({
    planOverride: plan,
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageClosurePlan.PublicEmission');
});

test('report theorem coverage closure plan rejects direct binding overclaim', async () => {
  const plan = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  plan.closureEntries[0].mayFlipDirectCheckerBindingComplete = true;

  const out = await CheckReportTheoremCoverageClosurePlan0({
    planOverride: plan,
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageClosurePlan.FlipFlag');
});

test('report theorem coverage closure plan rejects full historical coverage overclaim', async () => {
  const plan = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  plan.fullHistoricalReportTheoremCoverageProved = true;

  const out = await CheckReportTheoremCoverageClosurePlan0({
    planOverride: plan,
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageClosurePlan.Flag');
});

test('report theorem coverage closure plan rejects changed closure row ordering', async () => {
  const plan = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  const tmp = plan.closureEntries[0];
  plan.closureEntries[0] = plan.closureEntries[1];
  plan.closureEntries[1] = tmp;

  const out = await CheckReportTheoremCoverageClosurePlan0({
    planOverride: plan,
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageClosurePlan.ClosureIds');
});

test('report theorem coverage closure plan rejects matrix mismatch', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries[0].sourceLabel = 'NotBase';

  const out = await CheckReportTheoremCoverageClosurePlan0({
    planOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    matrixOverride: matrix,
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageClosurePlan.MatrixAlignment');
});

test('report theorem coverage closure plan rejects release-critical row unblocking', async () => {
  const plan = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  const finalEntry = plan.closureEntries.find((entry) => entry.sourceLabel === 'Final');
  finalEntry.closureStatus = 'direct-binding-needed';

  const out = await CheckReportTheoremCoverageClosurePlan0({
    planOverride: plan,
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageClosurePlan.ReleaseBoundaryStatus');
});

test('report theorem coverage closure plan rejects missing GAP-001 on unrestricted block', async () => {
  const plan = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  const rwEntry = plan.closureEntries.find((entry) => entry.sourceLabel === 'RW');
  rwEntry.blockingGaps = ['GAP-004-FiniteToUnboundedUniformity'];

  const out = await CheckReportTheoremCoverageClosurePlan0({
    planOverride: plan,
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageClosurePlan.UnrestrictedGapMissing');
});

test('report theorem coverage closure plan rejects coverage row public emission overclaim', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries[0].dischargesPublicTheorem = true;

  const out = await CheckReportTheoremCoverageClosurePlan0({
    planOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    matrixOverride: matrix,
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageClosurePlan.MatrixOverclaim');
});

test('report theorem coverage closure plan rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.reportTheoremCoverageClosurePlanCoordinate;

  const out = await CheckReportTheoremCoverageClosurePlan0({
    planOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremCoverageClosurePlan.StatusCoordinate');
});

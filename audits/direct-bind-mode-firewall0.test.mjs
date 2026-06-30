import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckModeDirectBindingSeed0 } from '../pcc-direct-bind-mode-firewall0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('Mode direct-binding seed accepts current manifest and linked ledgers', async () => {
  const out = await CheckModeDirectBindingSeed0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-MODE-FIREWALL-SEED-2026-06-27-01');
  assert.equal(out.modeDirectBindingSeedReady, true);
  assert.equal(out.boundInventoryEntryId, 'TL-003-Mode');
  assert.equal(out.boundCoverageEntryId, 'COV-003-Mode');
  assert.equal(out.boundClosureEntryId, 'DCC-003-Mode');
  assert.deepEqual(out.coveredModeComponents, [
    'Mode.FullToQuotientProjectionSurface',
    'Mode.QuotientEqualityNonconstructiveFirewall',
    'Mode.TransferIdentitySurface',
    'Mode.ProjectionDefectNonnegativeSurface',
  ]);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalModeTheoremDischarged, false);
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

test('Mode direct-binding seed rejects public theorem activation', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/MODE_DIRECT_BINDING_SEED.json'));
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckModeDirectBindingSeed0({
    manifestOverride: manifest,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    kernelOverride: await json0('kernel/PNP_MINIMAL_KERNEL.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ModeDirectBindingSeed.PublicEmission');
});

test('Mode direct-binding seed rejects direct binding completion overclaim', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/MODE_DIRECT_BINDING_SEED.json'));
  manifest.directCheckerBindingComplete = true;

  const out = await CheckModeDirectBindingSeed0({
    manifestOverride: manifest,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    kernelOverride: await json0('kernel/PNP_MINIMAL_KERNEL.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ModeDirectBindingSeed.Manifest.directCheckerBindingComplete');
});

test('Mode direct-binding seed rejects Mode inventory mismatch', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.inventoryEntries.find((entry) => entry.id === 'TL-003-Mode').sourceLabel = 'NotMode';

  const out = await CheckModeDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/MODE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: inventory,
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    kernelOverride: await json0('kernel/PNP_MINIMAL_KERNEL.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ModeDirectBindingSeed.InventoryModeMismatch');
});

test('Mode direct-binding seed rejects coverage row direct-binding flip', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries.find((entry) => entry.id === 'COV-003-Mode').directCheckerBindingComplete = true;

  const out = await CheckModeDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/MODE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: matrix,
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    kernelOverride: await json0('kernel/PNP_MINIMAL_KERNEL.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ModeDirectBindingSeed.MatrixModeMismatch');
});

test('Mode direct-binding seed rejects closure row surface mismatch', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-003-Mode').nextDirectBindingSurface = 'wrong-checker.mjs';

  const out = await CheckModeDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/MODE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: closure,
    kernelOverride: await json0('kernel/PNP_MINIMAL_KERNEL.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ModeDirectBindingSeed.ClosureModeMismatch');
});

test('Mode direct-binding seed rejects missing minimal-kernel rule', async () => {
  const kernel = clone0(await json0('kernel/PNP_MINIMAL_KERNEL.json'));
  kernel.proofKernel.primitiveRules = kernel.proofKernel.primitiveRules.filter((rule) => rule !== 'Transport');

  const out = await CheckModeDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/MODE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    kernelOverride: kernel,
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ModeDirectBindingSeed.KernelRuleMissing');
});

test('Mode direct-binding seed rejects missing proof obligation entry', async () => {
  const obligations = clone0(await json0('proof-obligations/OBLIGATION_LEDGER.json'));
  obligations.obligations = obligations.obligations.filter((entry) => entry.id !== 'OBL-018-ModeDirectBindingSeed');

  const out = await CheckModeDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/MODE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    kernelOverride: await json0('kernel/PNP_MINIMAL_KERNEL.json'),
    obligationsOverride: obligations,
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ModeDirectBindingSeed.ObligationMissing');
});

test('Mode direct-binding seed rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.modeDirectBindingSeedCoordinate;

  const out = await CheckModeDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/MODE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    kernelOverride: await json0('kernel/PNP_MINIMAL_KERNEL.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ModeDirectBindingSeed.StatusCoordinate');
});

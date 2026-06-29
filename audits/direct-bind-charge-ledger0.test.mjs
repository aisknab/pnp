import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckCHGDirectBindingSeed0 } from '../pcc-direct-bind-charge-ledger0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('CHG direct-binding seed accepts current manifest and linked ledgers', async () => {
  const out = await CheckCHGDirectBindingSeed0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-CHG-CHARGE-LEDGER-SEED-2026-06-27-01');
  assert.equal(out.chgDirectBindingSeedReady, true);
  assert.equal(out.boundInventoryEntryId, 'TL-002-CHG');
  assert.equal(out.boundCoverageEntryId, 'COV-002-CHG');
  assert.equal(out.boundClosureEntryId, 'DCC-002-CHG');
  assert.deepEqual(out.coveredCHGComponents, [
    'CHG.GlobalChargeLedgerSurface',
    'CHG.MaterializerOwnershipSurface',
    'CHG.ExactSizeEquationSurface',
    'CHG.ChargeSoundnessActivationBoundary',
  ]);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalCHGTheoremDischarged, false);
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

test('CHG direct-binding seed rejects public theorem activation', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/CHG_DIRECT_BINDING_SEED.json'));
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckCHGDirectBindingSeed0({
    manifestOverride: manifest,
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
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CHGDirectBindingSeed.PublicEmission');
});

test('CHG direct-binding seed rejects direct binding completion overclaim', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/CHG_DIRECT_BINDING_SEED.json'));
  manifest.directCheckerBindingComplete = true;

  const out = await CheckCHGDirectBindingSeed0({
    manifestOverride: manifest,
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
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CHGDirectBindingSeed.Manifest.directCheckerBindingComplete');
});

test('CHG direct-binding seed rejects CHG inventory mismatch', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.inventoryEntries.find((entry) => entry.id === 'TL-002-CHG').sourceLabel = 'NotCHG';

  const out = await CheckCHGDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/CHG_DIRECT_BINDING_SEED.json'),
    inventoryOverride: inventory,
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    totalityOverride: await json0('checker-totality/CHECKER_TOTALITY_AUDIT.json'),
    mutationsOverride: await json0('checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json'),
    ruleCoverageOverride: await json0('semantic-kernel/RULE_FAMILY_COVERAGE.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CHGDirectBindingSeed.InventoryCHGMismatch');
});

test('CHG direct-binding seed rejects coverage row direct-binding flip', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries.find((entry) => entry.id === 'COV-002-CHG').directCheckerBindingComplete = true;

  const out = await CheckCHGDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/CHG_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: matrix,
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    totalityOverride: await json0('checker-totality/CHECKER_TOTALITY_AUDIT.json'),
    mutationsOverride: await json0('checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json'),
    ruleCoverageOverride: await json0('semantic-kernel/RULE_FAMILY_COVERAGE.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CHGDirectBindingSeed.MatrixCHGMismatch');
});

test('CHG direct-binding seed rejects closure row surface mismatch', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-002-CHG').nextDirectBindingSurface = 'wrong-checker.mjs';

  const out = await CheckCHGDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/CHG_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: closure,
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    totalityOverride: await json0('checker-totality/CHECKER_TOTALITY_AUDIT.json'),
    mutationsOverride: await json0('checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json'),
    ruleCoverageOverride: await json0('semantic-kernel/RULE_FAMILY_COVERAGE.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CHGDirectBindingSeed.ClosureCHGMismatch');
});

test('CHG direct-binding seed rejects missing proof obligation entry', async () => {
  const obligations = clone0(await json0('proof-obligations/OBLIGATION_LEDGER.json'));
  obligations.obligations = obligations.obligations.filter((entry) => entry.id !== 'OBL-017-CHGDirectBindingSeed');

  const out = await CheckCHGDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/CHG_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    obligationsOverride: obligations,
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    totalityOverride: await json0('checker-totality/CHECKER_TOTALITY_AUDIT.json'),
    mutationsOverride: await json0('checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json'),
    ruleCoverageOverride: await json0('semantic-kernel/RULE_FAMILY_COVERAGE.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CHGDirectBindingSeed.ObligationMissing');
});

test('CHG direct-binding seed rejects mutated hardening ledger', async () => {
  const mutations = clone0(await json0('checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json'));
  mutations.fullNegativeMutationCoverageProved = true;

  const out = await CheckCHGDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/CHG_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    totalityOverride: await json0('checker-totality/CHECKER_TOTALITY_AUDIT.json'),
    mutationsOverride: mutations,
    ruleCoverageOverride: await json0('semantic-kernel/RULE_FAMILY_COVERAGE.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CHGDirectBindingSeed.MutationLedgerMismatch');
});

test('CHG direct-binding seed rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.chgDirectBindingSeedCoordinate;

  const out = await CheckCHGDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/CHG_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    totalityOverride: await json0('checker-totality/CHECKER_TOTALITY_AUDIT.json'),
    mutationsOverride: await json0('checker-mutations/NEGATIVE_CHECKER_MUTATIONS.json'),
    ruleCoverageOverride: await json0('semantic-kernel/RULE_FAMILY_COVERAGE.json'),
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'CHGDirectBindingSeed.StatusCoordinate');
});

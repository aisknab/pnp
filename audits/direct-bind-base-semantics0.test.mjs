import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckBaseDirectBindingSeed0 } from '../pcc-direct-bind-base-semantics0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('Base direct-binding seed accepts current manifest and linked ledgers', async () => {
  const out = await CheckBaseDirectBindingSeed0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-BASE-SEMANTICS-SEED-2026-06-27-01');
  assert.equal(out.baseDirectBindingSeedReady, true);
  assert.equal(out.boundInventoryEntryId, 'TL-001-Base');
  assert.equal(out.boundCoverageEntryId, 'COV-001-Base');
  assert.equal(out.boundClosureEntryId, 'DCC-001-Base');
  assert.deepEqual(out.coveredBaseComponents, [
    'Base.DirectWireNANDSyntax',
    'Base.OpenFunctionEvaluation',
    'Base.CompatibleReplacementSemantics',
    'Base.SlackLawLedgerSurface',
  ]);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalBaseTheoremDischarged, false);
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

test('Base direct-binding seed rejects public theorem activation', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json'));
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckBaseDirectBindingSeed0({
    manifestOverride: manifest,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    semanticsOverride: await json0('semantics/nand-direct-wire-spec.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'BaseDirectBindingSeed.PublicEmission');
});

test('Base direct-binding seed rejects direct binding completion overclaim', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json'));
  manifest.directCheckerBindingComplete = true;

  const out = await CheckBaseDirectBindingSeed0({
    manifestOverride: manifest,
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    semanticsOverride: await json0('semantics/nand-direct-wire-spec.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'BaseDirectBindingSeed.Manifest.directCheckerBindingComplete');
});

test('Base direct-binding seed rejects Base inventory mismatch', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.inventoryEntries.find((entry) => entry.id === 'TL-001-Base').sourceLabel = 'NotBase';

  const out = await CheckBaseDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: inventory,
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    semanticsOverride: await json0('semantics/nand-direct-wire-spec.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'BaseDirectBindingSeed.InventoryBaseMismatch');
});

test('Base direct-binding seed rejects coverage row direct-binding flip', async () => {
  const matrix = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'));
  matrix.coverageEntries.find((entry) => entry.id === 'COV-001-Base').directCheckerBindingComplete = true;

  const out = await CheckBaseDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: matrix,
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    semanticsOverride: await json0('semantics/nand-direct-wire-spec.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'BaseDirectBindingSeed.MatrixBaseMismatch');
});

test('Base direct-binding seed rejects closure row surface mismatch', async () => {
  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((entry) => entry.id === 'DCC-001-Base').nextDirectBindingSurface = 'wrong-checker.mjs';

  const out = await CheckBaseDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: closure,
    semanticsOverride: await json0('semantics/nand-direct-wire-spec.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'BaseDirectBindingSeed.ClosureBaseMismatch');
});

test('Base direct-binding seed rejects missing semantics concept', async () => {
  const semantics = clone0(await json0('semantics/nand-direct-wire-spec.json'));
  semantics.coveredConcepts = semantics.coveredConcepts.filter((concept) => concept !== 'compatible replacement semantics for same boundary and output arity');

  const out = await CheckBaseDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    semanticsOverride: semantics,
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'BaseDirectBindingSeed.SemanticsConceptMissing');
});

test('Base direct-binding seed rejects missing proof obligation entry', async () => {
  const obligations = clone0(await json0('proof-obligations/OBLIGATION_LEDGER.json'));
  obligations.obligations = obligations.obligations.filter((entry) => entry.id !== 'OBL-016-BaseDirectBindingSeed');

  const out = await CheckBaseDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    semanticsOverride: await json0('semantics/nand-direct-wire-spec.json'),
    obligationsOverride: obligations,
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'BaseDirectBindingSeed.ObligationMissing');
});

test('Base direct-binding seed rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.baseDirectBindingSeedCoordinate;

  const out = await CheckBaseDirectBindingSeed0({
    manifestOverride: await json0('report-bindings/direct-bindings/BASE_DIRECT_BINDING_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    semanticsOverride: await json0('semantics/nand-direct-wire-spec.json'),
    obligationsOverride: await json0('proof-obligations/OBLIGATION_LEDGER.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'BaseDirectBindingSeed.StatusCoordinate');
});

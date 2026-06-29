import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckReportTheoremInventory0 } from '../pcc-report-theorem-inventory0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}

function clone0(value) {
  return JSON.parse(JSON.stringify(value));
}

test('report theorem inventory accepts current inventory and linked ledgers', async () => {
  const out = await CheckReportTheoremInventory0({ writeOutput: false });

  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-REPORT-THEOREM-INVENTORY-2026-06-27-01');
  assert.equal(out.inventoryReady, true);
  assert.equal(out.inventoryEntryCount, 27);
  assert.equal(out.expectedInventoryEntryCount, 27);
  assert.equal(out.releaseCriticalSpineCoveredByBindings, true);
  assert.equal(out.allNumberedReportTheoremsInventoried, false);
  assert.equal(out.fullHistoricalReportTheoremInventoryExhaustive, false);
  assert.equal(out.allInventoryEntriesBoundToCheckers, false);
  assert.equal(out.publicTheoremEmissionAllowedByInventory, false);
  assert.equal(out.proseOnlyTheoremActivationAllowedByInventory, false);
  assert.ok(out.evidenceFileCount >= 7);
  assert.equal(out.evidenceDigestSha256.length, 64);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
  assert.deepEqual(out.remainingBlockers, [
    'Release.UnrestrictedFinalSoundness',
    'ExternalReview.Acceptance',
  ]);
});

test('report theorem inventory rejects public theorem activation', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.claimBoundary.publicTheoremEmissionAllowed = true;

  const out = await CheckReportTheoremInventory0({
    inventoryOverride: inventory,
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremInventory.PublicEmission');
});

test('report theorem inventory rejects exhaustive numbered-theorem overclaim', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.inventoryScope.allNumberedReportTheoremsInventoried = true;

  const out = await CheckReportTheoremInventory0({
    inventoryOverride: inventory,
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremInventory.AllNumberedOverclaim');
});

test('report theorem inventory rejects all-bound-to-checkers overclaim', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.inventoryScope.allInventoryEntriesBoundToCheckers = true;

  const out = await CheckReportTheoremInventory0({
    inventoryOverride: inventory,
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremInventory.AllBoundOverclaim');
});

test('report theorem inventory rejects changed entry ordering', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  const tmp = inventory.inventoryEntries[0];
  inventory.inventoryEntries[0] = inventory.inventoryEntries[1];
  inventory.inventoryEntries[1] = tmp;

  const out = await CheckReportTheoremInventory0({
    inventoryOverride: inventory,
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremInventory.EntryIds');
});

test('report theorem inventory rejects inventory entry theorem-emission effect', async () => {
  const inventory = clone0(await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'));
  inventory.inventoryEntries[0].publicEmissionEffect = 'activates-public-theorem';

  const out = await CheckReportTheoremInventory0({
    inventoryOverride: inventory,
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremInventory.EntryPublicEmissionEffect');
});

test('report theorem inventory rejects binding ledger public theorem discharge', async () => {
  const bindings = clone0(await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'));
  bindings.theoremBindings[0].dischargesPublicTheorem = true;

  const out = await CheckReportTheoremInventory0({
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: bindings,
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremInventory.BindingEmission');
});

test('report theorem inventory rejects policy missing inventory coordinate', async () => {
  const policy = clone0(await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'));
  delete policy.reportTheoremInventoryCoordinate;

  const out = await CheckReportTheoremInventory0({
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: policy,
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremInventory.PolicyInventoryCoordinate');
});

test('report theorem inventory rejects missing status coordinate', async () => {
  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.reportTheoremInventoryCoordinate;

  const out = await CheckReportTheoremInventory0({
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    bindingsOverride: await json0('report-bindings/REPORT_THEOREM_BINDINGS.json'),
    policyOverride: await json0('report-bindings/NO_PROSE_ONLY_THEOREM_POLICY.json'),
    statusOverride: status,
    writeOutput: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'ReportTheoremInventory.StatusCoordinate');
});

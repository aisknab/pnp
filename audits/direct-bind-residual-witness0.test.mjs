import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { test } from 'node:test';

import { CheckRWDirectBindingGapSeed0 } from '../pcc-direct-bind-residual-witness0.mjs';

async function json0(pathname) {
  return JSON.parse(await readFile(new URL(`../${pathname}`, import.meta.url), 'utf8'));
}
function clone0(value) { return JSON.parse(JSON.stringify(value)); }
async function base0(overrides = {}) {
  return {
    manifestOverride: await json0('report-bindings/direct-bindings/RW_DIRECT_BINDING_GAP_SEED.json'),
    inventoryOverride: await json0('report-bindings/REPORT_THEOREM_INVENTORY.json'),
    matrixOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_MATRIX.json'),
    closureOverride: await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'),
    gapsOverride: await json0('proof-obligations/GAP_LEDGER.json'),
    finiteOverride: await json0('proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json'),
    statusOverride: await json0('PNP_STATUS.json'),
    writeOutput: false,
    ...overrides,
  };
}

test('RW direct-binding gap seed accepts current linked ledgers', async () => {
  const out = await CheckRWDirectBindingGapSeed0({ writeOutput: false });
  assert.equal(out.tag, 'accept');
  assert.equal(out.coordinate, 'PNP-DIRECT-BIND-RW-RESIDUAL-WITNESS-GAP-SEED-2026-06-27-01');
  assert.equal(out.rwDirectBindingGapSeedReady, true);
  assert.equal(out.directBindingBlockedByGaps, true);
  assert.equal(out.boundInventoryEntryId, 'TL-014-RW');
  assert.equal(out.boundCoverageEntryId, 'COV-014-RW');
  assert.equal(out.boundClosureEntryId, 'DCC-014-RW');
  assert.deepEqual(out.blockingGaps, ['GAP-001-UnrestrictedFinalSoundness', 'GAP-004-FiniteToUnboundedUniformity']);
  assert.equal(out.directCheckerBindingComplete, false);
  assert.equal(out.fullHistoricalRWTheoremDischarged, false);
  assert.equal(out.publicTheoremEmissionAllowedByBinding, false);
  assert.equal(out.publicTheoremEmissionAllowed, false);
  assert.equal(out.finalTheoremReady, false);
  assert.deepEqual(out.activeFinalNodeIds, []);
});

test('RW direct-binding gap seed rejects activation and gap closure overclaims', async () => {
  const manifest = clone0(await json0('report-bindings/direct-bindings/RW_DIRECT_BINDING_GAP_SEED.json'));
  manifest.claimBoundary.publicTheoremEmissionAllowed = true;
  assert.equal((await CheckRWDirectBindingGapSeed0(await base0({ manifestOverride: manifest }))).coord, 'RWDirectBindingGapSeed.BoundaryMismatch');

  const closure = clone0(await json0('report-bindings/REPORT_THEOREM_COVERAGE_CLOSURE_PLAN.json'));
  closure.closureEntries.find((x) => x.id === 'DCC-014-RW').blockingGaps = [];
  assert.equal((await CheckRWDirectBindingGapSeed0(await base0({ closureOverride: closure }))).coord, 'RWDirectBindingGapSeed.ClosureGaps');

  const finite = clone0(await json0('proof-obligations/FINITE_TO_UNBOUNDED_FAMILY_AUDIT.json'));
  finite.uniformAllInputSizesCoverageProved = true;
  assert.equal((await CheckRWDirectBindingGapSeed0(await base0({ finiteOverride: finite }))).coord, 'RWDirectBindingGapSeed.FiniteAuditMismatch');

  const status = clone0(await json0('PNP_STATUS.json'));
  delete status.rwDirectBindingGapSeedCoordinate;
  assert.equal((await CheckRWDirectBindingGapSeed0(await base0({ statusOverride: status }))).coord, 'RWDirectBindingGapSeed.StatusCoordinate');
});

import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  BOOT_BATCH0_REQUIRED_ROWS,
  CheckBootBatch0,
  makeBootstrapB0Rows0,
} from '../pcc-boot0.mjs';

test('CheckBootBatch0 accepts the required B0 bootstrap coverage families', async () => {
  const out = await CheckBootBatch0({
    kind: 'BootBatch0',
    version: 0,
    batchId: 'B0',
    rows: makeBootstrapB0Rows0(),
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckBootBatch0');
  assert.equal(out.NF.batchId, 'B0');
  assert.equal(out.NF.rowCount, BOOT_BATCH0_REQUIRED_ROWS.length);
  assert.equal(out.NF.coverage.required, true);
  assert.equal(out.NF.coverage.familyCount, BOOT_BATCH0_REQUIRED_ROWS.length);

  const coveredFamilies = new Set(out.NF.coverage.families.map((entry) => entry.family));

  for (const required of BOOT_BATCH0_REQUIRED_ROWS) {
    assert.equal(coveredFamilies.has(required.family), true);
  }
});

test('CheckBootBatch0 rejects B0 when a required coverage family is missing', async () => {
  const rows = makeBootstrapB0Rows0().filter((row) => row.PackageID !== 'BTruthEval');

  const out = await CheckBootBatch0({
    kind: 'BootBatch0',
    version: 0,
    batchId: 'B0',
    rows,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckBootBatch0');
  assert.equal(out.Coord, 'CheckBootBatch0.coverage');
  assert.deepEqual(out.Path, ['rows', 'coverage', 'BTruthEval']);
  assert.equal(out.Witness.reason, 'B0 is missing required bootstrap row family');
});

test('CheckBootBatch0 rejects B0 when a coverage row is not full-mode', async () => {
  const rows = makeBootstrapB0Rows0();
  const modeIndex = rows.findIndex((row) => row.PackageID === 'BMode');

  rows[modeIndex] = {
    ...rows[modeIndex],
    ModeKey: 'Quot',
  };

  const out = await CheckBootBatch0({
    kind: 'BootBatch0',
    version: 0,
    batchId: 'B0',
    rows,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckBootBatch0');
  assert.equal(out.Coord, 'CheckBootBatch0.row.0008');
  assert.deepEqual(out.Path, ['rows', modeIndex, 'RowKey']);
});
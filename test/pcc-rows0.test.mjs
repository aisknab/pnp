import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckBatchDeps0,
  CheckRowFamilies0,
  CheckRows0,
  ROW_BATCH_IDS0,
  ROW_REQUIRED_FAMILIES0,
  makeSyntheticRowPack0,
} from '../pcc-rows0.mjs';

test('CheckRows0 accepts the synthetic generated row package', async () => {
  const out = await CheckRows0(makeSyntheticRowPack0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckRows0');
  assert.equal(out.NF.kind, 'RowPack0NF');
  assert.equal(out.NF.batchCount, ROW_BATCH_IDS0.length);
  assert.equal(out.NF.familyCount, ROW_REQUIRED_FAMILIES0.length);
  assert.equal(out.NF.rowCount, ROW_REQUIRED_FAMILIES0.length);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckBatchDeps0 accepts the synthetic B0 through B12 batch inventory', async () => {
  const pack = makeSyntheticRowPack0();
  const out = await CheckBatchDeps0(pack.BatchInv);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckBatchDeps0');
  assert.equal(out.NF.batchCount, ROW_BATCH_IDS0.length);
  assert.deepEqual(out.NF.batches.map((entry) => entry.batchId), ROW_BATCH_IDS0);
});

test('CheckRowFamilies0 accepts required generated row-family coverage', async () => {
  const out = await CheckRowFamilies0(makeSyntheticRowPack0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckRowFamilies0');
  assert.equal(out.NF.familyCount, ROW_REQUIRED_FAMILIES0.length);
});

test('CheckRows0 rejects a missing required row family', async () => {
  const pack = makeSyntheticRowPack0();

  pack.Rows = pack.Rows.filter((row) => row.FamilyID !== 'PkgC');

  const out = await CheckRows0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckRows0');
  assert.equal(out.Coord, 'CheckRows0.families');
  assert.deepEqual(out.Path, ['Rows', 'coverage', 'PkgC']);
  assert.equal(out.Witness.reason, 'inner checker rejected');
  assert.equal(out.Witness.detail.inner.witness.reason, 'RowPack0 is missing a required row family');
});

test('CheckRows0 rejects duplicate row keys with conflicting selected routes', async () => {
  const pack = makeSyntheticRowPack0();
  const source = pack.Rows.find((row) => row.FamilyID === 'BN2');

  pack.Rows = [
    ...pack.Rows,
    {
      ...source,
      SelectedRoute: 'Reject',
      ActiveRouteSet: ['Reject'],
      CandidateRoutes: ['Accept', 'Reject'],
    },
  ];

  const out = await CheckRows0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckRows0');
  assert.equal(out.Coord, 'CheckRows0.duplicates');
  assert.deepEqual(out.Path, ['Rows', 'duplicates']);
  assert.equal(out.Witness.reason, 'duplicate row conflict');
});

test('CheckRows0 rejects route priority downgrade', async () => {
  const pack = makeSyntheticRowPack0();
  const index = pack.Rows.findIndex((row) => row.FamilyID === 'R');

  pack.Rows[index] = {
    ...pack.Rows[index],
    ActiveRouteSet: ['Gain', 'Neutral'],
    CandidateRoutes: ['Gain', 'Neutral'],
    SelectedRoute: 'Neutral',
  };

  const out = await CheckRows0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckRows0');
  assert.equal(out.Coord, 'CheckRows0.routes');
  assert.deepEqual(out.Path, ['Rows', index, 'SelectedRoute']);
  assert.equal(out.Witness.reason, 'SelectedRoute must be the highest-priority active route');
});

test('CheckRows0 rejects hash-index lookup without full key or canonical byte comparison', async () => {
  const pack = makeSyntheticRowPack0();
  const firstHex = pack.Rows[0].HashKey.hex;

  pack.HashIndex = {
    ...pack.HashIndex,
    buckets: {
      ...pack.HashIndex.buckets,
      [firstHex]: [
        {
          ...pack.HashIndex.buckets[firstHex][0],
          fullKeyCompared: false,
          canonicalByteCompared: false,
        },
      ],
    },
  };

  const out = await CheckRows0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckRows0');
  assert.equal(out.Coord, 'CheckRows0.hashIndex');
  assert.deepEqual(out.Path, ['HashIndex', 'buckets', firstHex, 0, 'fullKeyCompared']);
  assert.equal(out.Witness.reason, 'HashIndex lookup must be followed by full key or canonical byte comparison');
});

test('CheckBatchDeps0 rejects a forbidden G to O import edge', async () => {
  const pack = makeSyntheticRowPack0();

  pack.BatchInv = {
    ...pack.BatchInv,
    batches: pack.BatchInv.batches.map((entry) => {
      if (entry.batchId !== 'B11') {
        return entry;
      }

      return {
        ...entry,
        imports: ['B10'],
      };
    }),
  };

  const out = await CheckBatchDeps0(pack.BatchInv);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckBatchDeps0');
  assert.equal(out.Coord, 'CheckBatchDeps0.imports');
  assert.deepEqual(out.Path, ['BatchInv', 'B11', 'imports', 0]);
  assert.equal(out.Witness.reason, 'batch import uses a forbidden package edge');
});

test('CheckRows0 rejects executable hidden minimization in a generated row', async () => {
  const pack = makeSyntheticRowPack0();
  const index = pack.Rows.findIndex((row) => row.FamilyID === 'Final');

  pack.Rows[index] = {
    ...pack.Rows[index],
    RawObj: {
      ...pack.Rows[index].RawObj,
      body: ['minimumEquivalent'],
    },
  };

  const out = await CheckRows0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckRows0');
  assert.equal(out.Coord, 'CheckRows0.noHiddenMin');
  assert.deepEqual(out.Path, ['RowPack0', 'Rows', index, 'RawObj', 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});
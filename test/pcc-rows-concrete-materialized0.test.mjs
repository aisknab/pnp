import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedRows0,
  makeConcreteMaterializedRows0,
  makeConcreteMaterializedRowPack0,
  writeConcreteMaterializedRowsFiles0,
} from '../pcc-rows-concrete-materialized0.mjs';

import {
  CheckRows0,
  ROW_REQUIRED_FAMILIES0,
} from '../pcc-rows0.mjs';

test('CheckConcreteMaterializedRows0 accepts concrete materialized RowPack rows', async () => {
  const envelope = await makeConcreteMaterializedRows0();
  const out = await CheckConcreteMaterializedRows0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedRows0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedRows0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.concreteIfaceHash, true);
  assert.equal(out.NF.syntheticIfaceHashCount, 0);
  assert.equal(out.NF.scaffoldMarkerCount, 0);
  assert.equal(out.NF.rowCount, ROW_REQUIRED_FAMILIES0.length);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner CheckRows0 accepts the concrete materialized RowPack core', async () => {
  const rowPack = await makeConcreteMaterializedRowPack0();
  const out = await CheckRows0(rowPack);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckRows0');
  assert.equal(out.NF.kind, 'RowPack0NF');
  assert.equal(out.NF.rowCount, ROW_REQUIRED_FAMILIES0.length);

  for (const row of rowPack.Rows) {
    assert.equal(typeof row.IfaceHash, 'object');
    assert.equal(row.IfaceHash.hex, rowPack.IfaceHash.hex);
    assert.notEqual(row.IfaceHash, 'IfaceDict0.synthetic');
  }
});

test('CheckConcreteMaterializedRows0 rejects a synthetic row IfaceHash marker', async () => {
  const envelope = await makeConcreteMaterializedRows0();

  envelope.RowPack = {
    ...envelope.RowPack,
    Rows: envelope.RowPack.Rows.map((row, index) => index === 0
      ? {
          ...row,
          IfaceHash: 'IfaceDict0.synthetic',
        }
      : row),
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    rowPackDigest: undefined,
  };

  const out = await CheckConcreteMaterializedRows0(envelope, {
    checkRows: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedRows0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedRows0.concreteIfaceHash');
  assert.deepEqual(out.Path, ['RowPack', 'Rows', 0, 'IfaceHash']);
});

test('CheckConcreteMaterializedRows0 rejects stale row ledgers through CheckRows0', async () => {
  const envelope = await makeConcreteMaterializedRows0();

  const firstHex = envelope.RowPack.Rows[0].HashKey.hex;

  envelope.RowPack = {
    ...envelope.RowPack,
    HashIndex: {
      ...envelope.RowPack.HashIndex,
      buckets: {
        ...envelope.RowPack.HashIndex.buckets,
        [firstHex]: [
          {
            ...envelope.RowPack.HashIndex.buckets[firstHex][0],
            fullKeyCompared: false,
            canonicalByteCompared: false,
          },
        ],
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    rowPackDigest: undefined,
  };

  const out = await CheckConcreteMaterializedRows0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedRows0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedRows0.Rows');
  assert.equal(out.Witness.detail.inner.coord, 'CheckRows0.hashIndex');
});

test('writeConcreteMaterializedRowsFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-materialized-rows-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedRowsFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.rowPackPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

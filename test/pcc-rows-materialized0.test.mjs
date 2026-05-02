import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedRows0,
  makeMaterializedRows0,
  writeMaterializedRowsFiles0,
} from '../pcc-rows-materialized0.mjs';

import {
  CheckRows0,
  ROW_BATCH_IDS0,
  ROW_REQUIRED_FAMILIES0,
} from '../pcc-rows0.mjs';

test('CheckMaterializedRows0 accepts a materialized RowPack envelope', async () => {
  const envelope = makeMaterializedRows0();
  const out = await CheckMaterializedRows0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedRows0');
  assert.equal(out.NF.kind, 'MaterializedRows0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.batchCount, ROW_BATCH_IDS0.length);
  assert.equal(out.NF.familyCount, ROW_REQUIRED_FAMILIES0.length);
  assert.equal(out.NF.rowCount, ROW_REQUIRED_FAMILIES0.length);
  assert.equal(out.NF.forbiddenMarkerCount, 0);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner CheckRows0 accepts the materialized RowPack core', async () => {
  const envelope = makeMaterializedRows0();
  const out = await CheckRows0(envelope.RowPack);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckRows0');
  assert.equal(out.NF.kind, 'RowPack0NF');
  assert.equal(out.NF.batchCount, ROW_BATCH_IDS0.length);
  assert.equal(out.NF.familyCount, ROW_REQUIRED_FAMILIES0.length);
});

test('CheckMaterializedRows0 exposes row-check failures', async () => {
  const envelope = makeMaterializedRows0();

  envelope.RowPack = {
    ...envelope.RowPack,
    Rows: envelope.RowPack.Rows.filter((row) => row.FamilyID !== 'PkgC'),
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    rowPackDigest: undefined,
    rowCount: envelope.RowPack.Rows.length,
  };

  const out = await CheckMaterializedRows0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedRows0');
  assert.equal(out.Coord, 'CheckMaterializedRows0.Rows');
  assert.equal(out.Witness.detail.inner.coord, 'CheckRows0.families');
});

test('CheckMaterializedRows0 rejects forbidden fixture marker text', async () => {
  const envelope = makeMaterializedRows0();

  envelope.RowPack = {
    ...envelope.RowPack,
    PiRows: {
      ...envelope.RowPack.PiRows,
      note: 'todo marker must reject',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    rowPackDigest: undefined,
  };

  const out = await CheckMaterializedRows0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedRows0');
  assert.equal(out.Coord, 'CheckMaterializedRows0.fixtureMarkers');
});

test('CheckMaterializedRows0 can strictly reject the current synthetic scaffold marker', async () => {
  const envelope = makeMaterializedRows0();

  const out = await CheckMaterializedRows0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedRows0');
  assert.equal(out.Coord, 'CheckMaterializedRows0.fixtureMarkers');
});

test('CheckMaterializedRows0 rejects stale linkage digests', async () => {
  const envelope = makeMaterializedRows0();

  envelope.Linkage = {
    ...envelope.Linkage,
    rowPackDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckMaterializedRows0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedRows0');
  assert.equal(out.Coord, 'CheckMaterializedRows0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'rowPackDigest']);
});

test('writeMaterializedRowsFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-rows-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeMaterializedRowsFiles0(dir);

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

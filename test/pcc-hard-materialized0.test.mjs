import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedHard0,
  makeMaterializedHard0,
  writeMaterializedHardFiles0,
} from '../pcc-hard-materialized0.mjs';

import {
  CheckHard0,
  HARD_CHECKER_FIELDS0,
  HARD_FORBIDDEN_SYMBOLS0,
  HARD_ROWKEY_FIELDS0,
} from '../pcc-hard0.mjs';

test('CheckMaterializedHard0 accepts a JSON-materialized hardened checker suite', async () => {
  const envelope = makeMaterializedHard0();
  const out = await CheckMaterializedHard0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedHard0');
  assert.equal(out.NF.kind, 'MaterializedHardCheck0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.checkerCount, HARD_CHECKER_FIELDS0.length);
  assert.deepEqual(out.NF.rowKeyFields, HARD_ROWKEY_FIELDS0);
  assert.deepEqual(out.NF.forbiddenSymbols, HARD_FORBIDDEN_SYMBOLS0);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner CheckHard0 accepts the materialized HardCheck core', async () => {
  const envelope = makeMaterializedHard0();
  const out = await CheckHard0(envelope.HardCheck);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckHard0');
  assert.equal(out.NF.kind, 'HardCheck0NF');
  assert.equal(out.NF.checkerCount, HARD_CHECKER_FIELDS0.length);
});

test('CheckMaterializedHard0 rejects fixture marker text in the HardCheck core', async () => {
  const envelope = makeMaterializedHard0();

  envelope.HardCheck = {
    ...envelope.HardCheck,
    PiHard: {
      ...envelope.HardCheck.PiHard,
      note: 'synthetic marker must reject',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    hardCheckDigest: undefined,
  };

  const out = await CheckMaterializedHard0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedHard0');
  assert.equal(out.Coord, 'CheckMaterializedHard0.fixtureMarkers');
});

test('CheckMaterializedHard0 exposes CheckHard0 failures', async () => {
  const envelope = makeMaterializedHard0();

  envelope.HardCheck = {
    ...envelope.HardCheck,
    HashCheck: {
      ...envelope.HardCheck.HashCheck,
      fullKeyCompareAfterHash: false,
      canonicalByteCompareAfterHash: false,
    },
  };

  const out = await CheckMaterializedHard0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedHard0');
  assert.equal(out.Coord, 'CheckMaterializedHard0.HardCheck');
  assert.deepEqual(out.Witness.detail.inner.coord, 'CheckHard0.HashCheck');
});

test('CheckMaterializedHard0 rejects stale linkage digests', async () => {
  const envelope = makeMaterializedHard0();

  envelope.Linkage = {
    ...envelope.Linkage,
    hardCheckDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckMaterializedHard0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedHard0');
  assert.equal(out.Coord, 'CheckMaterializedHard0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'hardCheckDigest']);
});

test('writeMaterializedHardFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-hard-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeMaterializedHardFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.hardPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

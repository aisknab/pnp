import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedLocalPackages0,
  makeMaterializedLocalPackages0,
  writeMaterializedLocalPackagesFiles0,
} from '../pcc-local-packages-materialized0.mjs';

import {
  CheckLocalPackages0,
  LOCAL_PACKAGE_REQUIRED_FAMILIES0,
} from '../pcc-local-packages0.mjs';

test('CheckMaterializedLocalPackages0 accepts a materialized local package envelope', async () => {
  const envelope = makeMaterializedLocalPackages0();
  const out = await CheckMaterializedLocalPackages0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedLocalPackages0');
  assert.equal(out.NF.kind, 'MaterializedLocalPackages0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.familyCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
  assert.equal(out.NF.packageCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner CheckLocalPackages0 accepts the materialized local package core', async () => {
  const envelope = makeMaterializedLocalPackages0();
  const out = await CheckLocalPackages0(envelope.LocalPackages);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.NF.kind, 'LocalPackages0NF');
  assert.equal(out.NF.familyCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
});

test('CheckMaterializedLocalPackages0 exposes local package checker failures', async () => {
  const envelope = makeMaterializedLocalPackages0();
  const index = envelope.LocalPackages.Packages.findIndex((entry) => entry.family === 'R');

  envelope.LocalPackages = {
    ...envelope.LocalPackages,
    Packages: envelope.LocalPackages.Packages.map((entry, entryIndex) => {
      if (entryIndex !== index) {
        return entry;
      }

      return {
        ...entry,
        routes: {
          ...entry.routes,
          constructiveRoutesCompileToVerifyDW: false,
        },
      };
    }),
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    localPackagePackDigest: undefined,
  };

  const out = await CheckMaterializedLocalPackages0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedLocalPackages0');
  assert.equal(out.Coord, 'CheckMaterializedLocalPackages0.LocalPackages');
  assert.equal(out.Witness.detail.inner.coord, 'CheckLocalPackages0.packages');
});

test('CheckMaterializedLocalPackages0 rejects forbidden fixture marker text', async () => {
  const envelope = makeMaterializedLocalPackages0();

  envelope.LocalPackages = {
    ...envelope.LocalPackages,
    PiLocalPackages: {
      ...envelope.LocalPackages.PiLocalPackages,
      note: 'todo marker must reject',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    localPackagePackDigest: undefined,
  };

  const out = await CheckMaterializedLocalPackages0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedLocalPackages0');
  assert.equal(out.Coord, 'CheckMaterializedLocalPackages0.fixtureMarkers');
});

test('CheckMaterializedLocalPackages0 rejects stale declared RowPackDigest', async () => {
  const envelope = makeMaterializedLocalPackages0();

  envelope.LocalPackages = {
    ...envelope.LocalPackages,
    RowPackDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    localPackagePackDigest: undefined,
  };

  const out = await CheckMaterializedLocalPackages0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedLocalPackages0');
  assert.equal(out.Coord, 'CheckMaterializedLocalPackages0.linkage');
  assert.deepEqual(out.Path, ['LocalPackages', 'RowPackDigest']);
});

test('CheckMaterializedLocalPackages0 rejects stale linkage digest', async () => {
  const envelope = makeMaterializedLocalPackages0();

  envelope.Linkage = {
    ...envelope.Linkage,
    localPackagePackDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckMaterializedLocalPackages0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedLocalPackages0');
  assert.equal(out.Coord, 'CheckMaterializedLocalPackages0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'localPackagePackDigest']);
});

test('writeMaterializedLocalPackagesFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-local-packages-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeMaterializedLocalPackagesFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.rowPackPath,
    result.files.localPackagesPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

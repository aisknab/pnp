import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedLocalPackages0,
  makeConcreteMaterializedLocalPackages0,
  writeConcreteMaterializedLocalPackagesFiles0,
} from '../pcc-local-packages-concrete-materialized0.mjs';

import {
  CheckLocalPackages0,
  LOCAL_PACKAGE_REQUIRED_FAMILIES0,
} from '../pcc-local-packages0.mjs';

test('CheckConcreteMaterializedLocalPackages0 accepts local packages over concrete rows', async () => {
  const envelope = await makeConcreteMaterializedLocalPackages0();
  const out = await CheckConcreteMaterializedLocalPackages0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedLocalPackages0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedLocalPackages0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteRowsEnvelopeKind, 'ConcreteMaterializedRows0');
  assert.equal(out.NF.familyCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
  assert.equal(out.NF.packageCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner CheckLocalPackages0 accepts the concrete local package core', async () => {
  const envelope = await makeConcreteMaterializedLocalPackages0();
  const out = await CheckLocalPackages0(envelope.LocalPackages);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.NF.kind, 'LocalPackages0NF');
  assert.equal(out.NF.familyCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
  assert.deepEqual(envelope.LocalPackages.RowPackDigest, envelope.Linkage.rowPackDigest);
});

test('CheckConcreteMaterializedLocalPackages0 rejects stale declared RowPackDigest', async () => {
  const envelope = await makeConcreteMaterializedLocalPackages0();

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

  const out = await CheckConcreteMaterializedLocalPackages0(envelope, {
    checkMaterializedLocalPackages: false,
    checkLocalPackages: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedLocalPackages0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedLocalPackages0.linkage');
  assert.deepEqual(out.Path, ['LocalPackages', 'RowPackDigest']);
});

test('CheckConcreteMaterializedLocalPackages0 exposes concrete row failures', async () => {
  const envelope = await makeConcreteMaterializedLocalPackages0();

  envelope.ConcreteRowsEnvelope = {
    ...envelope.ConcreteRowsEnvelope,
    RowPack: {
      ...envelope.ConcreteRowsEnvelope.RowPack,
      Rows: envelope.ConcreteRowsEnvelope.RowPack.Rows.map((row, index) => index === 0
        ? {
            ...row,
            IfaceHash: 'IfaceDict0.synthetic',
          }
        : row),
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteRowsDigest: undefined,
  };

  const out = await CheckConcreteMaterializedLocalPackages0(envelope, {
    checkMaterializedLocalPackages: false,
    checkLocalPackages: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedLocalPackages0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedLocalPackages0.ConcreteRows');
  assert.equal(out.Witness.detail.inner.coord, 'CheckConcreteMaterializedRows0.concreteIfaceHash');
});

test('CheckConcreteMaterializedLocalPackages0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeConcreteMaterializedLocalPackages0();

  envelope.LocalPackages = {
    ...envelope.LocalPackages,
    PiLocalPackages: {
      ...envelope.LocalPackages.PiLocalPackages,
      note: 'synthetic marker must reject in strict marker mode',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    localPackagePackDigest: undefined,
  };

  const out = await CheckConcreteMaterializedLocalPackages0(envelope, {
    allowSyntheticScaffoldMarker: false,
    checkMaterializedLocalPackages: false,
    checkLocalPackages: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedLocalPackages0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedLocalPackages0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteMaterializedLocalPackagesFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-local-packages-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedLocalPackagesFiles0(dir);

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

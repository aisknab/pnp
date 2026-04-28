import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckLocalPackageFamily0,
  CheckLocalPackages0,
  LOCAL_PACKAGE_REQUIRED_FAMILIES0,
  makeSyntheticLocalPackages0,
} from '../pcc-local-packages0.mjs';

test('CheckLocalPackages0 accepts the synthetic local package pack', async () => {
  const out = await CheckLocalPackages0(makeSyntheticLocalPackages0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.NF.kind, 'LocalPackages0NF');
  assert.equal(out.NF.familyCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
  assert.equal(out.NF.packageCount, LOCAL_PACKAGE_REQUIRED_FAMILIES0.length);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckLocalPackageFamily0 accepts a single local family package', async () => {
  const pack = makeSyntheticLocalPackages0();
  const pkg = pack.Packages.find((entry) => entry.family === 'E');

  const out = await CheckLocalPackageFamily0(pkg);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckLocalPackageFamily0');
  assert.equal(out.NF.family, 'E');
  assert.equal(out.NF.theorem, 'E.VerifyDWSoundness');
});

test('CheckLocalPackages0 rejects a missing required local package family', async () => {
  const pack = makeSyntheticLocalPackages0();

  pack.Packages = pack.Packages.filter((entry) => entry.family !== 'PkgC');

  const out = await CheckLocalPackages0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.Coord, 'CheckLocalPackages0.coverage');
  assert.deepEqual(out.Path, ['Packages', 'coverage', 'PkgC']);
  assert.equal(out.Witness.reason, 'LocalPackagePack0 is missing a required local package family');
});

test('CheckLocalPackages0 rejects forbidden BC to UN import', async () => {
  const pack = makeSyntheticLocalPackages0();
  const index = pack.Packages.findIndex((entry) => entry.family === 'BC');

  pack.Packages[index] = {
    ...pack.Packages[index],
    imports: [
      'UN',
    ],
  };

  const out = await CheckLocalPackages0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.Coord, 'CheckLocalPackages0.imports');
  assert.deepEqual(out.Path, ['Packages', 'BC', 'imports', 0]);
  assert.equal(out.Witness.reason, 'local package import uses a forbidden package edge');
});

test('CheckLocalPackages0 rejects forbidden G to O import', async () => {
  const pack = makeSyntheticLocalPackages0();
  const index = pack.Packages.findIndex((entry) => entry.family === 'G');

  pack.Packages[index] = {
    ...pack.Packages[index],
    imports: [
      'O',
    ],
  };

  const out = await CheckLocalPackages0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.Coord, 'CheckLocalPackages0.imports');
  assert.deepEqual(out.Path, ['Packages', 'G', 'imports', 0]);
  assert.equal(out.Witness.reason, 'local package import uses a forbidden package edge');
});

test('CheckLocalPackages0 rejects constructive gain routes without VerifyDW acceptance', async () => {
  const pack = makeSyntheticLocalPackages0();
  const index = pack.Packages.findIndex((entry) => entry.family === 'R');

  pack.Packages[index] = {
    ...pack.Packages[index],
    routes: {
      ...pack.Packages[index].routes,
      entries: [
        {
          kind: 'Gain',
          verifyDWAccepted: false,
        },
      ],
    },
  };

  const out = await CheckLocalPackages0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.Coord, 'CheckLocalPackages0.packages');
  assert.deepEqual(out.Path, ['Packages', 'R']);
  assert.equal(out.Witness.reason, 'local package checker rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckLocalPackageFamily0.routes');
  assert.deepEqual(out.Witness.detail.inner.path, ['routes', 'entries', 0, 'verifyDWAccepted']);
});

test('CheckLocalPackages0 rejects exact routes without accepted exact certificates', async () => {
  const pack = makeSyntheticLocalPackages0();
  const index = pack.Packages.findIndex((entry) => entry.family === 'O');

  pack.Packages[index] = {
    ...pack.Packages[index],
    routes: {
      ...pack.Packages[index].routes,
      entries: [
        {
          kind: 'ExactRoute',
          exactCertificateAccepted: false,
        },
      ],
    },
  };

  const out = await CheckLocalPackages0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.Coord, 'CheckLocalPackages0.packages');
  assert.equal(out.Witness.detail.inner.coord, 'CheckLocalPackageFamily0.routes');
  assert.deepEqual(out.Witness.detail.inner.path, ['routes', 'entries', 0, 'exactCertificateAccepted']);
});

test('CheckLocalPackages0 rejects non-polynomial local package bounds', async () => {
  const pack = makeSyntheticLocalPackages0();
  const index = pack.Packages.findIndex((entry) => entry.family === 'BN6');

  pack.Packages[index] = {
    ...pack.Packages[index],
    bounds: {
      ...pack.Packages[index].bounds,
      polynomial: false,
    },
  };

  const out = await CheckLocalPackages0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.Coord, 'CheckLocalPackages0.packages');
  assert.equal(out.Witness.detail.inner.coord, 'CheckLocalPackageFamily0.bounds');
  assert.deepEqual(out.Witness.detail.inner.path, ['bounds', 'polynomial']);
  assert.equal(out.Witness.detail.inner.witness.reason, 'LocalPackage0 bounds must be polynomial');
});

test('CheckLocalPackages0 rejects executable hidden minimization inside a local package', async () => {
  const pack = makeSyntheticLocalPackages0();
  const index = pack.Packages.findIndex((entry) => entry.family === 'Final');

  pack.Packages[index] = {
    ...pack.Packages[index],
    payload: {
      ...pack.Packages[index].payload,
      body: [
        'minimumEquivalent',
      ],
    },
  };

  const out = await CheckLocalPackages0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.Coord, 'CheckLocalPackages0.noHiddenMin');
  assert.deepEqual(out.Path, ['LocalPackagePack0', 'Packages', index, 'payload', 'body', 0]);
  assert.equal(out.Witness.reason, 'forbidden minimization symbol appears in executable position');
});

test('CheckLocalPackages0 rejects opaque proof blobs', async () => {
  const pack = makeSyntheticLocalPackages0();

  pack.PiLocalPackages = {
    ...pack.PiLocalPackages,
    proofBlob: {
      bytes: 'not allowed',
    },
  };

  const out = await CheckLocalPackages0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.Coord, 'CheckLocalPackages0.opaqueProof');
  assert.deepEqual(out.Path, ['LocalPackagePack0', 'PiLocalPackages', 'proofBlob']);
  assert.equal(out.Witness.reason, 'opaque proof material is not allowed in local packages');
});

test('CheckLocalPackages0 rejects a missing global package theorem reflection', async () => {
  const pack = makeSyntheticLocalPackages0();
  const index = pack.Packages.findIndex((entry) => entry.family === 'G');

  pack.Packages[index] = {
    ...pack.Packages[index],
    theorem: 'G.SomeOtherTheorem',
  };

  const out = await CheckLocalPackages0(pack);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckLocalPackages0');
  assert.equal(out.Coord, 'CheckLocalPackages0.packages');
  assert.equal(out.Witness.detail.inner.coord, 'CheckLocalPackageFamily0.identity');
  assert.deepEqual(out.Witness.detail.inner.path, ['theorem']);
});
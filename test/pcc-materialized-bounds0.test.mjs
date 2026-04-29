import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedBounds0,
  CheckMaterializedBoundsFile0,
  MATERIALIZED_BOUNDS_POLICY0,
  makeMaterializedBoundsShell0,
} from '../pcc-materialized-bounds0.mjs';

import {
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedBounds0 accepts finite polynomial public-schedule bounds', async () => {
  const out = await CheckMaterializedBounds0(makeMaterializedBoundsShell0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedBounds0');
  assert.equal(out.NF.kind, 'MaterializedBounds0NF');
  assert.equal(out.NF.globalExponent, MATERIALIZED_BOUNDS_POLICY0.globalExponent);
  assert.equal(out.NF.artefactCount > 0, true);
  assert.equal(out.PackObject.GPack.bounds.polynomial, true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedBoundsFile0 accepts a bounds shell file', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedBoundsShell0());

  const out = await CheckMaterializedBoundsFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedBoundsFile0');
  assert.equal(out.NF.kind, 'MaterializedBoundsFile0NF');
  assert.equal(out.NF.globalExponent, MATERIALIZED_BOUNDS_POLICY0.globalExponent);
});

test('CheckMaterializedBounds0 rejects missing bounds policy', async () => {
  const shell = makeMaterializedBoundsShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.Manifest.boundsPolicy;

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedBounds0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedBounds0');
  assert.equal(out.Coord, 'CheckMaterializedBounds0.boundsPolicy');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'boundsPolicy']);
  assert.equal(out.Witness.reason, 'Pack.Manifest boundsPolicy must be an object');
});

test('CheckMaterializedBounds0 rejects private schedule enlargement', async () => {
  const shell = makeMaterializedBoundsShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactBounds.GPack = {
    ...pack.Manifest.artefactBounds.GPack,
    noPrivateSchedule: false,
  };

  pack.GPack = {
    ...pack.GPack,
    bounds: pack.Manifest.artefactBounds.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedBounds0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedBounds0');
  assert.equal(out.Coord, 'CheckMaterializedBounds0.manifestArtefactBounds');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactBounds', 'GPack', 'noPrivateSchedule']);
  assert.equal(out.Witness.reason, 'materialized bounds must certify noPrivateSchedule');
});

test('CheckMaterializedBounds0 rejects non-polynomial artefact bounds', async () => {
  const shell = makeMaterializedBoundsShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactBounds.GPack = {
    ...pack.Manifest.artefactBounds.GPack,
    polynomial: false,
  };

  pack.GPack = {
    ...pack.GPack,
    bounds: pack.Manifest.artefactBounds.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedBounds0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedBounds0');
  assert.equal(out.Coord, 'CheckMaterializedBounds0.manifestArtefactBounds');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactBounds', 'GPack', 'polynomial']);
  assert.equal(out.Witness.reason, 'materialized bounds must certify polynomial');
});

test('CheckMaterializedBounds0 rejects non-positive exponent', async () => {
  const shell = makeMaterializedBoundsShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactBounds.GPack = {
    ...pack.Manifest.artefactBounds.GPack,
    exponent: 0,
  };

  pack.GPack = {
    ...pack.GPack,
    bounds: pack.Manifest.artefactBounds.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedBounds0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedBounds0');
  assert.equal(out.Coord, 'CheckMaterializedBounds0.manifestArtefactBounds');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactBounds', 'GPack', 'exponent']);
  assert.equal(out.Witness.reason, 'materialized bounds exponent must be a positive integer');
});

test('CheckMaterializedBounds0 rejects exponent above global policy', async () => {
  const shell = makeMaterializedBoundsShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactBounds.GPack = {
    ...pack.Manifest.artefactBounds.GPack,
    exponent: pack.Manifest.boundsPolicy.globalExponent + 1,
  };

  pack.GPack = {
    ...pack.GPack,
    bounds: pack.Manifest.artefactBounds.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedBounds0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedBounds0');
  assert.equal(out.Coord, 'CheckMaterializedBounds0.manifestArtefactBounds');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactBounds', 'GPack', 'exponent']);
  assert.equal(out.Witness.reason, 'materialized bounds exponent must not exceed globalExponent');
});

test('CheckMaterializedBounds0 rejects artefact bounds mismatch with manifest', async () => {
  const shell = makeMaterializedBoundsShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack = {
    ...pack.GPack,
    bounds: {
      ...pack.GPack.bounds,
      exponent: pack.GPack.bounds.exponent + 1,
    },
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedBounds0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedBounds0');
  assert.equal(out.Coord, 'CheckMaterializedBounds0.artefactBounds');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'bounds']);
  assert.equal(out.Witness.reason, 'materialized artefact bounds must match Pack.Manifest artefactBounds');
});

test('CheckMaterializedBounds0 rejects dependencyBoundRefs mismatch with artefact dependencies', async () => {
  const shell = makeMaterializedBoundsShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactBounds.GPack = {
    ...pack.Manifest.artefactBounds.GPack,
    dependencyBoundRefs: [],
  };

  pack.GPack = {
    ...pack.GPack,
    bounds: pack.Manifest.artefactBounds.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedBounds0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedBounds0');
  assert.equal(out.Coord, 'CheckMaterializedBounds0.dependencyBoundRefs');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactBounds', 'GPack', 'dependencyBoundRefs']);
  assert.equal(out.Witness.reason, 'bounds dependencyBoundRefs must match artefactDependencies');
});

test('CheckMaterializedBounds0 rejects bounds digest mismatch', async () => {
  const shell = makeMaterializedBoundsShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.artefactBounds.GPack = {
    ...pack.Manifest.artefactBounds.GPack,
    digest: {
      alg: 'SHA256',
      bytes: 'utf8',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  pack.GPack = {
    ...pack.GPack,
    bounds: pack.Manifest.artefactBounds.GPack,
  };

  resealShellPack0(shell, pack);

  const out = await CheckMaterializedBounds0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedBounds0');
  assert.equal(out.Coord, 'CheckMaterializedBounds0.boundsDigests');
  assert.deepEqual(out.Path, ['PackBytes', 'Manifest', 'artefactBounds', 'GPack', 'digest']);
  assert.equal(out.Witness.reason, 'manifest artefact bounds digest mismatch');
});

async function writeTempShellFile0(t, shell) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-bounds-'));
  const filePath = path.join(dir, 'MaterializedPCCPack0.json');

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  await fs.writeFile(filePath, JSON.stringify(shell, null, 2), 'utf8');

  return filePath;
}

function resealShellPack0(shell, pack) {
  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);
}
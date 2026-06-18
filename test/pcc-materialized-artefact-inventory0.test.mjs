import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  PCCPACK_REQUIRED_FIELDS0,
} from '../pcc-pack-sufficiency0.mjs';

import {
  CheckMaterializedArtefactInventory0,
  CheckMaterializedArtefactInventoryFile0,
  makeMaterializedArtefactInventoryShell0,
} from '../pcc-materialized-artefact-inventory0.mjs';

import {
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedArtefactInventory0 accepts a shell containing every required artefact', async () => {
  const out = await CheckMaterializedArtefactInventory0(makeMaterializedArtefactInventoryShell0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedArtefactInventory0');
  assert.equal(out.NF.kind, 'MaterializedArtefactInventory0NF');
  assert.equal(out.NF.artefactCount, PCCPACK_REQUIRED_FIELDS0.length);
  assert.deepEqual(out.NF.artefacts, PCCPACK_REQUIRED_FIELDS0);
  assert.equal(out.PackObject.GPack.artefactName, 'GPack');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedArtefactInventoryFile0 accepts an artefact inventory shell file', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedArtefactInventoryShell0());

  const out = await CheckMaterializedArtefactInventoryFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedArtefactInventoryFile0');
  assert.equal(out.NF.kind, 'MaterializedArtefactInventoryFile0NF');
  assert.equal(out.NF.artefactCount, PCCPACK_REQUIRED_FIELDS0.length);
});

test('CheckMaterializedArtefactInventory0 rejects a missing required artefact object', async () => {
  const shell = makeMaterializedArtefactInventoryShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.GPack;

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedArtefactInventory0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactInventory0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactInventory0.artefactInventory');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack']);
  assert.equal(out.Witness.reason, 'PackBytes is missing a required top-level artefact');
});

test('CheckMaterializedArtefactInventory0 rejects a non-object required artefact', async () => {
  const shell = makeMaterializedArtefactInventoryShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack = 'not an object';

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedArtefactInventory0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactInventory0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactInventory0.artefactInventory');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack']);
  assert.equal(out.Witness.reason, 'required top-level artefact must be an object');
});

test('CheckMaterializedArtefactInventory0 rejects an artefact missing a seal field', async () => {
  const shell = makeMaterializedArtefactInventoryShell0();
  const pack = JSON.parse(shell.PackBytes);

  delete pack.GPack.digest;

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedArtefactInventory0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactInventory0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactInventory0.artefactSeals');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'digest']);
  assert.equal(out.Witness.reason, 'materialized artefact object is missing a required seal field');
});

test('CheckMaterializedArtefactInventory0 rejects an artefact name mismatch', async () => {
  const shell = makeMaterializedArtefactInventoryShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack = {
    ...pack.GPack,
    artefactName: 'WrongName',
  };

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedArtefactInventory0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactInventory0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactInventory0.artefactSeals');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'artefactName']);
  assert.equal(out.Witness.reason, 'materialized artefact name mismatch');
});

test('CheckMaterializedArtefactInventory0 rejects a non-concrete artefact digest', async () => {
  const shell = makeMaterializedArtefactInventoryShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.GPack = {
    ...pack.GPack,
    digest: {
      alg: 'SHA256',
      hex: 'not-a-sha',
    },
  };

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedArtefactInventory0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactInventory0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactInventory0.artefactSeals');
  assert.deepEqual(out.Path, ['PackBytes', 'GPack', 'digest']);
  assert.equal(out.Witness.reason, 'materialized artefact digest must be a concrete SHA256 digest record');
});

test('CheckMaterializedArtefactInventory0 rejects AcceptRun as a top-level pack artefact', async () => {
  const shell = makeMaterializedArtefactInventoryShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.AcceptRun = {
    kind: 'AcceptRun0',
  };

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await CheckMaterializedArtefactInventory0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedArtefactInventory0');
  assert.equal(out.Coord, 'CheckMaterializedArtefactInventory0.packBoundary');
  assert.deepEqual(out.Path, ['PackBytes', 'AcceptRun']);
  assert.equal(out.Witness.reason, 'PackBytes must not contain AcceptRun as a package artefact');
});

async function writeTempShellFile0(t, shell) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-artefact-inventory-'));
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
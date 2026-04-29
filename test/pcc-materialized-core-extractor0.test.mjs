import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  ExtractMaterializedCore0,
  ExtractMaterializedCoreFile0,
} from '../pcc-materialized-core-extractor0.mjs';

import {
  makeMaterializedPCCPackShell0,
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('ExtractMaterializedCore0 accepts a materialized shell and extracts CoreObject and PackObject', async () => {
  const shell = makeMaterializedPCCPackShell0();
  const out = await ExtractMaterializedCore0(shell);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'ExtractMaterializedCore0');
  assert.equal(out.NF.kind, 'MaterializedCoreExtraction0NF');
  assert.equal(out.NF.packCoreMatchesCoreBytes, true);
  assert.equal(out.CoreObject.kind, 'PCCCorePackage0');
  assert.equal(out.PackObject.kind, 'PCCPack0');
  assert.deepEqual(out.PackObject.Core, out.CoreObject);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('ExtractMaterializedCoreFile0 extracts core and pack objects from a shell file', async (t) => {
  const shell = makeMaterializedPCCPackShell0();
  const filePath = await writeTempShellFile0(t, shell);

  const out = await ExtractMaterializedCoreFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'ExtractMaterializedCoreFile0');
  assert.equal(out.NF.kind, 'MaterializedCoreFileExtraction0NF');
  assert.equal(out.CoreObject.kind, 'PCCCorePackage0');
  assert.equal(out.PackObject.Core.kind, 'PCCCorePackage0');
});

test('ExtractMaterializedCore0 rejects Pack.Core divergence from CoreBytes', async () => {
  const shell = makeMaterializedPCCPackShell0();
  const packObject = JSON.parse(shell.PackBytes);

  packObject.Core = {
    ...packObject.Core,
    packageId: 'DifferentConcreteCore0',
  };

  shell.PackBytes = stableStringify0(packObject);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await ExtractMaterializedCore0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'ExtractMaterializedCore0');
  assert.equal(out.Coord, 'ExtractMaterializedCore0.packCoreLink');
  assert.deepEqual(out.Path, ['PackBytes', 'Core']);
  assert.equal(out.Witness.reason, 'Pack.Core canonical bytes must exactly match CoreBytes');
});

test('ExtractMaterializedCore0 rejects missing Pack.Core', async () => {
  const shell = makeMaterializedPCCPackShell0();
  const packObject = JSON.parse(shell.PackBytes);

  delete packObject.Core;

  shell.PackBytes = stableStringify0(packObject);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await ExtractMaterializedCore0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'ExtractMaterializedCore0');
  assert.equal(out.Coord, 'ExtractMaterializedCore0.packCoreLink');
  assert.deepEqual(out.Path, ['PackBytes', 'Core']);
  assert.equal(out.Witness.reason, 'PackBytes object must contain a Core field');
});

test('ExtractMaterializedCore0 rejects CoreDigest mismatch through shell validation', async () => {
  const shell = makeMaterializedPCCPackShell0();

  shell.CoreDigest = {
    ...shell.CoreDigest,
    hex: '0000000000000000000000000000000000000000000000000000000000000000',
  };

  const out = await ExtractMaterializedCore0(shell);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'ExtractMaterializedCore0');
  assert.equal(out.Coord, 'ExtractMaterializedCore0.shell');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.reason, 'CheckMaterializedPCCPackShell0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedPCCPackShell0.canonicalBytes');
});

test('ExtractMaterializedCore0 can skip shell validation and still reject displayed digest mismatch', async () => {
  const shell = makeMaterializedPCCPackShell0();

  shell.CoreDigest = {
    ...shell.CoreDigest,
    hex: '1111111111111111111111111111111111111111111111111111111111111111',
  };

  const out = await ExtractMaterializedCore0(shell, {
    checkShell: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'ExtractMaterializedCore0');
  assert.equal(out.Coord, 'ExtractMaterializedCore0.displayedDigests');
  assert.deepEqual(out.Path, ['CoreDigest']);
  assert.equal(out.Witness.reason, 'CoreDigest must be SHA256 over CoreBytes');
});

test('ExtractMaterializedCore0 rejects non-canonical CoreBytes when shell validation is skipped', async () => {
  const shell = makeMaterializedPCCPackShell0();

  shell.CoreBytes = JSON.stringify({
    z: 1,
    a: 2,
  });

  shell.CoreDigest = sha256Utf8DigestRecord0(shell.CoreBytes);

  const out = await ExtractMaterializedCore0(shell, {
    checkShell: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'ExtractMaterializedCore0');
  assert.equal(out.Coord, 'ExtractMaterializedCore0.coreBytes');
  assert.deepEqual(out.Path, ['CoreBytes']);
  assert.equal(out.Witness.reason, 'CoreBytes must be canonical JSON bytes');
});

test('ExtractMaterializedCore0 rejects core boundary when CoreObject includes AcceptRun', async () => {
  const shell = makeMaterializedPCCPackShell0();

  const badCore = {
    kind: 'PCCCorePackage0',
    version: 0,
    packageId: 'ConcreteBadCore0',
    excludesAcceptRun: true,
    includesAcceptRun: false,
    canonicalByteEquality: true,
    materializedOutputOnly: true,
    noDigestOnlyEquality: true,
    AcceptRun: {
      kind: 'AcceptRun0',
    },
  };

  const badPack = JSON.parse(shell.PackBytes);

  badPack.Core = badCore;

  shell.CoreBytes = stableStringify0(badCore);
  shell.CoreDigest = sha256Utf8DigestRecord0(shell.CoreBytes);
  shell.PackBytes = stableStringify0(badPack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const out = await ExtractMaterializedCore0(shell, {
    checkShell: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'ExtractMaterializedCore0');
  assert.equal(out.Coord, 'ExtractMaterializedCore0.coreBoundary');
  assert.deepEqual(out.Path, ['CoreObject']);
  assert.equal(out.Witness.reason, 'materialized core object must not contain AcceptRun');
});

test('ExtractMaterializedCore0 validates extractor config shape', async () => {
  const out = await ExtractMaterializedCore0(makeMaterializedPCCPackShell0(), {
    checkShell: 'yes',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'ExtractMaterializedCore0');
  assert.equal(out.Coord, 'ExtractMaterializedCore0.config');
  assert.deepEqual(out.Path, ['checkShell']);
  assert.equal(out.Witness.reason, 'MaterializedCoreExtractorConfig0 checkShell must be boolean');
});

async function writeTempShellFile0(t, shell) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-core-extractor-'));
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
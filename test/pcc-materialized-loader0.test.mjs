import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CheckMaterializedPCCPackShellFile0,
  LoadMaterializedPCCPackShellFile0,
} from '../pcc-materialized-loader0.mjs';

import {
  makeMaterializedPCCPackShell0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('LoadMaterializedPCCPackShellFile0 loads a JSON MaterializedPCCPack0 shell from disk', async (t) => {
  const { filePath } = await writeTempShell0(t);

  const out = await LoadMaterializedPCCPackShellFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'LoadMaterializedPCCPackShellFile0');
  assert.equal(out.Shell.kind, 'MaterializedPCCPack0');
  assert.match(out.NF.fileDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.shellDigest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedPCCPackShellFile0 accepts a JSON shell from disk', async (t) => {
  const { filePath } = await writeTempShell0(t);

  const out = await CheckMaterializedPCCPackShellFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShellFile0');
  assert.equal(out.NF.kind, 'CheckedMaterializedPCCPackShellFile0NF');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedPCCPackShellFile0 accepts canonical envelope bytes when requested', async (t) => {
  const shell = makeMaterializedPCCPackShell0();
  const { filePath } = await writeTempText0(t, stableStringify0(shell));

  const out = await CheckMaterializedPCCPackShellFile0(filePath, {
    requireCanonicalEnvelopeBytes: true,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShellFile0');
});

test('CheckMaterializedPCCPackShellFile0 rejects non-canonical envelope bytes when required', async (t) => {
  const shell = makeMaterializedPCCPackShell0();
  const { filePath } = await writeTempText0(t, JSON.stringify(shell, null, 2));

  const out = await CheckMaterializedPCCPackShellFile0(filePath, {
    requireCanonicalEnvelopeBytes: true,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShellFile0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShellFile0.load');
  assert.equal(out.Witness.detail.inner.coord, 'LoadMaterializedPCCPackShellFile0.canonicalEnvelopeBytes');
});

test('CheckMaterializedPCCPackShellFile0 rejects invalid JSON', async (t) => {
  const { filePath } = await writeTempText0(t, '{ this is not json');

  const out = await CheckMaterializedPCCPackShellFile0(filePath);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShellFile0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShellFile0.load');
  assert.equal(out.Witness.detail.inner.coord, 'LoadMaterializedPCCPackShellFile0.parse');
});

test('CheckMaterializedPCCPackShellFile0 rejects a shell with synthetic marker text', async (t) => {
  const shell = makeMaterializedPCCPackShell0();

  shell.Manifest = {
    ...shell.Manifest,
    label: 'sched.synthetic',
  };

  const { filePath } = await writeTempShell0(t, shell);
  const out = await CheckMaterializedPCCPackShellFile0(filePath);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShellFile0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShellFile0.shell');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedPCCPackShell0.materialized');
});

test('CheckMaterializedPCCPackShellFile0 rejects a missing file', async () => {
  const out = await CheckMaterializedPCCPackShellFile0(path.join(os.tmpdir(), 'pnp-missing-materialized-shell.json'));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShellFile0');
  assert.equal(out.Coord, 'CheckMaterializedPCCPackShellFile0.load');
  assert.equal(out.Witness.detail.inner.coord, 'LoadMaterializedPCCPackShellFile0.read');
});

test('bin/check-materialized-shell0.mjs emits an accepted shell summary', async (t) => {
  const { filePath } = await writeTempShell0(t);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-shell0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShellFile0');
  assert.match(out.fileDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/check-materialized-shell0.mjs --full emits the complete accept record', async (t) => {
  const { filePath } = await writeTempShell0(t);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-shell0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShellFile0');
  assert.equal(out.NF.kind, 'CheckedMaterializedPCCPackShellFile0NF');
  assert.equal(Array.isArray(out.Ledger), true);
});

test('bin/check-materialized-shell0.mjs exits nonzero without a path', () => {
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-shell0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.coord, 'check-materialized-shell0.args');
});

async function writeTempShell0(t, shell = makeMaterializedPCCPackShell0()) {
  return writeTempText0(t, JSON.stringify(shell, null, 2));
}

async function writeTempText0(t, text) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-shell-loader-'));
  const filePath = path.join(dir, 'MaterializedPCCPack0.json');

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  await fs.writeFile(filePath, text, 'utf8');

  return {
    dir,
    filePath,
  };
}
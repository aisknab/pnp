import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  MATERIALIZED_AGGREGATE_PHASES0,
  makeMaterializedAggregateShell0,
} from '../pcc-materialized-aggregate0.mjs';

import {
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('bin/check-materialized-aggregate0.mjs emits an accepted aggregate summary', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedAggregateShell0());
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-aggregate0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAggregateFile0');
  assert.equal(out.phaseCount, MATERIALIZED_AGGREGATE_PHASES0.length);
  assert.match(out.fileDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/check-materialized-aggregate0.mjs --full emits the complete aggregate accept record', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedAggregateShell0());
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-aggregate0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAggregateFile0');
  assert.equal(out.NF.kind, 'MaterializedAggregateFile0NF');
  assert.equal(out.NF.phaseCount, MATERIALIZED_AGGREGATE_PHASES0.length);
  assert.equal(Array.isArray(out.Ledger), true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/check-materialized-aggregate0.mjs accepts canonical envelope bytes when requested', async (t) => {
  const filePath = await writeTempTextFile0(t, stableStringify0(makeMaterializedAggregateShell0()));
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-aggregate0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath, '--canonical-envelope-bytes'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAggregateFile0');
  assert.equal(out.phaseCount, MATERIALIZED_AGGREGATE_PHASES0.length);
});

test('bin/check-materialized-aggregate0.mjs rejects non-canonical envelope bytes when requested', async (t) => {
  const filePath = await writeTempShellFile0(t, makeMaterializedAggregateShell0());
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-aggregate0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath, '--canonical-envelope-bytes'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregateFile0');
  assert.equal(out.coord, 'CheckMaterializedAggregateFile0.load');
  assert.equal(out.witness.detail.inner.coord, 'LoadMaterializedPCCPackShellFile0.canonicalEnvelopeBytes');
});

test('bin/check-materialized-aggregate0.mjs rejects a tampered aggregate shell', async (t) => {
  const shell = makeMaterializedAggregateShell0();
  const pack = JSON.parse(shell.PackBytes);

  pack.Manifest.packageImportEdges = [
    {
      from: 'O',
      to: 'G',
    },
  ];

  shell.PackBytes = stableStringify0(pack);
  shell.PackDigest = sha256Utf8DigestRecord0(shell.PackBytes);

  const filePath = await writeTempShellFile0(t, shell);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-aggregate0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAggregateFile0');
  assert.equal(out.coord, 'CheckMaterializedAggregateFile0.aggregate');
  assert.equal(out.witness.detail.inner.coord, 'CheckMaterializedAggregate0.CheckMaterializedImports0');
});

test('bin/check-materialized-aggregate0.mjs exits nonzero without a file path', () => {
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-aggregate0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'check-materialized-aggregate0');
  assert.equal(out.coord, 'check-materialized-aggregate0.args');
});

async function writeTempShellFile0(t, shell) {
  return writeTempTextFile0(t, JSON.stringify(shell, null, 2));
}

async function writeTempTextFile0(t, text) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-aggregate-cli-'));
  const filePath = path.join(dir, 'MaterializedPCCPack0.json');

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  await fs.writeFile(filePath, text, 'utf8');

  return filePath;
}
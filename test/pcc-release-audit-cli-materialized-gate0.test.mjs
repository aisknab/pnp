import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

test('release audit CLI --no-materialized-gate explicitly skips the materialized public status gate', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--no-materialized-gate'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.materializedPublicStatusGate, false);
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('release audit CLI --materialized-gate executes the materialized public status gate', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
    '--materialized-gate',
    '--materialized-gate-out',
    outputDir,
    '--no-materialized-gate-cli',
  ], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');
  assert.equal(out.materializedPublicStatusGate, true);

  const packStat = await fs.stat(path.join(outputDir, 'MaterializedPCCPack0.json'));

  assert.equal(packStat.isFile(), true);
});

test('release audit CLI --full exposes the materialized gate ledger phase', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--no-materialized-gate', '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);
  const gateLedger = out.Ledger.find((entry) => entry.phase === 'materializedPublicStatusGate');

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.materializedPublicStatusGate, false);
  assert.equal(gateLedger.status, 'pass');
});

test('release audit CLI rejects contradictory materialized gate flags', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
    '--materialized-gate',
    '--no-materialized-gate',
  ], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'release-audit0');
  assert.equal(out.coord, 'release-audit0.args');
  assert.equal(out.witness.reason, 'release audit CLI cannot use both --materialized-gate and --no-materialized-gate');
});

test('release audit CLI rejects contradictory materialized gate CLI flags', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
    '--materialized-gate-cli',
    '--no-materialized-gate-cli',
  ], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'release-audit0');
  assert.equal(out.coord, 'release-audit0.args');
  assert.equal(out.witness.reason, 'release audit CLI cannot use both --materialized-gate-cli and --no-materialized-gate-cli');
});

test('release audit CLI rejects missing materialized gate output directory argument', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--materialized-gate-out'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'release-audit0');
  assert.equal(out.coord, 'release-audit0.args');
  assert.deepEqual(out.path, ['argv', '--materialized-gate-out']);
  assert.equal(out.witness.reason, '--materialized-gate-out requires a directory argument');
});

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-release-audit-cli-materialized-gate-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
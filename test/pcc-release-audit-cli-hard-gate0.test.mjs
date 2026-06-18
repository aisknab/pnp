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

test('release audit CLI default hard gate executes public surface freeze and materialized gate', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
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

  assert.equal(out.publicSurfaceFreeze, true);
  assert.equal(out.publicSurfaceFreezeSurfaceFrozen, true);
  assert.equal(out.publicSurfaceFreezeSummary.skipped, false);

  assert.equal(out.materializedPublicStatusGate, true);
  assert.equal(out.materializedPublicStatusGateSummary.skipped, false);
  assert.equal(out.materializedPublicStatusGateAcceptedPublicConclusionOnly, true);
  assert.equal(out.materializedPublicStatusGateFileCount, 4);
  assert.equal(out.materializedPublicStatusGateDirectRecordCount, 4);
  assert.equal(out.materializedPublicStatusGateCliRecordCount, 0);

  const packStat = await fs.stat(path.join(outputDir, 'MaterializedPCCPack0.json'));

  assert.equal(packStat.isFile(), true);
});

test('release audit CLI --fast-local keeps public surface freeze and skips materialized gate', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
    '--fast-local',
  ], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAudit0');

  assert.equal(out.publicSurfaceFreeze, true);
  assert.equal(out.publicSurfaceFreezeSurfaceFrozen, true);
  assert.equal(out.publicSurfaceFreezeSummary.skipped, false);

  assert.equal(out.materializedPublicStatusGate, false);
  assert.equal(out.materializedPublicStatusGateSummary.skipped, true);
  assert.equal(out.materializedPublicStatusGateDigest, null);
  assert.equal(out.materializedPublicStatusGateFileCount, 0);
});

test('release audit CLI --fast-local full mode exposes skipped materialized gate NF', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
    '--fast-local',
    '--full',
  ], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);
  const publicSurfacePhase = out.Ledger.find((entry) => entry.phase === 'publicSurfaceFreeze');
  const materializedGatePhase = out.Ledger.find((entry) => entry.phase === 'materializedPublicStatusGate');

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.publicSurfaceFreeze, true);
  assert.equal(out.NF.materializedPublicStatusGate, false);
  assert.equal(out.NF.materializedPublicStatusGateSummary.skipped, true);
  assert.equal(publicSurfacePhase.status, 'pass');
  assert.equal(materializedGatePhase.status, 'pass');
});

test('release audit CLI rejects --fast-local with --materialized-gate', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
    '--fast-local',
    '--materialized-gate',
  ], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'release-audit0');
  assert.equal(out.coord, 'release-audit0.args');
  assert.deepEqual(out.path, ['argv']);
  assert.equal(out.witness.reason, 'release audit CLI cannot use both --fast-local and --materialized-gate');
});

test('release audit CLI rejects --fast-local with --materialized-gate-out', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
    '--fast-local',
    '--materialized-gate-out',
    outputDir,
  ], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'release-audit0');
  assert.equal(out.coord, 'release-audit0.args');
  assert.deepEqual(out.path, ['argv', '--materialized-gate-out']);
  assert.equal(out.witness.reason, 'release audit CLI cannot use --materialized-gate-out with --fast-local');
});

test('release audit CLI rejects --fast-local with --materialized-gate-canonical', () => {
  const cliPath = fileURLToPath(new URL('../bin/release-audit0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [
    cliPath,
    '--fast-local',
    '--materialized-gate-canonical',
  ], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'release-audit0');
  assert.equal(out.coord, 'release-audit0.args');
  assert.deepEqual(out.path, ['argv']);
  assert.equal(out.witness.reason, 'release audit CLI cannot use --materialized-gate-canonical with --fast-local');
});

test('README documents hard-gate default and no longer advertises src as active structure', async () => {
  const readme = await fs.readFile(new URL('../README.md', import.meta.url), 'utf8');

  assert.equal(readme.includes('Release audit hard-gate default'), true);
  assert.equal(readme.includes('npm run release:audit -- --fast-local'), true);
  assert.equal(readme.includes('Fast local mode keeps the public surface freeze enabled'), true);
  assert.equal(readme.includes('stale duplicate ES modules under `src`'), false);
});

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-release-audit-hard-gate-cli-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
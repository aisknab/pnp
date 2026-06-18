import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

function npmCommand0() {
  return process.platform === 'win32'
    ? 'npm.cmd'
    : 'npm';
}

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

function parseJsonFromStdout0(stdout) {
  const firstBrace = stdout.indexOf('{');

  assert.notEqual(firstBrace, -1, stdout);

  return JSON.parse(stdout.slice(firstBrace));
}

test('README documents the materialized public status release gate', async () => {
  const readme = await fs.readFile(new URL('../README.md', import.meta.url), 'utf8');

  assert.equal(readme.includes('Internal materialized public status release gate'), true);
  assert.equal(readme.includes('npm run materialized:public-status-roundtrip'), true);
  assert.equal(readme.includes('pending  -> no public P = NP conclusion'), true);
  assert.equal(readme.includes('rejected -> no public P = NP conclusion'), true);
  assert.equal(readme.includes('accepted -> emits the conditional public conclusion'), true);
  assert.equal(readme.includes('separate from synthetic `RunAll0`'), true);
  assert.equal(readme.includes('CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP'), true);
});

test('package.json exposes materialized public status release gate scripts', async () => {
  const pkg = JSON.parse(await fs.readFile(new URL('../package.json', import.meta.url), 'utf8'));

  for (const script of [
    'materialized:public-status-roundtrip',
    'materialized:public-status-roundtrip:full',
  ]) {
    assert.equal(typeof pkg.scripts[script], 'string');
    assert.equal(pkg.scripts[script].length > 0, true);
  }
});

test('npm run materialized:public-status-roundtrip emits accepted release-gate summary', async (t) => {
  const outputDir = await makeTempDir0(t);

  const child = spawnSync(npmCommand0(), ['run', 'materialized:public-status-roundtrip', '--', outputDir], {
    encoding: 'utf8',
    shell: process.platform === 'win32',
    windowsHide: true,
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = parseJsonFromStdout0(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPublicStatusRoundtrip0');
  assert.equal(out.fileCount, 4);
  assert.equal(out.deterministic, true);
  assert.equal(out.materializedPath, true);
  assert.equal(out.syntheticRunAll, false);
  assert.equal(out.acceptedPublicConclusionOnly, true);
  assert.equal(out.directRecordCount, 4);
  assert.equal(out.cliRecordCount, 4);
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('npm run materialized:public-status-roundtrip:full emits full accepted release-gate record', async (t) => {
  const outputDir = await makeTempDir0(t);

  const child = spawnSync(npmCommand0(), ['run', 'materialized:public-status-roundtrip:full', '--', outputDir], {
    encoding: 'utf8',
    shell: process.platform === 'win32',
    windowsHide: true,
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = parseJsonFromStdout0(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPublicStatusRoundtrip0');
  assert.equal(out.NF.kind, 'MaterializedPublicStatusRoundtrip0NF');
  assert.equal(out.NF.acceptedPublicConclusionOnly, true);
  assert.equal(Array.isArray(out.Ledger), true);
});

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-public-status-release-gate-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
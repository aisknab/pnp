import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  makeMaterializedAggregateShell0,
} from '../pcc-materialized-aggregate0.mjs';

import {
  makeAcceptedMaterializedAcceptanceBridge0,
  makeMaterializedAcceptanceBridge0,
} from '../pcc-materialized-acceptance-bridge0.mjs';

function npmCommand0() {
  return process.platform === 'win32'
    ? 'npm.cmd'
    : 'npm';
}

function spawnNpmRun0(script, filePath) {
  return spawnSync(npmCommand0(), ['run', script, '--', filePath], {
    encoding: 'utf8',
    shell: process.platform === 'win32',
    windowsHide: true,
  });
}

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

function parseNpmJsonStdout0(stdout) {
  const firstBrace = stdout.indexOf('{');

  assert.notEqual(firstBrace, -1, stdout);

  return JSON.parse(stdout.slice(firstBrace));
}

test('README documents the internal materialized package path', async () => {
  const readme = await fs.readFile(new URL('../README.md', import.meta.url), 'utf8');

  assert.equal(readme.includes('Internal materialized package path'), true);
  assert.equal(readme.includes('npm run materialized:shell'), true);
  assert.equal(readme.includes('npm run materialized:aggregate'), true);
  assert.equal(readme.includes('npm run materialized:bridge'), true);
  assert.equal(readme.includes('CheckPCCPackexp status = accepted'), true);
  assert.equal(readme.includes('ExternalAcceptRunReplay verdict = accept'), true);
  assert.equal(readme.includes('CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP'), true);
});

test('package.json exposes materialized path smoke scripts', async () => {
  const pkg = JSON.parse(await fs.readFile(new URL('../package.json', import.meta.url), 'utf8'));

  for (const script of [
    'materialized:shell',
    'materialized:shell:full',
    'materialized:aggregate',
    'materialized:aggregate:full',
    'materialized:bridge',
    'materialized:bridge:full',
    'materialized:write-fixtures',
    'materialized:write-fixtures:full',    
  ]) {
    assert.equal(typeof pkg.scripts[script], 'string');
    assert.equal(pkg.scripts[script].length > 0, true);
  }
});

test('npm run materialized:shell checks a materialized package shell file', async (t) => {
  const filePath = await writeTempJsonFile0(t, 'MaterializedPCCPack0.json', makeMaterializedAggregateShell0());

  const child = spawnNpmRun0('materialized:shell', filePath);

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = parseNpmJsonStdout0(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPackShellFile0');
});

test('npm run materialized:aggregate checks the full materialized aggregate file', async (t) => {
  const filePath = await writeTempJsonFile0(t, 'MaterializedPCCPack0.json', makeMaterializedAggregateShell0());

  const child = spawnNpmRun0('materialized:aggregate', filePath);

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = parseNpmJsonStdout0(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAggregateFile0');
  assert.equal(out.phaseCount > 0, true);
});

test('npm run materialized:bridge accepts pending bridge without public conclusion', async (t) => {
  const filePath = await writeTempJsonFile0(
    t,
    'MaterializedAcceptanceBridge0.json',
    makeMaterializedAcceptanceBridge0(),
  );

  const child = spawnNpmRun0('materialized:bridge', filePath);

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = parseNpmJsonStdout0(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.replayVerdict, 'pending');
  assert.equal(out.publicConclusionEmitted, false);
});

test('npm run materialized:bridge accepts accepted bridge with public conclusion emission', async (t) => {
  const filePath = await writeTempJsonFile0(
    t,
    'MaterializedAcceptanceBridge0.json',
    makeAcceptedMaterializedAcceptanceBridge0(),
  );

  const child = spawnNpmRun0('materialized:bridge', filePath);

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = parseNpmJsonStdout0(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.replayVerdict, 'accept');
  assert.equal(out.publicConclusionEmitted, true);
});

async function writeTempJsonFile0(t, filename, value) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-path-readme-'));
  const filePath = path.join(dir, filename);

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  await fs.writeFile(filePath, JSON.stringify(value, null, 2), 'utf8');

  return filePath;
}
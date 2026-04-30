import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  MATERIALIZED_FIXTURE_FILENAMES0,
  WriteMaterializedFixtureSet0,
} from '../pcc-materialized-fixture-writer0.mjs';

import {
  CheckMaterializedAggregateFile0,
} from '../pcc-materialized-aggregate0.mjs';

import {
  CheckMaterializedAcceptanceBridgeFile0,
} from '../pcc-materialized-acceptance-bridge0.mjs';

function npmCommand0() {
  return process.platform === 'win32'
    ? 'npm.cmd'
    : 'npm';
}

function parseJsonFromStdout0(stdout) {
  const firstBrace = stdout.indexOf('{');

  assert.notEqual(firstBrace, -1, stdout);

  return JSON.parse(stdout.slice(firstBrace));
}

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

test('WriteMaterializedFixtureSet0 writes and verifies all materialized fixture files', async (t) => {
  const outputDir = await makeTempDir0(t);
  const out = await WriteMaterializedFixtureSet0({
    outputDir,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'WriteMaterializedFixtureSet0');
  assert.equal(out.NF.fileCount, 3);
  assert.equal(out.NF.verification.verified, true);

  for (const filename of Object.values(MATERIALIZED_FIXTURE_FILENAMES0)) {
    const stat = await fs.stat(path.join(outputDir, filename));

    assert.equal(stat.isFile(), true);
  }
});

test('generated MaterializedPCCPack0 fixture passes aggregate checking', async (t) => {
  const outputDir = await makeTempDir0(t);

  await WriteMaterializedFixtureSet0({
    outputDir,
  });

  const out = await CheckMaterializedAggregateFile0(
    path.join(outputDir, MATERIALIZED_FIXTURE_FILENAMES0.pack),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAggregateFile0');
});

test('generated pending and accepted bridge fixtures pass bridge checking', async (t) => {
  const outputDir = await makeTempDir0(t);

  await WriteMaterializedFixtureSet0({
    outputDir,
  });

  const pending = await CheckMaterializedAcceptanceBridgeFile0(
    path.join(outputDir, MATERIALIZED_FIXTURE_FILENAMES0.pendingBridge),
  );

  assert.equal(pending.tag, 'accept');
  assert.equal(pending.NF.replayVerdict, 'pending');
  assert.equal(pending.NF.publicConclusionEmitted, false);

  const accepted = await CheckMaterializedAcceptanceBridgeFile0(
    path.join(outputDir, MATERIALIZED_FIXTURE_FILENAMES0.acceptedBridge),
  );

  assert.equal(accepted.tag, 'accept');
  assert.equal(accepted.NF.replayVerdict, 'accept');
  assert.equal(accepted.NF.publicConclusionEmitted, true);
});

test('WriteMaterializedFixtureSet0 writes canonical package envelope bytes when requested', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await WriteMaterializedFixtureSet0({
    outputDir,
    canonicalEnvelopeBytes: true,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.canonicalEnvelopeBytes, true);

  const packFile = path.join(outputDir, MATERIALIZED_FIXTURE_FILENAMES0.pack);
  const aggregate = await CheckMaterializedAggregateFile0(packFile, {
    loaderConfig: {
      requireCanonicalEnvelopeBytes: true,
    },
  });

  assert.equal(aggregate.tag, 'accept');
});

test('WriteMaterializedFixtureSet0 rejects existing file when overwrite is false', async (t) => {
  const outputDir = await makeTempDir0(t);

  const first = await WriteMaterializedFixtureSet0({
    outputDir,
  });

  assert.equal(first.tag, 'accept');

  const second = await WriteMaterializedFixtureSet0({
    outputDir,
    overwrite: false,
  });

  assert.equal(second.tag, 'reject');
  assert.equal(second.checker, 'WriteMaterializedFixtureSet0');
  assert.equal(second.Coord, 'WriteMaterializedFixtureSet0.writeFixtures');
  assert.equal(second.Witness.reason, 'failed to write materialized fixture file');
});

test('WriteMaterializedFixtureSet0 validates config shape', async () => {
  const out = await WriteMaterializedFixtureSet0({
    outputDir: '',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'WriteMaterializedFixtureSet0');
  assert.equal(out.Coord, 'WriteMaterializedFixtureSet0.config');
  assert.deepEqual(out.Path, ['outputDir']);
  assert.equal(out.Witness.reason, 'MaterializedFixtureWriterConfig0 outputDir must be a non-empty string');
});

test('bin/write-materialized-fixtures0.mjs writes fixtures and emits summary', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/write-materialized-fixtures0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--out', outputDir], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'WriteMaterializedFixtureSet0');
  assert.equal(out.fileCount, 3);
  assert.equal(out.verified, true);
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/write-materialized-fixtures0.mjs --full emits full accept record', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/write-materialized-fixtures0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--out', outputDir, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'WriteMaterializedFixtureSet0');
  assert.equal(out.NF.kind, 'MaterializedFixtureWriter0NF');
  assert.equal(Array.isArray(out.Ledger), true);
});

test('npm run materialized:write-fixtures writes fixtures', async (t) => {
  const outputDir = await makeTempDir0(t);

  const child = spawnSync(npmCommand0(), ['run', 'materialized:write-fixtures', '--', outputDir], {
    encoding: 'utf8',
    shell: process.platform === 'win32',
    windowsHide: true,
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = parseJsonFromStdout0(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.fileCount, 3);
  assert.equal(out.verified, true);
});

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-fixture-writer-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
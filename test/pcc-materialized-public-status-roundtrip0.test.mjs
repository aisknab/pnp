import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CheckMaterializedPublicStatusRoundtrip0,
  MATERIALIZED_PUBLIC_STATUS_ROUNDTRIP_CHECKS0,
} from '../pcc-materialized-public-status-roundtrip0.mjs';

import {
  MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0,
} from '../pcc-materialized-accept-run-fixtures0.mjs';

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

test('CheckMaterializedPublicStatusRoundtrip0 writes deterministic fixtures and verifies direct and CLI public status paths', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await CheckMaterializedPublicStatusRoundtrip0({
    outputDir,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPublicStatusRoundtrip0');
  assert.equal(out.NF.kind, 'MaterializedPublicStatusRoundtrip0NF');
  assert.equal(out.NF.fileCount, 4);
  assert.equal(out.NF.deterministic, true);
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.acceptedPublicConclusionOnly, true);
  assert.equal(out.NF.byteComparisons.length, 4);
  assert.equal(out.NF.directRecords.length, 4);
  assert.equal(out.NF.cliRecords.length, 4);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedPublicStatusRoundtrip0 accepts canonical envelope public status fixtures', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await CheckMaterializedPublicStatusRoundtrip0({
    outputDir,
    canonicalEnvelopeBytes: true,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.canonicalEnvelopeBytes, true);
  assert.equal(out.NF.deterministic, true);
  assert.equal(out.NF.acceptedPublicConclusionOnly, true);
});

test('CheckMaterializedPublicStatusRoundtrip0 can skip CLI checks while retaining direct verification', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await CheckMaterializedPublicStatusRoundtrip0({
    outputDir,
    runCliChecks: false,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.directRecords.length, 4);
  assert.deepEqual(out.NF.cliRecords, []);
});

test('CheckMaterializedPublicStatusRoundtrip0 rejects non-deterministic second write bytes', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await CheckMaterializedPublicStatusRoundtrip0({
    outputDir,
    runCliChecks: false,
    mutateSecondWrite: async ({ outputDir: dir }) => {
      await fs.appendFile(
        path.join(dir, MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.accepted),
        '\n',
        'utf8',
      );
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPublicStatusRoundtrip0');
  assert.equal(out.Coord, 'CheckMaterializedPublicStatusRoundtrip0.compareBytes');
  assert.deepEqual(out.Path, ['files', MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.accepted]);
  assert.equal(out.Witness.reason, 'materialized public status fixture bytes are not deterministic across repeated writes');
});

test('CheckMaterializedPublicStatusRoundtrip0 validates outputDir shape', async () => {
  const out = await CheckMaterializedPublicStatusRoundtrip0({
    outputDir: '',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPublicStatusRoundtrip0');
  assert.equal(out.Coord, 'CheckMaterializedPublicStatusRoundtrip0.config');
  assert.deepEqual(out.Path, ['outputDir']);
  assert.equal(out.Witness.reason, 'MaterializedPublicStatusRoundtripConfig0 outputDir must be a non-empty string');
});

test('materialized public status roundtrip phase names are stable', () => {
  assert.deepEqual(MATERIALIZED_PUBLIC_STATUS_ROUNDTRIP_CHECKS0, [
    'WriteMaterializedFinalRunFixtureSet0.first',
    'WriteMaterializedFinalRunFixtureSet0.second',
    'CompareMaterializedPublicStatusFixtureBytes0',
    'CheckMaterializedAggregateFile0',
    'CheckMaterializedPublicStatusFile0.pending',
    'CheckMaterializedPublicStatusFile0.rejected',
    'CheckMaterializedPublicStatusFile0.accepted',
    'CLI.check-materialized-aggregate0',
    'CLI.check-materialized-public-status0.pending',
    'CLI.check-materialized-public-status0.rejected',
    'CLI.check-materialized-public-status0.accepted',
  ]);
});

test('bin/check-materialized-public-status-roundtrip0.mjs emits accepted summary', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-public-status-roundtrip0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--out', outputDir], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

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

test('bin/check-materialized-public-status-roundtrip0.mjs --full emits full record', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-public-status-roundtrip0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--out', outputDir, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPublicStatusRoundtrip0');
  assert.equal(out.NF.kind, 'MaterializedPublicStatusRoundtrip0NF');
  assert.equal(Array.isArray(out.Ledger), true);
});

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-public-status-roundtrip-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
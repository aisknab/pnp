import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CheckMaterializedFinalRunRoundtrip0,
  MATERIALIZED_FINAL_RUN_ROUNDTRIP_CHECKS0,
} from '../pcc-materialized-final-run-roundtrip0.mjs';

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

test('CheckMaterializedFinalRunRoundtrip0 writes deterministic final-run fixtures and verifies direct and CLI paths', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await CheckMaterializedFinalRunRoundtrip0({
    outputDir,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFinalRunRoundtrip0');
  assert.equal(out.NF.kind, 'MaterializedFinalRunRoundtrip0NF');
  assert.equal(out.NF.fileCount, 4);
  assert.equal(out.NF.deterministic, true);
  assert.equal(out.NF.acceptedPublicConclusionOnly, true);
  assert.equal(out.NF.byteComparisons.length, 4);
  assert.equal(out.NF.directRecords.length, 4);
  assert.equal(out.NF.cliRecords.length, 4);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedFinalRunRoundtrip0 accepts canonical envelope final-run fixtures', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await CheckMaterializedFinalRunRoundtrip0({
    outputDir,
    canonicalEnvelopeBytes: true,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.canonicalEnvelopeBytes, true);
  assert.equal(out.NF.deterministic, true);
  assert.equal(out.NF.acceptedPublicConclusionOnly, true);
});

test('CheckMaterializedFinalRunRoundtrip0 can skip CLI checks while retaining direct verification', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await CheckMaterializedFinalRunRoundtrip0({
    outputDir,
    runCliChecks: false,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.directRecords.length, 4);
  assert.deepEqual(out.NF.cliRecords, []);
});

test('CheckMaterializedFinalRunRoundtrip0 rejects non-deterministic second write bytes', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await CheckMaterializedFinalRunRoundtrip0({
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
  assert.equal(out.checker, 'CheckMaterializedFinalRunRoundtrip0');
  assert.equal(out.Coord, 'CheckMaterializedFinalRunRoundtrip0.compareBytes');
  assert.deepEqual(out.Path, ['files', MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.accepted]);
  assert.equal(out.Witness.reason, 'final-run fixture bytes are not deterministic across repeated writes');
});

test('CheckMaterializedFinalRunRoundtrip0 validates outputDir shape', async () => {
  const out = await CheckMaterializedFinalRunRoundtrip0({
    outputDir: '',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalRunRoundtrip0');
  assert.equal(out.Coord, 'CheckMaterializedFinalRunRoundtrip0.config');
  assert.deepEqual(out.Path, ['outputDir']);
  assert.equal(out.Witness.reason, 'MaterializedFinalRunRoundtripConfig0 outputDir must be a non-empty string');
});

test('materialized final-run roundtrip phase names are stable', () => {
  assert.deepEqual(MATERIALIZED_FINAL_RUN_ROUNDTRIP_CHECKS0, [
    'WriteMaterializedFinalRunFixtureSet0.first',
    'WriteMaterializedFinalRunFixtureSet0.second',
    'CompareFinalRunFixtureBytes0',
    'CheckMaterializedAggregateFile0',
    'CheckMaterializedFinalVerdictFile0.pending',
    'CheckMaterializedFinalVerdictFile0.reject',
    'CheckMaterializedFinalVerdictFile0.accepted',
    'CLI.check-materialized-aggregate0',
    'CLI.check-materialized-final-verdict0.pending',
    'CLI.check-materialized-final-verdict0.reject',
    'CLI.check-materialized-final-verdict0.accepted',
  ]);
});

test('bin/check-materialized-final-run-roundtrip0.mjs emits accepted summary', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-final-run-roundtrip0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--out', outputDir], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFinalRunRoundtrip0');
  assert.equal(out.fileCount, 4);
  assert.equal(out.deterministic, true);
  assert.equal(out.acceptedPublicConclusionOnly, true);
  assert.equal(out.directRecordCount, 4);
  assert.equal(out.cliRecordCount, 4);
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/check-materialized-final-run-roundtrip0.mjs --full emits full record', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-final-run-roundtrip0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--out', outputDir, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFinalRunRoundtrip0');
  assert.equal(out.NF.kind, 'MaterializedFinalRunRoundtrip0NF');
  assert.equal(Array.isArray(out.Ledger), true);
});

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-final-run-roundtrip-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
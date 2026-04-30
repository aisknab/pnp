import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CheckMaterializedFixtureRoundtrip0,
  MATERIALIZED_ROUNDTRIP_CHECKS0,
} from '../pcc-materialized-fixture-roundtrip0.mjs';

import {
  MATERIALIZED_FIXTURE_FILENAMES0,
} from '../pcc-materialized-fixture-writer0.mjs';

function childFailureMessage0(child) {
  return [
    child.error?.message ?? '',
    child.stderr ?? '',
    child.stdout ?? '',
  ].filter((entry) => entry.length > 0).join('\n');
}

test('CheckMaterializedFixtureRoundtrip0 writes deterministic fixtures and verifies direct and CLI paths', async (t) => {
  const base = await makeTempDir0(t);

  const out = await CheckMaterializedFixtureRoundtrip0({
    outputDirA: path.join(base, 'a'),
    outputDirB: path.join(base, 'b'),
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFixtureRoundtrip0');
  assert.equal(out.NF.kind, 'MaterializedFixtureRoundtrip0NF');
  assert.equal(out.NF.fileCount, 3);
  assert.equal(out.NF.deterministic, true);
  assert.equal(out.NF.byteComparisons.length, 3);
  assert.equal(out.NF.directRecords.length, 4);
  assert.equal(out.NF.cliRecords.length, 4);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedFixtureRoundtrip0 accepts canonical envelope fixture roundtrip', async (t) => {
  const base = await makeTempDir0(t);

  const out = await CheckMaterializedFixtureRoundtrip0({
    outputDirA: path.join(base, 'a'),
    outputDirB: path.join(base, 'b'),
    canonicalEnvelopeBytes: true,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.canonicalEnvelopeBytes, true);
  assert.equal(out.NF.deterministic, true);
});

test('CheckMaterializedFixtureRoundtrip0 can skip CLI checks while retaining direct verification', async (t) => {
  const base = await makeTempDir0(t);

  const out = await CheckMaterializedFixtureRoundtrip0({
    outputDirA: path.join(base, 'a'),
    outputDirB: path.join(base, 'b'),
    runCliChecks: false,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.directRecords.length, 4);
  assert.deepEqual(out.NF.cliRecords, []);
});

test('CheckMaterializedFixtureRoundtrip0 rejects non-deterministic second write bytes', async (t) => {
  const base = await makeTempDir0(t);

  const out = await CheckMaterializedFixtureRoundtrip0({
    outputDirA: path.join(base, 'a'),
    outputDirB: path.join(base, 'b'),
    runCliChecks: false,
    mutateSecondWrite: async ({ outputDir }) => {
      await fs.appendFile(
        path.join(outputDir, MATERIALIZED_FIXTURE_FILENAMES0.pack),
        '\n',
        'utf8',
      );
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFixtureRoundtrip0');
  assert.equal(out.Coord, 'CheckMaterializedFixtureRoundtrip0.compareBytes');
  assert.deepEqual(out.Path, ['files', MATERIALIZED_FIXTURE_FILENAMES0.pack]);
  assert.equal(out.Witness.reason, 'roundtrip fixture bytes are not deterministic across repeated writes');
});

test('CheckMaterializedFixtureRoundtrip0 validates distinct output directories', async (t) => {
  const base = await makeTempDir0(t);

  const out = await CheckMaterializedFixtureRoundtrip0({
    outputDirA: base,
    outputDirB: base,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFixtureRoundtrip0');
  assert.equal(out.Coord, 'CheckMaterializedFixtureRoundtrip0.config');
  assert.deepEqual(out.Path, ['outputDirB']);
  assert.equal(out.Witness.reason, 'roundtrip output directories must be distinct');
});

test('materialized roundtrip phase names are stable', () => {
  assert.deepEqual(MATERIALIZED_ROUNDTRIP_CHECKS0, [
    'WriteMaterializedFixtureSet0.first',
    'WriteMaterializedFixtureSet0.second',
    'CompareFixtureBytes0',
    'CheckMaterializedPCCPackShellFile0',
    'CheckMaterializedAggregateFile0',
    'CheckMaterializedAcceptanceBridgeFile0.pending',
    'CheckMaterializedAcceptanceBridgeFile0.accepted',
    'CLI.check-materialized-shell0',
    'CLI.check-materialized-aggregate0',
    'CLI.check-materialized-acceptance-bridge0.pending',
    'CLI.check-materialized-acceptance-bridge0.accepted',
  ]);
});

test('bin/check-materialized-fixture-roundtrip0.mjs emits accepted summary', async (t) => {
  const base = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-fixture-roundtrip0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--out', base], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFixtureRoundtrip0');
  assert.equal(out.fileCount, 3);
  assert.equal(out.deterministic, true);
  assert.equal(out.directRecordCount, 4);
  assert.equal(out.cliRecordCount, 4);
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/check-materialized-fixture-roundtrip0.mjs --full emits full record', async (t) => {
  const base = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-fixture-roundtrip0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--out', base, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFixtureRoundtrip0');
  assert.equal(out.NF.kind, 'MaterializedFixtureRoundtrip0NF');
  assert.equal(Array.isArray(out.Ledger), true);
});

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-fixture-roundtrip-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
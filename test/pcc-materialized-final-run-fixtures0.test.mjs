import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CheckMaterializedFinalVerdictFile0,
} from '../pcc-materialized-final-verdict0.mjs';

import {
  MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0,
} from '../pcc-materialized-accept-run-fixtures0.mjs';

import {
  WriteMaterializedFinalRunFixtureSet0,
} from '../pcc-materialized-final-run-fixtures0.mjs';

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

test('WriteMaterializedFinalRunFixtureSet0 writes and verifies final-run fixtures', async (t) => {
  const outputDir = await makeTempDir0(t);
  const out = await WriteMaterializedFinalRunFixtureSet0({
    outputDir,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'WriteMaterializedFinalRunFixtureSet0');
  assert.equal(out.NF.fileCount, 3);
  assert.equal(out.NF.directVerification.verified, true);
  assert.equal(out.NF.cliVerification.verified, true);

  for (const filename of Object.values(MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0)) {
    const stat = await fs.stat(path.join(outputDir, filename));

    assert.equal(stat.isFile(), true, filename);
  }
});

test('written final-run fixtures verify with expected final verdicts', async (t) => {
  const outputDir = await makeTempDir0(t);

  await WriteMaterializedFinalRunFixtureSet0({
    outputDir,
  });

  const pending = await CheckMaterializedFinalVerdictFile0(path.join(outputDir, MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.pending));
  assert.equal(pending.tag, 'accept');
  assert.equal(pending.NF.verdict, 'pending');
  assert.equal(pending.NF.publicConclusionEmitted, false);
  assert.equal(pending.NF.publicConclusion, null);

  const reject = await CheckMaterializedFinalVerdictFile0(path.join(outputDir, MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.reject));
  assert.equal(reject.tag, 'accept');
  assert.equal(reject.NF.verdict, 'reject');
  assert.equal(reject.NF.publicConclusionEmitted, false);
  assert.equal(reject.NF.publicConclusion, null);
  assert.equal(reject.NF.rejectLogCount, 1);

  const accepted = await CheckMaterializedFinalVerdictFile0(path.join(outputDir, MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.accepted));
  assert.equal(accepted.tag, 'accept');
  assert.equal(accepted.NF.verdict, 'accept');
  assert.equal(accepted.NF.publicConclusionEmitted, true);
  assert.equal(accepted.NF.publicConclusion.consequent, 'P = NP');
});

test('WriteMaterializedFinalRunFixtureSet0 can write canonical envelope bytes', async (t) => {
  const outputDir = await makeTempDir0(t);

  const out = await WriteMaterializedFinalRunFixtureSet0({
    outputDir,
    canonicalEnvelopeBytes: true,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.canonicalEnvelopeBytes, true);

  const accepted = await CheckMaterializedFinalVerdictFile0(path.join(outputDir, MATERIALIZED_ACCEPT_RUN_FIXTURE_FILENAMES0.accepted));

  assert.equal(accepted.tag, 'accept');
  assert.equal(accepted.NF.verdict, 'accept');
});

test('WriteMaterializedFinalRunFixtureSet0 rejects existing files when overwrite is false', async (t) => {
  const outputDir = await makeTempDir0(t);

  const first = await WriteMaterializedFinalRunFixtureSet0({
    outputDir,
  });

  assert.equal(first.tag, 'accept');

  const second = await WriteMaterializedFinalRunFixtureSet0({
    outputDir,
    overwrite: false,
  });

  assert.equal(second.tag, 'reject');
  assert.equal(second.checker, 'WriteMaterializedFinalRunFixtureSet0');
  assert.equal(second.Coord, 'WriteMaterializedFinalRunFixtureSet0.acceptRunFixtures');
});

test('WriteMaterializedFinalRunFixtureSet0 validates config shape', async () => {
  const out = await WriteMaterializedFinalRunFixtureSet0({
    outputDir: '',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'WriteMaterializedFinalRunFixtureSet0');
  assert.equal(out.Coord, 'WriteMaterializedFinalRunFixtureSet0.config');
  assert.deepEqual(out.Path, ['outputDir']);
  assert.equal(out.Witness.reason, 'MaterializedFinalRunFixtureWriterConfig0 outputDir must be a non-empty string');
});

test('bin/write-materialized-final-run-fixtures0.mjs writes fixtures and emits summary', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/write-materialized-final-run-fixtures0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--out', outputDir], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'WriteMaterializedFinalRunFixtureSet0');
  assert.equal(out.fileCount, 3);
  assert.equal(out.directVerified, true);
  assert.equal(out.cliVerified, true);
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/write-materialized-final-run-fixtures0.mjs --full emits full accept record', async (t) => {
  const outputDir = await makeTempDir0(t);
  const cliPath = fileURLToPath(new URL('../bin/write-materialized-final-run-fixtures0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, '--out', outputDir, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'WriteMaterializedFinalRunFixtureSet0');
  assert.equal(out.NF.kind, 'MaterializedFinalRunFixtureWriter0NF');
  assert.equal(Array.isArray(out.Ledger), true);
});

test('npm run materialized:write-final-runs writes and verifies final-run fixtures', async (t) => {
  const outputDir = await makeTempDir0(t);

  const child = spawnSync(npmCommand0(), ['run', 'materialized:write-final-runs', '--', outputDir], {
    encoding: 'utf8',
    shell: process.platform === 'win32',
    windowsHide: true,
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = parseJsonFromStdout0(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.fileCount, 3);
  assert.equal(out.directVerified, true);
  assert.equal(out.cliVerified, true);
});

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-final-run-fixtures-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
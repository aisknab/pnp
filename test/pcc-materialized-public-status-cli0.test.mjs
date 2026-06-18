import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
  CheckMaterializedAggregateFile0,
  makeMaterializedAggregateShell0,
} from '../pcc-materialized-aggregate0.mjs';

import {
  makeMaterializedAcceptRun0,
  makeMaterializedReplayFirstFailure0,
  makeMaterializedReplayTranscript0,
} from '../pcc-materialized-accept-run0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
} from '../pcc-materialized-pack0.mjs';

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

test('bin/check-materialized-public-status0.mjs emits pending status with no public conclusion', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const acceptRunFile = await writeTempJsonFile0(
    t,
    'MaterializedAcceptRun0.pending.json',
    makeMaterializedAcceptRun0({
      packFilePath,
      aggregateDigest,
      verdict: 'pending',
    }),
  );
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-public-status0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, acceptRunFile], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.materializedPath, true);
  assert.equal(out.syntheticRunAll, false);
  assert.equal(out.status, 'pending');
  assert.equal(out.verdict, 'pending');
  assert.equal(out.replayAccepted, false);
  assert.equal(out.publicConclusionEmitted, false);
  assert.equal(out.publicConclusion, null);
  assert.equal(out.claimBoundary, 'conditional-on-accepted-materialized-final-verdict');
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/check-materialized-public-status0.mjs emits rejected status with no public conclusion', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const firstFailure = makeMaterializedReplayFirstFailure0({
    coord: 'Replay.first.public-status.reject',
    path: [
      'ReplayTranscript',
    ],
    rejectionClass: 'ReplayMismatch',
  });
  const replayTranscript = makeMaterializedReplayTranscript0({
    verdict: 'reject',
    firstFailure,
  });
  const acceptRunFile = await writeTempJsonFile0(
    t,
    'MaterializedAcceptRun0.reject.json',
    makeMaterializedAcceptRun0({
      packFilePath,
      aggregateDigest,
      verdict: 'reject',
      replayTranscript,
    }),
  );
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-public-status0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, acceptRunFile], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.status, 'rejected');
  assert.equal(out.verdict, 'reject');
  assert.equal(out.replayAccepted, false);
  assert.equal(out.publicConclusionEmitted, false);
  assert.equal(out.publicConclusion, null);
  assert.equal(out.rejectLogCount, 1);
});

test('bin/check-materialized-public-status0.mjs emits accepted status and public conclusion', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const acceptRunFile = await writeTempJsonFile0(
    t,
    'MaterializedAcceptRun0.accept.json',
    makeMaterializedAcceptRun0({
      packFilePath,
      aggregateDigest,
      verdict: 'accept',
    }),
  );
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-public-status0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, acceptRunFile], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.status, 'accepted');
  assert.equal(out.verdict, 'accept');
  assert.equal(out.replayAccepted, true);
  assert.equal(out.publicConclusionEmitted, true);
  assert.deepEqual(out.publicConclusion, MATERIALIZED_PACK_PUBLIC_BOUNDARY0);
  assert.equal(out.publicConclusion.consequent, 'P = NP');
});

test('bin/check-materialized-public-status0.mjs --full emits complete public status record', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const acceptRunFile = await writeTempJsonFile0(
    t,
    'MaterializedAcceptRun0.accept.json',
    makeMaterializedAcceptRun0({
      packFilePath,
      aggregateDigest,
      verdict: 'accept',
    }),
  );
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-public-status0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, acceptRunFile, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.NF.kind, 'MaterializedPublicStatus0NF');
  assert.equal(out.NF.status, 'accepted');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(Array.isArray(out.Ledger), true);
});

test('bin/check-materialized-public-status0.mjs rejects public conclusion before accepted replay', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const run = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'pending',
  });

  run.Verdict = {
    ...run.Verdict,
    publicConclusionEmitted: true,
    publicConclusion: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
  };

  const acceptRunFile = await writeTempJsonFile0(t, 'MaterializedAcceptRun0.bad.json', run);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-public-status0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, acceptRunFile], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.coord, 'CheckMaterializedPublicStatus0.FinalVerdict');
  assert.equal(out.witness.detail.inner.coord, 'CheckMaterializedFinalVerdictFile0.AcceptRunFile');
});

test('npm run materialized:public-status checks an accepted materialized accept-run file', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const acceptRunFile = await writeTempJsonFile0(
    t,
    'MaterializedAcceptRun0.accept.json',
    makeMaterializedAcceptRun0({
      packFilePath,
      aggregateDigest,
      verdict: 'accept',
    }),
  );

  const child = spawnSync(npmCommand0(), ['run', 'materialized:public-status', '--', acceptRunFile], {
    encoding: 'utf8',
    shell: process.platform === 'win32',
    windowsHide: true,
  });

  assert.equal(child.status, 0, childFailureMessage0(child));

  const out = parseJsonFromStdout0(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.status, 'accepted');
  assert.equal(out.publicConclusionEmitted, true);
});

test('bin/check-materialized-public-status0.mjs rejects invalid JSON accept-run file', async (t) => {
  const acceptRunFile = await writeTempTextFile0(t, 'MaterializedAcceptRun0.bad.json', '{ not json');
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-public-status0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, acceptRunFile], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.coord, 'CheckMaterializedPublicStatus0.FinalVerdict');
  assert.equal(out.witness.detail.inner.coord, 'CheckMaterializedFinalVerdictFile0.AcceptRunFile');
});

test('bin/check-materialized-public-status0.mjs exits nonzero without a file path', () => {
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-public-status0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'check-materialized-public-status0');
  assert.equal(out.coord, 'check-materialized-public-status0.args');
});

async function writeAggregatePack0(t) {
  const dir = await makeTempDir0(t);
  const packFilePath = path.join(dir, 'MaterializedPCCPack0.json');
  const shell = makeMaterializedAggregateShell0();

  await fs.writeFile(packFilePath, JSON.stringify(shell, null, 2), 'utf8');

  const aggregate = await CheckMaterializedAggregateFile0(packFilePath);

  assert.equal(aggregate.tag, 'accept');

  return {
    dir,
    packFilePath,
    aggregateDigest: aggregate.Digest,
  };
}

async function writeTempJsonFile0(t, filename, value) {
  return writeTempTextFile0(t, filename, JSON.stringify(value, null, 2));
}

async function writeTempTextFile0(t, filename, text) {
  const dir = await makeTempDir0(t);
  const filePath = path.join(dir, filename);

  await fs.writeFile(filePath, text, 'utf8');

  return filePath;
}

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-public-status-cli-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
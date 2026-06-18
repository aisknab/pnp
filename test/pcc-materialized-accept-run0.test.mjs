import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedAggregateFile0,
  makeMaterializedAggregateShell0,
} from '../pcc-materialized-aggregate0.mjs';

import {
  CheckMaterializedAcceptRun0,
  CheckMaterializedAcceptRunFile0,
  MATERIALIZED_ACCEPT_RUN_PHASES0,
  makeMaterializedAcceptRun0,
  makeMaterializedReplayFirstFailure0,
  makeMaterializedReplayTranscript0,
} from '../pcc-materialized-accept-run0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedAcceptRun0 accepts pending replay with no public conclusion', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const run = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'pending',
  });

  const out = await CheckMaterializedAcceptRun0(run);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptRun0');
  assert.equal(out.NF.kind, 'MaterializedAcceptRun0NF');
  assert.equal(out.NF.verdict, 'pending');
  assert.equal(out.NF.replayAccepted, false);
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion, null);
  assert.equal(out.NF.rejectLogCount, 0);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedAcceptRun0 accepts reject replay with one replayable first failure and no public conclusion', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const firstFailure = makeMaterializedReplayFirstFailure0({
    coord: 'Replay.first.bad.import',
    path: [
      'PackBytes',
      'Manifest',
      'packageImportEdges',
      0,
    ],
    rejectionClass: 'ForbiddenImport',
  });
  const transcript = makeMaterializedReplayTranscript0({
    verdict: 'reject',
    firstFailure,
  });
  const run = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'reject',
    replayTranscript: transcript,
  });

  const out = await CheckMaterializedAcceptRun0(run);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.verdict, 'reject');
  assert.equal(out.NF.replayAccepted, false);
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion, null);
  assert.equal(out.NF.rejectLogCount, 1);
});

test('CheckMaterializedAcceptRun0 accepts accepted replay and emits conditional public conclusion', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const run = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'accept',
  });

  const out = await CheckMaterializedAcceptRun0(run);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.replayAccepted, true);
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.deepEqual(out.NF.publicConclusion, MATERIALIZED_PACK_PUBLIC_BOUNDARY0);
});

test('CheckMaterializedAcceptRunFile0 accepts an accepted materialized accept-run file', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const run = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'accept',
  });
  const acceptRunFile = await writeTempJsonFile0(t, 'MaterializedAcceptRun0.json', run);

  const out = await CheckMaterializedAcceptRunFile0(acceptRunFile);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptRunFile0');
  assert.equal(out.NF.kind, 'MaterializedAcceptRunFile0NF');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.publicConclusionEmitted, true);
});

test('Materialized replay phase order is stable', () => {
  assert.equal(MATERIALIZED_ACCEPT_RUN_PHASES0.includes('CheckPCCPackexpPrecondition0'), true);
  assert.equal(MATERIALIZED_ACCEPT_RUN_PHASES0.includes('ExternalReplayTranscript0'), true);
  assert.equal(MATERIALIZED_ACCEPT_RUN_PHASES0.includes('EmitMaterializedAcceptRunVerdict0'), true);
});

test('CheckMaterializedAcceptRun0 rejects aggregate digest mismatch', async (t) => {
  const { packFilePath } = await writeAggregatePack0(t);
  const run = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
    verdict: 'pending',
  });

  const out = await CheckMaterializedAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptRun0.AggregateCheck');
  assert.deepEqual(out.Path, ['AggregateCheck', 'digest']);
  assert.equal(out.Witness.reason, 'AggregateCheck digest must match CheckMaterializedAggregateFile0 digest');
});

test('CheckMaterializedAcceptRun0 rejects public conclusion before accepted replay', async (t) => {
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

  const out = await CheckMaterializedAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptRun0.Verdict');
  assert.deepEqual(out.Path, ['Verdict', 'publicConclusion']);
  assert.equal(out.Witness.reason, 'non-accept verdict must not emit public conclusion');
});

test('CheckMaterializedAcceptRun0 rejects transcript digest mismatch', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const run = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'pending',
  });

  run.ReplayTranscript = {
    ...run.ReplayTranscript,
    transcriptDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '1111111111111111111111111111111111111111111111111111111111111111',
    },
  };

  const out = await CheckMaterializedAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptRun0.ReplayTranscript');
  assert.deepEqual(out.Path, ['ReplayTranscript', 'transcriptDigest']);
  assert.equal(out.Witness.reason, 'ReplayTranscript transcriptDigest mismatch');
});

test('CheckMaterializedAcceptRun0 rejects reject transcript without reject log entry', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const run = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'reject',
  });

  run.RejectLog = [];

  const out = await CheckMaterializedAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptRun0.RejectLog');
  assert.deepEqual(out.Path, ['RejectLog']);
  assert.equal(out.Witness.reason, 'reject verdict must contain exactly one first rejection entry');
});

test('CheckMaterializedAcceptRun0 rejects embedded generated package bytes', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const run = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'pending',
  });

  run.GeneratedPackage = {
    ...run.GeneratedPackage,
    CoreBytes: '{"not":"allowed"}',
  };

  const out = await CheckMaterializedAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptRun0.noEmbeddedPackageBytes');
  assert.deepEqual(out.Path, ['GeneratedPackage', 'CoreBytes']);
  assert.equal(out.Witness.reason, 'GeneratedPackage ref must not embed generated package bytes or Pgen');
});

test('CheckMaterializedAcceptRun0 rejects generated package path whose aggregate fails', async (t) => {
  const dir = await makeTempDir0(t);
  const badPackFile = path.join(dir, 'MaterializedPCCPack0.bad.json');

  await fs.writeFile(
    badPackFile,
    JSON.stringify({
      kind: 'MaterializedPCCPack0',
      CoreBytes: 'not valid',
    }),
    'utf8',
  );

  const run = makeMaterializedAcceptRun0({
    packFilePath: badPackFile,
    aggregateDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '2222222222222222222222222222222222222222222222222222222222222222',
    },
    verdict: 'pending',
  });

  const out = await CheckMaterializedAcceptRun0(run);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptRun0.aggregate');
  assert.deepEqual(out.Path, ['GeneratedPackage', 'path']);
  assert.equal(out.Witness.reason, 'CheckMaterializedAggregateFile0 rejected');
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
  const dir = await makeTempDir0(t);
  const filePath = path.join(dir, filename);

  await fs.writeFile(filePath, JSON.stringify(value, null, 2), 'utf8');

  return filePath;
}

async function makeTempDir0(t) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-accept-run-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
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
  makeMaterializedAcceptRun0,
  makeMaterializedReplayFirstFailure0,
  makeMaterializedReplayTranscript0,
} from '../pcc-materialized-accept-run0.mjs';

import {
  CheckMaterializedPublicStatus0,
  CheckMaterializedPublicStatusFile0,
  MATERIALIZED_PUBLIC_STATUS_PHASES0,
  MATERIALIZED_PUBLIC_STATUS_POLICY0,
  makeMaterializedPublicStatusInput0,
} from '../pcc-materialized-public-status0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
} from '../pcc-materialized-pack0.mjs';

test('CheckMaterializedPublicStatusFile0 accepts pending final status with no public conclusion', async (t) => {
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

  const out = await CheckMaterializedPublicStatusFile0(acceptRunFile);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.NF.kind, 'MaterializedPublicStatus0NF');
  assert.deepEqual(out.NF.phaseOrder, MATERIALIZED_PUBLIC_STATUS_PHASES0);
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.status, 'pending');
  assert.equal(out.NF.verdict, 'pending');
  assert.equal(out.NF.replayAccepted, false);
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion, null);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedPublicStatusFile0 accepts rejected final status with no public conclusion', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const firstFailure = makeMaterializedReplayFirstFailure0({
    coord: 'Replay.first.materialized.public.status.reject',
    path: [
      'ReplayTranscript',
    ],
    rejectionClass: 'ReplayMismatch',
  });
  const transcript = makeMaterializedReplayTranscript0({
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
      replayTranscript: transcript,
    }),
  );

  const out = await CheckMaterializedPublicStatusFile0(acceptRunFile);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'rejected');
  assert.equal(out.NF.verdict, 'reject');
  assert.equal(out.NF.replayAccepted, false);
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion, null);
  assert.equal(out.NF.rejectLogCount, 1);
});

test('CheckMaterializedPublicStatusFile0 accepts accepted final status and emits public conclusion', async (t) => {
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

  const out = await CheckMaterializedPublicStatusFile0(acceptRunFile);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'accepted');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.replayAccepted, true);
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.deepEqual(out.NF.publicConclusion, MATERIALIZED_PACK_PUBLIC_BOUNDARY0);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
});

test('CheckMaterializedPublicStatus0 accepts explicit input object', async (t) => {
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

  const out = await CheckMaterializedPublicStatus0(makeMaterializedPublicStatusInput0({
    acceptRunFilePath: acceptRunFile,
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'accepted');
});

test('CheckMaterializedPublicStatus0 rejects invalid status policy before final verdict checking', async (t) => {
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

  const out = await CheckMaterializedPublicStatus0(makeMaterializedPublicStatusInput0({
    acceptRunFilePath: acceptRunFile,
    overrides: {
      StatusPolicy: {
        ...MATERIALIZED_PUBLIC_STATUS_POLICY0,
        publicConclusionOnlyAfterAccept: false,
      },
    },
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.Coord, 'CheckMaterializedPublicStatus0.StatusPolicy');
  assert.deepEqual(out.Path, ['StatusPolicy', 'publicConclusionOnlyAfterAccept']);
  assert.equal(out.Witness.reason, 'StatusPolicy must certify publicConclusionOnlyAfterAccept');
});

test('CheckMaterializedPublicStatus0 rejects public claim boundary mismatch', async (t) => {
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

  const out = await CheckMaterializedPublicStatus0(makeMaterializedPublicStatusInput0({
    acceptRunFilePath: acceptRunFile,
    overrides: {
      PublicClaimBoundary: {
        ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
        consequent: 'not P = NP',
      },
    },
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.Coord, 'CheckMaterializedPublicStatus0.PublicClaimBoundary');
  assert.deepEqual(out.Path, ['PublicClaimBoundary']);
  assert.equal(out.Witness.reason, 'PublicClaimBoundary mismatch');
});

test('CheckMaterializedPublicStatusFile0 rejects invalid accept-run file through final verdict checker', async (t) => {
  const acceptRunFile = await writeTempTextFile0(t, 'MaterializedAcceptRun0.bad.json', '{ not json');

  const out = await CheckMaterializedPublicStatusFile0(acceptRunFile);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.Coord, 'CheckMaterializedPublicStatus0.FinalVerdict');
  assert.deepEqual(out.Path, ['AcceptRunFilePath']);
  assert.equal(out.Witness.reason, 'CheckMaterializedFinalVerdictFile0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedFinalVerdictFile0.AcceptRunFile');
});

test('CheckMaterializedPublicStatusFile0 rejects accept-run that tries to emit public conclusion before accept', async (t) => {
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
  const out = await CheckMaterializedPublicStatusFile0(acceptRunFile);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedPublicStatus0');
  assert.equal(out.Coord, 'CheckMaterializedPublicStatus0.FinalVerdict');
  assert.equal(out.Witness.reason, 'CheckMaterializedFinalVerdictFile0 rejected');
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
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-public-status-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
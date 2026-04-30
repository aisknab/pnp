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
  CheckMaterializedFinalVerdict0,
  CheckMaterializedFinalVerdictFile0,
  MATERIALIZED_FINAL_VERDICT_PHASES0,
  makeMaterializedFinalVerdictInput0,
} from '../pcc-materialized-final-verdict0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedFinalVerdict0 accepts pending accept-run and emits no public conclusion', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const acceptRun = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'pending',
  });

  const out = await CheckMaterializedFinalVerdict0(acceptRun);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFinalVerdict0');
  assert.equal(out.NF.kind, 'MaterializedFinalVerdict0NF');
  assert.deepEqual(out.NF.phaseOrder, MATERIALIZED_FINAL_VERDICT_PHASES0);
  assert.equal(out.NF.verdict, 'pending');
  assert.equal(out.NF.replayAccepted, false);
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion, null);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedFinalVerdict0 accepts reject accept-run and emits no public conclusion', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const firstFailure = makeMaterializedReplayFirstFailure0({
    coord: 'Replay.first.failure',
    path: [
      'ReplayTranscript',
    ],
    rejectionClass: 'ReplayMismatch',
  });
  const replayTranscript = makeMaterializedReplayTranscript0({
    verdict: 'reject',
    firstFailure,
  });
  const acceptRun = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'reject',
    replayTranscript,
  });

  const out = await CheckMaterializedFinalVerdict0(makeMaterializedFinalVerdictInput0({
    acceptRun,
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.verdict, 'reject');
  assert.equal(out.NF.replayAccepted, false);
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion, null);
  assert.equal(out.NF.rejectLogCount, 1);
});

test('CheckMaterializedFinalVerdict0 accepts accepted replay and emits the conditional public conclusion', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const acceptRun = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'accept',
  });

  const out = await CheckMaterializedFinalVerdict0(acceptRun);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.replayAccepted, true);
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.deepEqual(out.NF.publicConclusion, MATERIALIZED_PACK_PUBLIC_BOUNDARY0);
});

test('CheckMaterializedFinalVerdictFile0 accepts an accepted accept-run file', async (t) => {
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

  const out = await CheckMaterializedFinalVerdictFile0(acceptRunFile);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFinalVerdictFile0');
  assert.equal(out.NF.kind, 'MaterializedFinalVerdictFile0NF');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.deepEqual(out.NF.publicConclusion, MATERIALIZED_PACK_PUBLIC_BOUNDARY0);
});

test('CheckMaterializedFinalVerdict0 rejects invalid final verdict policy', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const acceptRun = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'pending',
  });

  const out = await CheckMaterializedFinalVerdict0(makeMaterializedFinalVerdictInput0({
    acceptRun,
    overrides: {
      VerdictPolicy: {
        kind: 'MaterializedFinalVerdictPolicy0',
        version: 0,
        acceptsPendingVerdict: true,
        acceptsRejectVerdict: true,
        publicConclusionOnlyAfterAccept: false,
        rejectEmitsNoPublicConclusion: true,
        pendingEmitsNoPublicConclusion: true,
        acceptRunOutsideCore: true,
        generatedPackageRefOnly: true,
      },
    },
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalVerdict0');
  assert.equal(out.Coord, 'CheckMaterializedFinalVerdict0.VerdictPolicy');
  assert.deepEqual(out.Path, ['VerdictPolicy', 'publicConclusionOnlyAfterAccept']);
  assert.equal(out.Witness.reason, 'VerdictPolicy must certify publicConclusionOnlyAfterAccept');
});

test('CheckMaterializedFinalVerdict0 rejects public claim boundary mismatch', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const acceptRun = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'pending',
  });

  const out = await CheckMaterializedFinalVerdict0(makeMaterializedFinalVerdictInput0({
    acceptRun,
    overrides: {
      PublicClaimBoundary: {
        ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
        consequent: 'not P = NP',
      },
    },
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalVerdict0');
  assert.equal(out.Coord, 'CheckMaterializedFinalVerdict0.PublicClaimBoundary');
  assert.deepEqual(out.Path, ['PublicClaimBoundary']);
  assert.equal(out.Witness.reason, 'PublicClaimBoundary mismatch');
});

test('CheckMaterializedFinalVerdict0 rejects accept-run that tries to emit public conclusion before accepted replay', async (t) => {
  const { packFilePath, aggregateDigest } = await writeAggregatePack0(t);
  const acceptRun = makeMaterializedAcceptRun0({
    packFilePath,
    aggregateDigest,
    verdict: 'pending',
  });

  acceptRun.Verdict = {
    ...acceptRun.Verdict,
    publicConclusionEmitted: true,
    publicConclusion: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
  };

  const out = await CheckMaterializedFinalVerdict0(acceptRun);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalVerdict0');
  assert.equal(out.Coord, 'CheckMaterializedFinalVerdict0.AcceptRun');
  assert.deepEqual(out.Path, ['AcceptRun']);
  assert.equal(out.Witness.reason, 'CheckMaterializedAcceptRun0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedAcceptRun0.Verdict');
});

test('CheckMaterializedFinalVerdictFile0 rejects invalid accept-run file', async (t) => {
  const filePath = await writeTempTextFile0(t, 'MaterializedAcceptRun0.bad.json', '{ not json');

  const out = await CheckMaterializedFinalVerdictFile0(filePath);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalVerdictFile0');
  assert.equal(out.Coord, 'CheckMaterializedFinalVerdictFile0.AcceptRunFile');
  assert.deepEqual(out.Path, ['AcceptRunFile']);
  assert.equal(out.Witness.reason, 'CheckMaterializedAcceptRunFile0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedAcceptRunFile0.load');
});

test('CheckMaterializedFinalVerdict0 rejects accept-run whose aggregate package path fails', async (t) => {
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

  const acceptRun = makeMaterializedAcceptRun0({
    packFilePath: badPackFile,
    aggregateDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '2222222222222222222222222222222222222222222222222222222222222222',
    },
    verdict: 'pending',
  });

  const out = await CheckMaterializedFinalVerdict0(acceptRun);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalVerdict0');
  assert.equal(out.Coord, 'CheckMaterializedFinalVerdict0.AcceptRun');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedAcceptRun0.aggregate');
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
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-final-verdict-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  return dir;
}
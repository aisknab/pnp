import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedGeneratedAcceptRun0,
  makeMaterializedGeneratedAcceptRun0,
  writeMaterializedGeneratedAcceptRunFiles0,
} from '../pcc-accept-run-materialized0.mjs';

import {
  CheckAcceptRun0,
  EmitFinalVerdict0,
  ReplayAcceptRun0,
} from '../pcc-accept-run0.mjs';

test('CheckMaterializedGeneratedAcceptRun0 accepts a generated package accept-run envelope', async () => {
  const envelope = await makeMaterializedGeneratedAcceptRun0();
  const out = await CheckMaterializedGeneratedAcceptRun0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedGeneratedAcceptRun0');
  assert.equal(out.NF.kind, 'MaterializedGeneratedAcceptRun0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.generator, 'GeneratePCCPack');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.replayAccepted, true);
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner accept-run, replay, and final verdict checkers accept the materialized run', async () => {
  const envelope = await makeMaterializedGeneratedAcceptRun0();

  const acceptRun = await CheckAcceptRun0(envelope.AcceptRun);
  const replay = await ReplayAcceptRun0(envelope.AcceptRun);
  const finalVerdict = await EmitFinalVerdict0(envelope.AcceptRun);

  assert.equal(acceptRun.tag, 'accept');
  assert.equal(replay.tag, 'accept');
  assert.equal(finalVerdict.tag, 'accept');
  assert.equal(finalVerdict.NF.publicConclusionEmitted, true);
  assert.equal(finalVerdict.NF.publicConclusion.consequent, 'P = NP');
});

test('CheckMaterializedGeneratedAcceptRun0 rejects generated package byte mismatch', async () => {
  const envelope = await makeMaterializedGeneratedAcceptRun0();

  envelope.GeneratedPackage = {
    ...envelope.GeneratedPackage,
    outputPackBytes: '{}',
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedPackageDigest: undefined,
    outputPackDigest: undefined,
  };

  const out = await CheckMaterializedGeneratedAcceptRun0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedGeneratedAcceptRun0.linkage');
  assert.deepEqual(out.Path, ['GeneratedPackage', 'outputPackBytes']);
});

test('CheckMaterializedGeneratedAcceptRun0 exposes AcceptRun canonical byte mismatch', async () => {
  const envelope = await makeMaterializedGeneratedAcceptRun0();

  envelope.AcceptRun = {
    ...envelope.AcceptRun,
    GenCall: {
      ...envelope.AcceptRun.GenCall,
      outputPackBytes: '{}',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    acceptRunDigest: undefined,
  };

  const out = await CheckMaterializedGeneratedAcceptRun0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedGeneratedAcceptRun0.AcceptRun');
  assert.equal(out.Witness.detail.inner.coord, 'CheckAcceptRun0.verdict');
  assert.equal(out.Witness.detail.inner.witness.detail.replay.coord, 'ReplayAcceptRun0.generatorBytes');
});

test('CheckMaterializedGeneratedAcceptRun0 rejects forbidden fixture marker text', async () => {
  const envelope = await makeMaterializedGeneratedAcceptRun0();

  envelope.AcceptRun = {
    ...envelope.AcceptRun,
    PiRun: {
      ...envelope.AcceptRun.PiRun,
      note: 'todo marker must reject',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    acceptRunDigest: undefined,
  };

  const out = await CheckMaterializedGeneratedAcceptRun0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedGeneratedAcceptRun0.fixtureMarkers');
});


test('CheckMaterializedGeneratedAcceptRun0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeMaterializedGeneratedAcceptRun0();

  envelope.AcceptRun = {
    ...envelope.AcceptRun,
    PiRun: {
      ...envelope.AcceptRun.PiRun,
      note: 'synthetic marker must reject in strict marker mode',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    acceptRunDigest: undefined,
  };

  const out = await CheckMaterializedGeneratedAcceptRun0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedGeneratedAcceptRun0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});


test('CheckMaterializedGeneratedAcceptRun0 rejects stale linkage digest', async () => {
  const envelope = await makeMaterializedGeneratedAcceptRun0();

  envelope.Linkage = {
    ...envelope.Linkage,
    acceptRunDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckMaterializedGeneratedAcceptRun0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckMaterializedGeneratedAcceptRun0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'acceptRunDigest']);
});

test('writeMaterializedGeneratedAcceptRunFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-accept-run-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeMaterializedGeneratedAcceptRunFiles0(dir);

  assert.equal(result.checked.tag, 'accept');
  assert.equal(result.finalVerdict.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.generatedPath,
    result.files.acceptRunPath,
    result.files.pccPackPath,
    result.files.finalVerdictPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

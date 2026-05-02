import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedFinalCertificate0,
  makeMaterializedFinalCertificate0,
  writeMaterializedFinalCertificateFiles0,
} from '../pcc-final-certificate-materialized0.mjs';

import {
  EmitFinalVerdict0,
} from '../pcc-accept-run0.mjs';

test('CheckMaterializedFinalCertificate0 accepts a materialized final certificate appendix', async () => {
  const envelope = await makeMaterializedFinalCertificate0();
  const out = await CheckMaterializedFinalCertificate0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFinalCertificate0');
  assert.equal(out.NF.kind, 'MaterializedFinalCertificate0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.status, 'accepted');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicTheorem.consequent, 'P = NP');
  assert.equal(out.NF.releaseAuditStatus, 'not-attached-to-this-materialized-certificate-yet');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('fresh final verdict emission matches the certificate final verdict', async () => {
  const envelope = await makeMaterializedFinalCertificate0();
  const emitted = await EmitFinalVerdict0(envelope.GeneratedAcceptRunEnvelope.AcceptRun);

  assert.equal(emitted.tag, 'accept');
  assert.equal(envelope.FinalVerdict.tag, 'accept');
  assert.deepEqual(emitted.NF.publicConclusion, envelope.FinalVerdict.NF.publicConclusion);
  assert.equal(emitted.NF.publicConclusion.consequent, 'P = NP');
});

test('CheckMaterializedFinalCertificate0 rejects a tampered public theorem', async () => {
  const envelope = await makeMaterializedFinalCertificate0();

  envelope.Certificate = {
    ...envelope.Certificate,
    publicTheorem: {
      ...envelope.Certificate.publicTheorem,
      consequent: 'P != NP',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    certificateDigest: undefined,
  };

  const out = await CheckMaterializedFinalCertificate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckMaterializedFinalCertificate0.Certificate');
  assert.deepEqual(out.Path, ['Certificate', 'publicTheorem']);
});

test('CheckMaterializedFinalCertificate0 rejects a tampered final verdict record', async () => {
  const envelope = await makeMaterializedFinalCertificate0();

  envelope.FinalVerdict = {
    ...envelope.FinalVerdict,
    NF: {
      ...envelope.FinalVerdict.NF,
      publicConclusion: {
        ...envelope.FinalVerdict.NF.publicConclusion,
        consequent: 'P != NP',
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    finalVerdictDigest: undefined,
    finalVerdictRecordDigest: undefined,
  };

  const out = await CheckMaterializedFinalCertificate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckMaterializedFinalCertificate0.FinalVerdict');
  assert.deepEqual(out.Path, ['FinalVerdict', 'Digest']);
});

test('CheckMaterializedFinalCertificate0 rejects forbidden fixture marker text', async () => {
  const envelope = await makeMaterializedFinalCertificate0();

  envelope.Certificate = {
    ...envelope.Certificate,
    releaseAuditStatus: 'todo marker must reject',
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    certificateDigest: undefined,
  };

  const out = await CheckMaterializedFinalCertificate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckMaterializedFinalCertificate0.fixtureMarkers');
});

test('CheckMaterializedFinalCertificate0 can strictly reject current synthetic scaffold markers', async () => {
  const envelope = await makeMaterializedFinalCertificate0();

  const out = await CheckMaterializedFinalCertificate0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckMaterializedFinalCertificate0.fixtureMarkers');
});

test('CheckMaterializedFinalCertificate0 rejects stale linkage digest', async () => {
  const envelope = await makeMaterializedFinalCertificate0();

  envelope.Linkage = {
    ...envelope.Linkage,
    certificateDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckMaterializedFinalCertificate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckMaterializedFinalCertificate0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'certificateDigest']);
});

test('writeMaterializedFinalCertificateFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-final-certificate-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeMaterializedFinalCertificateFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.certificatePath,
    result.files.finalVerdictPath,
    result.files.generatedAcceptRunPath,
    result.files.acceptRunPath,
    result.files.pccPackPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

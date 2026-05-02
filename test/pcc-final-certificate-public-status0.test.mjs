import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckFinalCertificatePublicStatus0,
  makeFinalCertificatePublicStatus0,
  writeFinalCertificatePublicStatusFiles0,
} from '../pcc-final-certificate-public-status0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

function makeAcceptedReleaseAuditRecord0() {
  const nf = {
    kind: 'ReleaseAudit0NF',
    checker: 'CheckReleaseAudit0',
    version: 0,
    rootDir: '/materialized/test',
    materializedPublicStatusGateSummary: {
      acceptedPublicConclusionOnly: true,
    },
    publicConclusion: {
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
      conditional: true,
    },
  };

  return {
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckReleaseAudit0',
    version: 0,
    NF: nf,
    Digest: digestCanonical0(nf),
    Ledger: [],
    nf,
    digest: digestCanonical0(nf),
    ledger: [],
  };
}

test('CheckFinalCertificatePublicStatus0 accepts a final-certificate public status gate', async () => {
  const envelope = await makeFinalCertificatePublicStatus0();
  const out = await CheckFinalCertificatePublicStatus0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinalCertificatePublicStatus0');
  assert.equal(out.NF.kind, 'FinalCertificatePublicStatus0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.status, 'accepted');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.equal(out.NF.releaseAuditAttached, false);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckFinalCertificatePublicStatus0 accepts an attached release-audit record', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeFinalCertificatePublicStatus0({
    ReleaseAuditRecord: releaseAuditRecord,
  });

  const out = await CheckFinalCertificatePublicStatus0(envelope, {
    checkReleaseAuditRecord: true,
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.releaseAuditAttached, true);
  assert.deepEqual(out.NF.releaseAuditDigest, releaseAuditRecord.Digest);
  assert.equal(out.NF.releaseAuditStatus, 'attached');
});

test('CheckFinalCertificatePublicStatus0 rejects a tampered public conclusion', async () => {
  const envelope = await makeFinalCertificatePublicStatus0();

  envelope.PublicStatus = {
    ...envelope.PublicStatus,
    publicConclusion: {
      ...envelope.PublicStatus.publicConclusion,
      consequent: 'P != NP',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    publicStatusDigest: undefined,
  };

  const out = await CheckFinalCertificatePublicStatus0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckFinalCertificatePublicStatus0.PublicStatus');
  assert.deepEqual(out.Path, ['PublicStatus', 'publicConclusion']);
});

test('CheckFinalCertificatePublicStatus0 rejects an unattached release-audit requirement', async () => {
  const envelope = await makeFinalCertificatePublicStatus0();

  const out = await CheckFinalCertificatePublicStatus0(envelope, {
    checkReleaseAuditRecord: true,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckFinalCertificatePublicStatus0.ReleaseAudit');
  assert.deepEqual(out.Path, ['ReleaseAuditRecord']);
});

test('CheckFinalCertificatePublicStatus0 rejects forbidden fixture marker text', async () => {
  const envelope = await makeFinalCertificatePublicStatus0();

  envelope.PublicStatus = {
    ...envelope.PublicStatus,
    releaseAuditStatus: 'todo marker must reject',
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    publicStatusDigest: undefined,
  };

  const out = await CheckFinalCertificatePublicStatus0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckFinalCertificatePublicStatus0.fixtureMarkers');
});


test('CheckFinalCertificatePublicStatus0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeFinalCertificatePublicStatus0();

  envelope.PublicStatus = {
    ...envelope.PublicStatus,
    ScaffoldWitness: 'synthetic marker must reject in strict marker mode',
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    publicStatusDigest: undefined,
  };

  const out = await CheckFinalCertificatePublicStatus0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckFinalCertificatePublicStatus0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});


test('CheckFinalCertificatePublicStatus0 rejects stale linkage digest', async () => {
  const envelope = await makeFinalCertificatePublicStatus0();

  envelope.Linkage = {
    ...envelope.Linkage,
    publicStatusDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckFinalCertificatePublicStatus0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckFinalCertificatePublicStatus0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'publicStatusDigest']);
});

test('writeFinalCertificatePublicStatusFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-final-certificate-public-status-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeFinalCertificatePublicStatusFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.publicStatusPath,
    result.files.certificatePath,
    result.files.finalVerdictPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

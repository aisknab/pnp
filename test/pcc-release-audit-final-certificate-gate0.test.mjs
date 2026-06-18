import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckReleaseAuditFinalCertificateGate0,
  makeReleaseAuditFinalCertificateGate0,
  writeReleaseAuditFinalCertificateGateFiles0,
} from '../pcc-release-audit-final-certificate-gate0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

function makeAcceptedReleaseAuditRecord0(overrides = {}) {
  const nf = {
    kind: 'ReleaseAudit0NF',
    checker: 'CheckReleaseAudit0',
    version: 0,
    rootDir: '/materialized/test',
    moduleCount: 0,
    testCount: 0,
    requiredExports: [],
    requiredScripts: [],
    checkerCoverageCount: 0,
    publicSurfaceFreeze: true,
    publicSurfaceFreezeDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '1111111111111111111111111111111111111111111111111111111111111111',
    },
    materializedPublicStatusGate: true,
    materializedPublicStatusGateDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '2222222222222222222222222222222222222222222222222222222222222222',
    },
    materializedPublicStatusGateAcceptedPublicConclusionOnly: true,
    publicConclusion: {
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
      conditional: true,
    },
    ...overrides,
  };

  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker: 'CheckReleaseAudit0',
    version: 0,
    NF: nf,
    Digest: digest,
    Ledger: [],
    nf,
    digest,
    ledger: [],
  };
}

test('CheckReleaseAuditFinalCertificateGate0 accepts attached release audit plus final certificate public status', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  const out = await CheckReleaseAuditFinalCertificateGate0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAuditFinalCertificateGate0');
  assert.equal(out.NF.kind, 'ReleaseAuditFinalCertificateGate0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.releaseAuditAttached, true);
  assert.deepEqual(out.NF.releaseAuditDigest, releaseAuditRecord.Digest);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckReleaseAuditFinalCertificateGate0 rejects a non-accepted release audit record', async () => {
  const releaseAuditRecord = {
    ...makeAcceptedReleaseAuditRecord0(),
    tag: 'reject',
  };

  const envelope = await makeReleaseAuditFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  const out = await CheckReleaseAuditFinalCertificateGate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditFinalCertificateGate0.ReleaseAuditRecord');
  assert.deepEqual(out.Path, ['ReleaseAuditRecord', 'tag']);
});

test('CheckReleaseAuditFinalCertificateGate0 rejects public conclusion drift between release audit and certificate', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0({
    publicConclusion: {
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P != NP',
      conditional: true,
    },
  });

  releaseAuditRecord.Digest = digestCanonical0(releaseAuditRecord.NF);
  releaseAuditRecord.digest = releaseAuditRecord.Digest;

  const envelope = await makeReleaseAuditFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  const out = await CheckReleaseAuditFinalCertificateGate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, ['ReleaseAuditRecord', 'NF', 'publicConclusion']);
});

test('CheckReleaseAuditFinalCertificateGate0 rejects a stale public-status release audit digest', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.FinalCertificatePublicStatusEnvelope = {
    ...envelope.FinalCertificatePublicStatusEnvelope,
    PublicStatus: {
      ...envelope.FinalCertificatePublicStatusEnvelope.PublicStatus,
      releaseAuditDigest: {
        alg: 'SHA256',
        bytes: 'canonical-json-v0',
        hex: '0000000000000000000000000000000000000000000000000000000000000000',
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    finalCertificatePublicStatusDigest: undefined,
    publicStatusDigest: undefined,
  };

  const out = await CheckReleaseAuditFinalCertificateGate0(envelope, {
    checkFinalCertificatePublicStatus: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, ['FinalCertificatePublicStatusEnvelope', 'PublicStatus', 'releaseAuditDigest']);
});

test('CheckReleaseAuditFinalCertificateGate0 rejects forbidden fixture marker text', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
    overrides: {
      GateNote: 'todo marker must reject',
    },
  });

  const out = await CheckReleaseAuditFinalCertificateGate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditFinalCertificateGate0.fixtureMarkers');
});


test('CheckReleaseAuditFinalCertificateGate0 strictly rejects an injected synthetic scaffold marker', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
    overrides: {
      GateNote: 'synthetic marker must reject in strict marker mode',
    },
  });

  const out = await CheckReleaseAuditFinalCertificateGate0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditFinalCertificateGate0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});


test('CheckReleaseAuditFinalCertificateGate0 rejects stale linkage digest', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    releaseAuditDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckReleaseAuditFinalCertificateGate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditFinalCertificateGate0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'releaseAuditDigest']);
});

test('writeReleaseAuditFinalCertificateGateFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-release-audit-final-certificate-gate-'));
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeReleaseAuditFinalCertificateGateFiles0(dir, {
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.releaseAuditPath,
    result.files.finalCertificatePublicStatusPath,
    result.files.publicStatusPath,
    result.files.certificatePath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckReleaseAuditConcreteFinalCertificateGate0,
  makeReleaseAuditConcreteFinalCertificateGate0,
  writeReleaseAuditConcreteFinalCertificateGateFiles0,
} from '../pcc-release-audit-final-certificate-concrete-gate0.mjs';

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
    finalCertificatePublicStatusGate: true,
    finalCertificatePublicStatusGateDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '3333333333333333333333333333333333333333333333333333333333333333',
    },
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

test('CheckReleaseAuditConcreteFinalCertificateGate0 accepts attached release audit plus concrete public status', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.NF.kind, 'ReleaseAuditConcreteFinalCertificateGate0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.releaseAuditAttached, true);
  assert.deepEqual(out.NF.releaseAuditDigest, releaseAuditRecord.Digest);

  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteGlobalFirewalls, true);
  assert.equal(out.NF.concreteGlobalProofDAG, true);
  assert.equal(out.NF.finalCertificateUsesConcreteAcceptRun, true);
  assert.equal(out.NF.statusUsesConcreteFinalCertificate, true);

  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects a non-accepted release audit record', async () => {
  const releaseAuditRecord = {
    ...makeAcceptedReleaseAuditRecord0(),
    tag: 'reject',
  };

  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.ReleaseAuditRecord');
  assert.deepEqual(out.Path, ['ReleaseAuditRecord', 'tag']);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects public conclusion drift', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0({
    publicConclusion: {
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P != NP',
      conditional: true,
    },
  });

  releaseAuditRecord.Digest = digestCanonical0(releaseAuditRecord.NF);
  releaseAuditRecord.digest = releaseAuditRecord.Digest;

  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, ['ReleaseAuditRecord', 'NF', 'publicConclusion']);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects stale public-status release audit digest', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.ConcreteFinalCertificatePublicStatusEnvelope = {
    ...envelope.ConcreteFinalCertificatePublicStatusEnvelope,
    FinalCertificatePublicStatusEnvelope: {
      ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.FinalCertificatePublicStatusEnvelope,
      PublicStatus: {
        ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.FinalCertificatePublicStatusEnvelope.PublicStatus,
        releaseAuditDigest: {
          alg: 'SHA256',
          bytes: 'canonical-json-v0',
          hex: '0000000000000000000000000000000000000000000000000000000000000000',
        },
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concretePublicStatusEnvelopeDigest: undefined,
    publicStatusDigest: undefined,
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, ['ConcreteFinalCertificatePublicStatusEnvelope', 'PublicStatus', 'releaseAuditDigest']);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects forbidden fixture marker text', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
    overrides: {
      GateNote: 'todo marker must reject',
    },
  });

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.fixtureMarkers');
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 strictly rejects an injected synthetic scaffold marker', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
    overrides: {
      GateNote: 'synthetic marker must reject in strict marker mode',
    },
  });

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects stale linkage digest', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    pccPackDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'pccPackDigest']);
});

test('writeReleaseAuditConcreteFinalCertificateGateFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-release-audit-concrete-final-certificate-gate-'));
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeReleaseAuditConcreteFinalCertificateGateFiles0(dir, {
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.releaseAuditPath,
    result.files.concretePublicStatusPath,
    result.files.publicStatusPath,
    result.files.concreteFinalCertificatePath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

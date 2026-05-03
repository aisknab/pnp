import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteReleaseAppendix0,
  makeConcreteReleaseAppendix0,
  writeConcreteReleaseAppendixFiles0,
} from '../pcc-concrete-release-appendix0.mjs';

import {
  makeReleaseAuditConcreteFinalCertificateGate0,
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
    materializedPublicStatusGate: true,
    finalCertificatePublicStatusGate: true,
    concreteFinalCertificatePublicStatusGate: true,
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

async function makeGate0() {
  return makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: makeAcceptedReleaseAuditRecord0(),
    runReleaseAudit: false,
  });
}

test('CheckConcreteReleaseAppendix0 accepts the concrete release appendix', async () => {
  const gate = await makeGate0();
  const envelope = await makeConcreteReleaseAppendix0({
    ReleaseAuditConcreteFinalCertificateGateEnvelope: gate,
  });

  const out = await CheckConcreteReleaseAppendix0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteReleaseAppendix0');
  assert.equal(out.NF.kind, 'ConcreteReleaseAppendix0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.status, 'accepted');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.releaseAuditAttached, true);

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

test('CheckConcreteReleaseAppendix0 rejects public conclusion drift in the appendix', async () => {
  const gate = await makeGate0();
  const envelope = await makeConcreteReleaseAppendix0({
    ReleaseAuditConcreteFinalCertificateGateEnvelope: gate,
  });

  envelope.Appendix = {
    ...envelope.Appendix,
    publicConclusion: {
      ...envelope.Appendix.publicConclusion,
      consequent: 'P != NP',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    appendixDigest: undefined,
  };

  const out = await CheckConcreteReleaseAppendix0(envelope, {
    checkConcreteReleaseGate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteReleaseAppendix0');
  assert.equal(out.Coord, 'CheckConcreteReleaseAppendix0.appendix');
  assert.deepEqual(out.Path, ['Appendix']);
});

test('CheckConcreteReleaseAppendix0 rejects stale appendix package digest', async () => {
  const gate = await makeGate0();
  const envelope = await makeConcreteReleaseAppendix0({
    ReleaseAuditConcreteFinalCertificateGateEnvelope: gate,
  });

  envelope.Appendix = {
    ...envelope.Appendix,
    pccPackDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    appendixDigest: undefined,
  };

  const out = await CheckConcreteReleaseAppendix0(envelope, {
    checkConcreteReleaseGate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteReleaseAppendix0');
  assert.equal(out.Coord, 'CheckConcreteReleaseAppendix0.appendix');
  assert.deepEqual(out.Path, ['Appendix']);
});

test('CheckConcreteReleaseAppendix0 rejects forbidden fixture marker text', async () => {
  const gate = await makeGate0();
  const envelope = await makeConcreteReleaseAppendix0({
    ReleaseAuditConcreteFinalCertificateGateEnvelope: gate,
    overrides: {
      AppendixNote: 'todo marker must reject',
    },
  });

  const out = await CheckConcreteReleaseAppendix0(envelope, {
    checkConcreteReleaseGate: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteReleaseAppendix0');
  assert.equal(out.Coord, 'CheckConcreteReleaseAppendix0.fixtureMarkers');
});

test('CheckConcreteReleaseAppendix0 rejects stale linkage digest', async () => {
  const gate = await makeGate0();
  const envelope = await makeConcreteReleaseAppendix0({
    ReleaseAuditConcreteFinalCertificateGateEnvelope: gate,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    pccPackDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckConcreteReleaseAppendix0(envelope, {
    checkConcreteReleaseGate: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteReleaseAppendix0');
  assert.equal(out.Coord, 'CheckConcreteReleaseAppendix0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'pccPackDigest']);
});

test('writeConcreteReleaseAppendixFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-release-appendix-'));
  const gate = await makeGate0();

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteReleaseAppendixFiles0(dir, {
    ReleaseAuditConcreteFinalCertificateGateEnvelope: gate,
  });

  assert.equal(result.checked.tag, 'accept');
  assert.equal(result.gateCheck.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.appendixPath,
    result.files.gatePath,
    result.files.publicStatusPath,
    result.files.certificatePath,
    result.files.releaseAuditPath,
    result.files.gateCheckPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('CheckConcreteReleaseAppendix0 reports concrete HardCheck coverage in the appendix', async () => {
  const gate = await makeGate0();
  const envelope = await makeConcreteReleaseAppendix0({
    ReleaseAuditConcreteFinalCertificateGateEnvelope: gate,
  });

  const out = await CheckConcreteReleaseAppendix0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.hardEnvelopeKind, 'ConcreteMaterializedHardCheck0');
  assert.equal(out.NF.concreteHardCheck, true);
  assert.equal(out.NF.hardCheckerCoverageComplete, true);
  assert.equal(out.NF.hardRowKeyCoverageComplete, true);
  assert.equal(out.NF.hardRoutePriorityComplete, true);
  assert.equal(out.NF.hardProofRefPolicyComplete, true);
  assert.equal(out.NF.hardHashDisciplineComplete, true);
  assert.equal(out.NF.hardNoMinCoverageComplete, true);
  assert.equal(out.NF.hardImportPolicyComplete, true);
  assert.equal(out.NF.hardReflectionPolicyComplete, true);
  assert.equal(out.NF.hardBoundsPolicyComplete, true);
  assert.equal(out.NF.hardDiagnosticsPolicyComplete, true);
  assert.match(out.NF.hardCoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.hardCheckDigest.hex, /^[0-9a-f]{64}$/);
});

test('CheckConcreteReleaseAppendix0 rejects appendix without concrete HardCheck no-min coverage', async () => {
  const gate = await makeGate0();

  gate.ConcreteFinalCertificatePublicStatusEnvelope
    .ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .GeneratedAcceptRunEnvelope
    .MaterializedPCCPack
    .HardEnvelope
    .Coverage = {
      ...gate.ConcreteFinalCertificatePublicStatusEnvelope
        .ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .GeneratedAcceptRunEnvelope
        .MaterializedPCCPack
        .HardEnvelope
        .Coverage,
      noMinCoverageComplete: false,
    };

  const envelope = await makeConcreteReleaseAppendix0({
    ReleaseAuditConcreteFinalCertificateGateEnvelope: gate,
  });

  const out = await CheckConcreteReleaseAppendix0(envelope, {
    checkConcreteReleaseGate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteReleaseAppendix0');
  assert.equal(out.Coord, 'CheckConcreteReleaseAppendix0.appendix');
  assert.deepEqual(out.Path, ['Appendix', 'hardNoMinCoverageComplete']);
});

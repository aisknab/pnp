import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckFinalPNPReleaseGate0,
  FINAL_PNP_RELEASE_GATE_PHASES0,
  makeFinalPNPReleaseGate0,
  writeFinalPNPReleaseGateFiles0,
} from '../pcc-final-pnp-release-gate0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

test('CheckFinalPNPReleaseGate0 accepts the final P=NP release gate', async () => {
  const envelope = await makeFinalPNPReleaseGate0();
  const out = await CheckFinalPNPReleaseGate0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinalPNPReleaseGate0');
  assert.equal(out.NF.kind, 'FinalPNPReleaseGate0NF');
  assert.deepEqual(out.NF.phaseOrder, FINAL_PNP_RELEASE_GATE_PHASES0);

  assert.equal(out.NF.finalPNPReleaseGateAccepted, true);
  assert.equal(out.NF.finalPNPCertificateAccepted, true);
  assert.equal(out.NF.releaseAuditAccepted, true);
  assert.equal(out.NF.finalAcceptanceReplayClosed, true);

  assert.equal(out.NF.status, 'accepted');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.theorem.statement, 'P = NP');
  assert.equal(out.NF.theorem.antecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.NF.theorem.consequent, 'P = NP');
  assert.equal(out.NF.theorem.conditional, true);

  assert.equal(out.NF.generator, 'GeneratePCCPack');
  assert.equal(out.NF.checkerName, 'CheckPCCPackexp0');
  assert.equal(out.NF.generatorIsGeneratePCCPack, true);
  assert.equal(out.NF.checkPCCPackexpAccepted, true);
  assert.equal(out.NF.checkAcceptRunAccepted, true);
  assert.equal(out.NF.replayAccepted, true);
  assert.equal(out.NF.finalVerdictAccepted, true);

  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusionAntecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.NF.publicConclusionConsequent, 'P = NP');
  assert.equal(out.NF.publicConclusionConditional, true);

  assert.equal(out.NF.checkPCCPackexpGeneratedPackageImplication, true);
  assert.equal(out.NF.checkPCCPackexpConcreteCoverageComplete, true);
  assert.equal(out.NF.checkPCCPackexpPCCPackLinkageComplete, true);

  assert.match(out.NF.releaseAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.finalPNPCertificateEnvelopeDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.checkFinalPNPCertificateRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.certificateDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.acceptRunDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.pccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.acceptanceTranscriptDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.finalVerdictRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.checkPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckFinalPNPReleaseGate0 rejects a stale final PNP certificate record', async () => {
  const envelope = await makeFinalPNPReleaseGate0();

  const nf = {
    ...envelope.CheckFinalPNPCertificateRecord.NF,
    finalPNPCertificateAccepted: false,
  };

  envelope.CheckFinalPNPCertificateRecord = {
    ...envelope.CheckFinalPNPCertificateRecord,
    NF: nf,
    nf,
    Digest: digestCanonical0(nf),
    digest: digestCanonical0(nf),
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    checkFinalPNPCertificateRecordDigest: undefined,
  };

  const out = await CheckFinalPNPReleaseGate0(envelope, {
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalPNPReleaseGate0');
  assert.equal(out.Coord, 'CheckFinalPNPReleaseGate0.CheckFinalPNPCertificateRecord');
  assert.deepEqual(out.Path, ['CheckFinalPNPCertificateRecord']);
});

test('CheckFinalPNPReleaseGate0 rejects release-audit digest drift in certificate', async () => {
  const envelope = await makeFinalPNPReleaseGate0();

  envelope.FinalPNPCertificateEnvelope.Certificate = {
    ...envelope.FinalPNPCertificateEnvelope.Certificate,
    releaseAuditDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    certificateDigest: undefined,
  };

  const out = await CheckFinalPNPReleaseGate0(envelope, {
    checkFinalPNPCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalPNPReleaseGate0');
  assert.equal(out.Coord, 'CheckFinalPNPReleaseGate0.contract');
  assert.deepEqual(out.Path, [
    'FinalPNPCertificateEnvelope',
    'Certificate',
    'releaseAuditDigest',
  ]);
});

test('CheckFinalPNPReleaseGate0 rejects theorem drift', async () => {
  const envelope = await makeFinalPNPReleaseGate0();

  envelope.FinalPNPCertificateEnvelope.Certificate = {
    ...envelope.FinalPNPCertificateEnvelope.Certificate,
    theorem: {
      ...envelope.FinalPNPCertificateEnvelope.Certificate.theorem,
      consequent: 'P != NP',
    },
  };

  const out = await CheckFinalPNPReleaseGate0(envelope, {
    checkFinalPNPCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalPNPReleaseGate0');
  assert.equal(out.Coord, 'CheckFinalPNPReleaseGate0.contract');
  assert.deepEqual(out.Path, [
    'FinalPNPCertificateEnvelope',
    'Certificate',
    'theorem',
  ]);
});

test('writeFinalPNPReleaseGateFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-final-pnp-release-gate-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeFinalPNPReleaseGateFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.certificateEnvelopePath,
    result.files.certificateRecordPath,
    result.files.releaseAuditPath,
    result.files.certificatePath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

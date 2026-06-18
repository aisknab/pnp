import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckFinalPNPCertificate0,
  FINAL_PNP_CERTIFICATE_PHASES0,
  makeFinalPNPCertificate0,
  writeFinalPNPCertificateFiles0,
} from '../pcc-final-pnp-certificate0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

test('CheckFinalPNPCertificate0 accepts the final P=NP certificate appendix', async () => {
  const envelope = await makeFinalPNPCertificate0();
  const out = await CheckFinalPNPCertificate0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinalPNPCertificate0');
  assert.equal(out.NF.kind, 'FinalPNPCertificate0NF');
  assert.deepEqual(out.NF.phaseOrder, FINAL_PNP_CERTIFICATE_PHASES0);

  assert.equal(out.NF.finalPNPCertificateAccepted, true);
  assert.equal(out.NF.status, 'accepted');
  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.theorem.statement, 'P = NP');
  assert.equal(out.NF.theorem.antecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.NF.theorem.consequent, 'P = NP');
  assert.equal(out.NF.theorem.conditional, true);

  assert.equal(out.NF.finalAcceptanceReplayClosed, true);
  assert.equal(out.NF.generatorIsGeneratePCCPack, true);
  assert.equal(out.NF.checkAcceptRunAccepted, true);
  assert.equal(out.NF.replayAccepted, true);
  assert.equal(out.NF.finalVerdictAccepted, true);
  assert.equal(out.NF.checkPCCPackexpAccepted, true);

  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusionAntecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.NF.publicConclusionConsequent, 'P = NP');
  assert.equal(out.NF.publicConclusionConditional, true);

  assert.equal(out.NF.checkPCCPackexpGeneratedPackageImplication, true);
  assert.equal(out.NF.checkPCCPackexpConcreteCoverageComplete, true);
  assert.equal(out.NF.checkPCCPackexpPCCPackLinkageComplete, true);

  assert.match(out.NF.releaseAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concreteFinalAcceptanceReplayEnvelopeDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concreteFinalAcceptanceReplayRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.acceptRunDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.pccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.acceptanceTranscriptDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.finalVerdictRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.checkPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.certificateDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckFinalPNPCertificate0 rejects theorem drift', async () => {
  const envelope = await makeFinalPNPCertificate0();

  envelope.Certificate = {
    ...envelope.Certificate,
    theorem: {
      ...envelope.Certificate.theorem,
      consequent: 'P != NP',
    },
    publicConclusionConsequent: 'P != NP',
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    certificateDigest: undefined,
  };

  const out = await CheckFinalPNPCertificate0(envelope, {
    checkConcreteFinalAcceptanceReplay: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalPNPCertificate0');
  assert.equal(out.Coord, 'CheckFinalPNPCertificate0.certificate');
  assert.deepEqual(out.Path, ['Certificate']);
});

test('CheckFinalPNPCertificate0 rejects stale final acceptance replay record evidence', async () => {
  const envelope = await makeFinalPNPCertificate0();

  const nf = {
    ...envelope.CheckConcreteFinalAcceptanceReplayRecord.NF,
    checkPCCPackexpAccepted: false,
  };

  envelope.CheckConcreteFinalAcceptanceReplayRecord = {
    ...envelope.CheckConcreteFinalAcceptanceReplayRecord,
    NF: nf,
    nf,
    Digest: digestCanonical0(nf),
    digest: digestCanonical0(nf),
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteFinalAcceptanceReplayRecordDigest: undefined,
  };

  const out = await CheckFinalPNPCertificate0(envelope, {
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalPNPCertificate0');
  assert.equal(out.Coord, 'CheckFinalPNPCertificate0.CheckConcreteFinalAcceptanceReplayRecord');
  assert.deepEqual(out.Path, ['CheckConcreteFinalAcceptanceReplayRecord']);
});

test('CheckFinalPNPCertificate0 rejects stale certificate linkage', async () => {
  const envelope = await makeFinalPNPCertificate0();

  envelope.Linkage = {
    ...envelope.Linkage,
    certificateDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckFinalPNPCertificate0(envelope, {
    checkConcreteFinalAcceptanceReplay: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalPNPCertificate0');
  assert.equal(out.Coord, 'CheckFinalPNPCertificate0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'certificateDigest']);
});

test('writeFinalPNPCertificateFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-final-pnp-certificate-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeFinalPNPCertificateFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.certificatePath,
    result.files.replayPath,
    result.files.replayCheckPath,
    result.files.appendixPath,
    result.files.finalVerdictPath,
    result.files.checkPCCPackexpPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

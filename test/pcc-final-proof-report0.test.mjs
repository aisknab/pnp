import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckFinalPNPProofReport0,
  FINAL_PNP_PROOF_REPORT_PHASES0,
  makeFinalPNPProofReport0,
  writeFinalPNPProofReportFiles0,
} from '../pcc-final-proof-report0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

test('CheckFinalPNPProofReport0 accepts the final P=NP proof report', async () => {
  const envelope = await makeFinalPNPProofReport0();
  const out = await CheckFinalPNPProofReport0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinalPNPProofReport0');
  assert.equal(out.NF.kind, 'FinalPNPProofReport0NF');
  assert.deepEqual(out.NF.phaseOrder, FINAL_PNP_PROOF_REPORT_PHASES0);

  assert.equal(out.NF.finalPNPProofReportAccepted, true);
  assert.equal(out.NF.status, 'accepted');
  assert.equal(out.NF.theorem.statement, 'P = NP');
  assert.equal(out.NF.theorem.antecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.NF.theorem.consequent, 'P = NP');
  assert.equal(out.NF.theorem.conditional, true);

  assert.equal(out.NF.finalPNPReleaseGateAccepted, true);
  assert.equal(out.NF.finalPNPCertificateAccepted, true);
  assert.equal(out.NF.releaseAuditAccepted, true);
  assert.equal(out.NF.finalAcceptanceReplayClosed, true);
  assert.equal(out.NF.generator, 'GeneratePCCPack');
  assert.equal(out.NF.checkerName, 'CheckPCCPackexp0');

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
  assert.equal(out.NF.publicTheoremStatement, 'P = NP');
  assert.equal(out.NF.publicConclusionStatement, 'CheckPCCPackexp(GeneratePCCPack())=accept => P = NP');

  assert.match(out.NF.finalPNPReleaseGateEnvelopeDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.finalPNPReleaseGateRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.releaseAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.certificateDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.acceptRunDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.pccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.acceptanceTranscriptDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.finalVerdictRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.checkPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.reportDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckFinalPNPProofReport0 rejects stale final release-gate record evidence', async () => {
  const envelope = await makeFinalPNPProofReport0();

  const nf = {
    ...envelope.CheckFinalPNPReleaseGateRecord.NF,
    finalPNPReleaseGateAccepted: false,
  };

  envelope.CheckFinalPNPReleaseGateRecord = {
    ...envelope.CheckFinalPNPReleaseGateRecord,
    NF: nf,
    nf,
    Digest: digestCanonical0(nf),
    digest: digestCanonical0(nf),
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    finalPNPReleaseGateRecordDigest: undefined,
  };

  const out = await CheckFinalPNPProofReport0(envelope, {
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalPNPProofReport0');
  assert.equal(out.Coord, 'CheckFinalPNPProofReport0.CheckFinalPNPReleaseGateRecord');
  assert.deepEqual(out.Path, ['CheckFinalPNPReleaseGateRecord']);
});

test('CheckFinalPNPProofReport0 rejects theorem drift', async () => {
  const envelope = await makeFinalPNPProofReport0();

  envelope.Report = {
    ...envelope.Report,
    theorem: {
      ...envelope.Report.theorem,
      consequent: 'P != NP',
    },
    publicConclusionConsequent: 'P != NP',
    publicTheoremStatement: 'P != NP',
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    reportDigest: undefined,
  };

  const out = await CheckFinalPNPProofReport0(envelope, {
    checkFinalPNPReleaseGate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalPNPProofReport0');
  assert.equal(out.Coord, 'CheckFinalPNPProofReport0.report');
  assert.deepEqual(out.Path, ['Report']);
});

test('CheckFinalPNPProofReport0 rejects stale report linkage', async () => {
  const envelope = await makeFinalPNPProofReport0();

  envelope.Linkage = {
    ...envelope.Linkage,
    reportDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckFinalPNPProofReport0(envelope, {
    checkFinalPNPReleaseGate: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckFinalPNPProofReport0');
  assert.equal(out.Coord, 'CheckFinalPNPProofReport0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'reportDigest']);
});

test('writeFinalPNPProofReportFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-final-pnp-proof-report-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeFinalPNPProofReportFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.reportPath,
    result.files.releaseGatePath,
    result.files.releaseGateCheckPath,
    result.files.certificatePath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

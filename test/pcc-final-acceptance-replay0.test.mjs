import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteFinalAcceptanceReplay0,
  CONCRETE_FINAL_ACCEPTANCE_REPLAY_PHASES0,
  makeConcreteFinalAcceptanceReplay0,
  writeConcreteFinalAcceptanceReplayFiles0,
} from '../pcc-final-acceptance-replay0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

test('CheckConcreteFinalAcceptanceReplay0 accepts the concrete final acceptance replay closure', async () => {
  const envelope = await makeConcreteFinalAcceptanceReplay0();
  const out = await CheckConcreteFinalAcceptanceReplay0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteFinalAcceptanceReplay0');
  assert.equal(out.NF.kind, 'ConcreteFinalAcceptanceReplay0NF');
  assert.deepEqual(out.NF.phaseOrder, CONCRETE_FINAL_ACCEPTANCE_REPLAY_PHASES0);

  assert.equal(out.NF.finalAcceptanceReplayClosed, true);
  assert.equal(out.NF.generatorIsGeneratePCCPack, true);
  assert.equal(out.NF.checkAcceptRunAccepted, true);
  assert.equal(out.NF.replayAccepted, true);
  assert.equal(out.NF.finalVerdictAccepted, true);
  assert.equal(out.NF.checkPCCPackexpAccepted, true);

  assert.equal(out.NF.verdict, 'accept');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusionAntecedent, 'CheckPCCPackexp(GeneratePCCPack())=accept');
  assert.equal(out.NF.publicConclusionConsequent, 'P = NP');
  assert.equal(out.NF.publicConclusionConditional, true);

  assert.equal(out.NF.generatedPackageCanonicalCoreBytesMatch, true);
  assert.equal(out.NF.generatedPackageCanonicalPackBytesMatch, true);
  assert.equal(out.NF.acceptRunGenCallCoreBytesMatch, true);
  assert.equal(out.NF.acceptRunGenCallPackBytesMatch, true);
  assert.equal(out.NF.checkPCCPackexpGeneratedPackageImplication, true);
  assert.equal(out.NF.checkPCCPackexpConcreteCoverageComplete, true);
  assert.equal(out.NF.checkPCCPackexpPCCPackLinkageComplete, true);
  assert.equal(out.NF.appendixCarriesCheckPCCPackexpContract, true);

  assert.match(out.NF.acceptRunDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.pccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPackageDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.checkAcceptRunRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.replayRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.finalVerdictRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.checkPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckConcreteFinalAcceptanceReplay0 rejects stale replay record evidence', async () => {
  const envelope = await makeConcreteFinalAcceptanceReplay0();

  const nf = {
    ...envelope.ReplayAcceptRunRecord.NF,
    runId: 'stale-replay-run-id',
  };

  envelope.ReplayAcceptRunRecord = {
    ...envelope.ReplayAcceptRunRecord,
    NF: nf,
    nf,
    Digest: digestCanonical0(nf),
    digest: digestCanonical0(nf),
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    replayRecordDigest: undefined,
  };

  const out = await CheckConcreteFinalAcceptanceReplay0(envelope, {
    checkConcreteReleaseAppendix: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalAcceptanceReplay0');
  assert.equal(out.Coord, 'CheckConcreteFinalAcceptanceReplay0.ReplayAcceptRunRecord');
  assert.deepEqual(out.Path, ['ReplayAcceptRunRecord']);
});

test('CheckConcreteFinalAcceptanceReplay0 rejects appendix without generated package implication evidence', async () => {
  const envelope = await makeConcreteFinalAcceptanceReplay0();

  envelope.ConcreteReleaseAppendixEnvelope.Appendix = {
    ...envelope.ConcreteReleaseAppendixEnvelope.Appendix,
    generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication: false,
  };

  envelope.ConcreteReleaseAppendixEnvelope.Linkage = {
    ...envelope.ConcreteReleaseAppendixEnvelope.Linkage,
    appendixDigest: undefined,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteReleaseAppendixEnvelopeDigest: undefined,
    appendixDigest: undefined,
  };

  const out = await CheckConcreteFinalAcceptanceReplay0(envelope, {
    checkConcreteReleaseAppendix: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalAcceptanceReplay0');
  assert.equal(out.Coord, 'CheckConcreteFinalAcceptanceReplay0.contract');
  assert.deepEqual(out.Path, [
    'ConcreteReleaseAppendixEnvelope',
    'Appendix',
    'generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication',
  ]);
});

test('CheckConcreteFinalAcceptanceReplay0 rejects digest-only generator drift', async () => {
  const envelope = await makeConcreteFinalAcceptanceReplay0();

  const generatedAcceptRunEnvelope = envelope.ConcreteReleaseAppendixEnvelope
    .ReleaseAuditConcreteFinalCertificateGateEnvelope
    .ConcreteFinalCertificatePublicStatusEnvelope
    .ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .GeneratedAcceptRunEnvelope;

  generatedAcceptRunEnvelope.GeneratedPackage = {
    ...generatedAcceptRunEnvelope.GeneratedPackage,
    outputPackBytes: '{"not":"the canonical package bytes"}',
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedPackageDigest: undefined,
  };

  const out = await CheckConcreteFinalAcceptanceReplay0(envelope, {
    checkConcreteReleaseAppendix: false,
    checkAcceptRun: false,
    checkReplay: false,
    checkFinalVerdict: false,
    checkPCCPackexp: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalAcceptanceReplay0');
  assert.equal(out.Coord, 'CheckConcreteFinalAcceptanceReplay0.contract');
  assert.deepEqual(out.Path, ['AcceptRun', 'GenCall', 'generatedPackageCanonicalPackBytesMatch']);
});

test('writeConcreteFinalAcceptanceReplayFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-final-acceptance-replay-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteFinalAcceptanceReplayFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.appendixPath,
    result.files.acceptRunPath,
    result.files.checkAcceptRunPath,
    result.files.replayPath,
    result.files.finalVerdictPath,
    result.files.checkPCCPackexpPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

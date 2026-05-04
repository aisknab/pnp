import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteFinalCertificatePublicStatus0,
  makeConcreteFinalCertificatePublicStatus0,
  summarizeConcreteFinalCertificatePublicStatusChain0,
  writeConcreteFinalCertificatePublicStatusFiles0,
} from '../pcc-final-certificate-public-status-concrete0.mjs';

import {
  CheckFinalCertificatePublicStatus0,
} from '../pcc-final-certificate-public-status0.mjs';

test('CheckConcreteFinalCertificatePublicStatus0 accepts public status over concrete final certificate', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();
  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.NF.kind, 'ConcreteFinalCertificatePublicStatus0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteGlobalFirewalls, true);
  assert.equal(out.NF.concreteGlobalProofDAG, true);

  assert.equal(out.NF.concreteKBundle, true);
  assert.equal(out.NF.kBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.kBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.kBundleReflectionProofRefsResolve, true);

  assert.equal(out.NF.concreteHardCheck, true);
  assert.equal(out.NF.hardCheckerCoverageComplete, true);
  assert.equal(out.NF.hardNoMinCoverageComplete, true);
  assert.equal(out.NF.hardImportPolicyComplete, true);

  assert.equal(out.NF.concreteFinalIntegration, true);
  assert.equal(out.NF.finalIntegrationConcreteGlobalProofDAG, true);
  assert.equal(out.NF.finalIntegrationGPackFieldCoverageComplete, true);
  assert.equal(out.NF.finalIntegrationRowFamGCoverageComplete, true);

  assert.equal(out.NF.concretePCCPack, true);
  assert.match(out.NF.concretePCCPackCoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.pccPackPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(out.NF.pccPackLinkedToKBundle, true);
  assert.equal(out.NF.pccPackLinkedToHardCheck, true);
  assert.equal(out.NF.pccPackLinkedToRows, true);
  assert.equal(out.NF.pccPackLinkedToLocalPackages, true);
  assert.equal(out.NF.pccPackLinkedToGlobalFirewalls, true);
  assert.equal(out.NF.pccPackLinkedToGlobalProofDAG, true);
  assert.equal(out.NF.pccPackLinkedToGPack, true);
  assert.equal(out.NF.pccPackLinkedToFinalIntegration, true);
  assert.equal(out.NF.pccPackLinkedToFinalTheorem, true);

  assert.equal(out.NF.checkPCCPackexpRecordPresent, true);
  assert.equal(out.NF.checkPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.checkPCCPackexpRecordChecker, 'CheckPCCPackexp0');
  assert.match(out.NF.checkPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.checkPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(out.NF.checkPCCPackexpRecordConcretePCCPack, true);
  assert.match(out.NF.checkPCCPackexpRecordPccPackDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.checkPCCPackexpRecordPccPackDigestMatchesConcreteRun, true);
  assert.equal(out.NF.checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun, true);
  assert.equal(out.NF.checkPCCPackexpRecordPublicConclusionNotEmitted, true);
  assert.equal(out.NF.checkPCCPackexpRecordClaimBoundaryConditional, true);

  assert.equal(out.NF.generatedPCCPackexpEnvelopePresent, true);
  assert.match(out.NF.generatedPCCPackexpEnvelopeDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpGenCallGeneratePCCPack, true);
  assert.equal(out.NF.generatedPCCPackexpCoreOnly, true);
  assert.equal(out.NF.generatedPCCPackexpExcludesAcceptRun, true);
  assert.equal(out.NF.generatedPCCPackexpPackageMatchesConcreteRun, true);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordMatchesConcreteRun, true);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordAccepted, true);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordChecker, 'CheckPCCPackexp0');
  assert.match(out.NF.generatedPCCPackexpCheckRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordDigestMatchesNF, true);
  assert.equal(out.NF.generatedPCCPackexpCheckRecordClaimBoundaryConditional, true);
  assert.equal(out.NF.generatedPCCPackexpLinkageGeneratedPackageDigestMatches, true);
  assert.equal(out.NF.generatedPCCPackexpLinkageCheckRecordDigestMatches, true);

  assert.equal(out.NF.checkGeneratedPCCPackexpRecordPresent, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordAccepted, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordChecker, 'CheckGeneratedPCCPackexp0');
  assert.match(out.NF.checkGeneratedPCCPackexpRecordDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordDigestMatchesNF, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope, true);
  assert.equal(out.NF.checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope, true);

  assert.equal(out.NF.generatedPCCPackexpBoot0, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0Kind, 'Boot0');
  assert.match(out.NF.generatedPCCPackexpBoot0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpBoot0CheckDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpBoot0CanonicalByteDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpBoot0RowCount > 0, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0KernelRuleCount > 0, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0JsonMaterialized, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0NoFixtureMarkers, true);
  assert.match(out.NF.generatedPCCPackexpBoot0BootBatchDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpBoot0BootAuditDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpBoot0LinkedToPCCPack, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0LinkedToCoreDigestMap, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0DigestMatchesGeneratedPackage, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0DigestMatchesCoreDigestMap, true);

  assert.equal(out.NF.statusUsesConcreteFinalCertificate, true);
  assert.equal(out.NF.publicStatusCertificateDigestMatchesConcrete, true);
  assert.equal(out.NF.publicStatusFinalVerdictDigestMatchesConcrete, true);
  assert.equal(out.NF.publicStatusAcceptRunDigestMatchesConcrete, true);
  assert.equal(out.NF.publicStatusPccPackDigestMatchesConcrete, true);
  assert.equal(out.NF.publicConclusionMatchesCertificate, true);
  assert.equal(out.NF.publicConclusionMatchesFinalVerdict, true);
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');

  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner final-certificate public-status checker accepts the concrete status envelope', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();
  const out = await CheckFinalCertificatePublicStatus0(envelope.FinalCertificatePublicStatusEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckFinalCertificatePublicStatus0');
  assert.equal(out.NF.kind, 'FinalCertificatePublicStatus0NF');
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects stale concrete public-status chain summary', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.ConcreteChain = {
    ...envelope.ConcreteChain,
    statusUsesConcreteFinalCertificate: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects status envelope not tied to concrete final certificate', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.FinalCertificatePublicStatusEnvelope = {
    ...envelope.FinalCertificatePublicStatusEnvelope,
    FinalCertificateEnvelope: {
      ...envelope.FinalCertificatePublicStatusEnvelope.FinalCertificateEnvelope,
      Certificate: {
        ...envelope.FinalCertificatePublicStatusEnvelope.FinalCertificateEnvelope.Certificate,
        status: 'drifted',
      },
    },
  };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    finalCertificatePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'statusUsesConcreteFinalCertificate']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects concrete PCCPack component drift', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .GeneratedAcceptRunEnvelope
    .MaterializedPCCPack
    .PCCPack = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .GeneratedAcceptRunEnvelope
        .MaterializedPCCPack
        .PCCPack,
      HardCheck: {
        ...envelope.ConcreteFinalCertificateEnvelope
          .ConcreteGeneratedAcceptRunEnvelope
          .GeneratedAcceptRunEnvelope
          .MaterializedPCCPack
          .PCCPack
          .HardCheck,
        DriftWitness: 'changed-hard-check',
      },
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'concretePCCPack']);
});

test('CheckConcreteFinalCertificatePublicStatus0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.FinalCertificatePublicStatusEnvelope = {
    ...envelope.FinalCertificatePublicStatusEnvelope,
    PublicStatus: {
      ...envelope.FinalCertificatePublicStatusEnvelope.PublicStatus,
      ScaffoldWitness: 'synthetic marker must reject in strict marker mode',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    finalCertificatePublicStatusEnvelopeDigest: undefined,
    publicStatusDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkFinalCertificatePublicStatus: false,
    checkConcreteChain: false,
    checkLinkage: false,
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteFinalCertificatePublicStatusFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-public-status-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteFinalCertificatePublicStatusFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.concreteFinalCertificatePath,
    result.files.finalCertificatePublicStatusPath,
    result.files.publicStatusPath,
    result.files.concreteChainPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects incomplete concrete HardCheck coverage', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .GeneratedAcceptRunEnvelope
    .MaterializedPCCPack
    .HardEnvelope
    .Coverage = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .GeneratedAcceptRunEnvelope
        .MaterializedPCCPack
        .HardEnvelope
        .Coverage,
      noMinCoverageComplete: false,
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'hardNoMinCoverageComplete']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects incomplete concrete final-integration coverage', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .GeneratedAcceptRunEnvelope
    .MaterializedPCCPack
    .FinalIntegrationEnvelope
    .ConcreteLinks = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .GeneratedAcceptRunEnvelope
        .MaterializedPCCPack
        .FinalIntegrationEnvelope
        .ConcreteLinks,
      rowFamGCoverageComplete: false,
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'finalIntegrationRowFamGCoverageComplete']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects missing materialized CheckPCCPackexp0 evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  delete envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckPCCPackexpRecord;

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .Linkage = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .Linkage,
      checkPCCPackexpRecordDigest: undefined,
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'checkPCCPackexpRecordPresent']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects missing GeneratedPCCPackexp0 evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  delete envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .GeneratedPCCPackexpEnvelope;

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .Linkage = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .Linkage,
      generatedPCCPackexpEnvelopeDigest: undefined,
      generatedPCCPackDigest: undefined,
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpEnvelopePresent']);
});

test('CheckConcreteFinalCertificatePublicStatus0 rejects missing CheckGeneratedPCCPackexp0 evidence', async () => {
  const envelope = await makeConcreteFinalCertificatePublicStatus0();

  delete envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .CheckGeneratedPCCPackexpRecord;

  envelope.ConcreteFinalCertificateEnvelope
    .ConcreteGeneratedAcceptRunEnvelope
    .Linkage = {
      ...envelope.ConcreteFinalCertificateEnvelope
        .ConcreteGeneratedAcceptRunEnvelope
        .Linkage,
      checkGeneratedPCCPackexpRecordDigest: undefined,
    };

  envelope.ConcreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteFinalCertificatePublicStatus0(envelope, {
    checkConcreteFinalCertificate: false,
    checkFinalCertificatePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteFinalCertificatePublicStatus0');
  assert.equal(out.Coord, 'CheckConcreteFinalCertificatePublicStatus0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'checkGeneratedPCCPackexpRecordPresent']);
});

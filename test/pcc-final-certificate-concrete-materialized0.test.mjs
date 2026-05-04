import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedFinalCertificate0,
  makeConcreteMaterializedFinalCertificate0,
  summarizeConcreteFinalCertificateChain0,
  writeConcreteMaterializedFinalCertificateFiles0,
} from '../pcc-final-certificate-concrete-materialized0.mjs';

import {
  CheckMaterializedFinalCertificate0,
} from '../pcc-final-certificate-materialized0.mjs';

test('CheckConcreteMaterializedFinalCertificate0 accepts a final certificate over the concrete accept-run chain', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();
  const out = await CheckConcreteMaterializedFinalCertificate0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedFinalCertificate0NF');
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

  assert.equal(out.NF.finalCertificateUsesConcreteAcceptRun, true);
  assert.equal(out.NF.certificatePccPackDigestMatchesConcreteRun, true);
  assert.equal(out.NF.certificateAcceptRunDigestMatchesConcreteRun, true);
  assert.equal(out.NF.certificateFinalVerdictDigestMatchesRecord, true);
  assert.equal(out.NF.publicTheoremMatchesAcceptedFinalVerdict, true);
  assert.equal(out.NF.publicTheorem.consequent, 'P = NP');

  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner materialized final certificate accepts the concrete-chain final certificate envelope', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();
  const out = await CheckMaterializedFinalCertificate0(envelope.FinalCertificateEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFinalCertificate0');
  assert.equal(out.NF.kind, 'MaterializedFinalCertificate0NF');
});

test('CheckConcreteMaterializedFinalCertificate0 rejects a non-concrete final-certificate chain summary', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  envelope.ConcreteChain = {
    ...envelope.ConcreteChain,
    concreteGlobalProofDAG: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkConcreteGeneratedAcceptRun: false,
    checkFinalCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain']);
});

test('CheckConcreteMaterializedFinalCertificate0 rejects final certificate accept-run drift', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  envelope.FinalCertificateEnvelope = {
    ...envelope.FinalCertificateEnvelope,
    GeneratedAcceptRunEnvelope: {
      ...envelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope,
      AcceptRun: {
        ...envelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope.AcceptRun,
        RunID: 'drifted-run-id',
      },
    },
  };

  envelope.ConcreteChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope: envelope.ConcreteGeneratedAcceptRunEnvelope,
    finalCertificateEnvelope: envelope.FinalCertificateEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    finalCertificateEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkFinalCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'finalCertificateUsesConcreteAcceptRun']);
});

test('CheckConcreteMaterializedFinalCertificate0 rejects concrete PCCPack component drift', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.PCCPack = {
    ...envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.PCCPack,
    HardCheck: {
      ...envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.PCCPack.HardCheck,
      DriftWitness: 'changed-hard-check',
    },
  };

  envelope.ConcreteChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope: envelope.ConcreteGeneratedAcceptRunEnvelope,
    finalCertificateEnvelope: envelope.FinalCertificateEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkConcreteGeneratedAcceptRun: false,
    checkFinalCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'concretePCCPack']);
});

test('CheckConcreteMaterializedFinalCertificate0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  envelope.FinalCertificateEnvelope = {
    ...envelope.FinalCertificateEnvelope,
    Certificate: {
      ...envelope.FinalCertificateEnvelope.Certificate,
      ScaffoldWitness: 'synthetic marker must reject in strict marker mode',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    finalCertificateEnvelopeDigest: undefined,
    finalCertificateDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkFinalCertificate: false,
    checkConcreteChain: false,
    checkLinkage: false,
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteMaterializedFinalCertificateFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-final-certificate-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedFinalCertificateFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.concreteAcceptRunPath,
    result.files.finalCertificateEnvelopePath,
    result.files.certificatePath,
    result.files.chainPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('CheckConcreteMaterializedFinalCertificate0 rejects incomplete concrete HardCheck coverage', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.HardEnvelope.Coverage = {
    ...envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.HardEnvelope.Coverage,
    noMinCoverageComplete: false,
  };

  envelope.ConcreteChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope: envelope.ConcreteGeneratedAcceptRunEnvelope,
    finalCertificateEnvelope: envelope.FinalCertificateEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkConcreteGeneratedAcceptRun: false,
    checkFinalCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'hardNoMinCoverageComplete']);
});

test('CheckConcreteMaterializedFinalCertificate0 rejects incomplete concrete final-integration coverage', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.FinalIntegrationEnvelope.ConcreteLinks = {
    ...envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.FinalIntegrationEnvelope.ConcreteLinks,
    rowFamGCoverageComplete: false,
  };

  envelope.ConcreteChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope: envelope.ConcreteGeneratedAcceptRunEnvelope,
    finalCertificateEnvelope: envelope.FinalCertificateEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkConcreteGeneratedAcceptRun: false,
    checkFinalCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'finalIntegrationRowFamGCoverageComplete']);
});

test('CheckConcreteMaterializedFinalCertificate0 rejects missing materialized CheckPCCPackexp0 evidence', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  delete envelope.ConcreteGeneratedAcceptRunEnvelope.CheckPCCPackexpRecord;

  envelope.ConcreteGeneratedAcceptRunEnvelope.Linkage = {
    ...envelope.ConcreteGeneratedAcceptRunEnvelope.Linkage,
    checkPCCPackexpRecordDigest: undefined,
  };

  envelope.ConcreteChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope: envelope.ConcreteGeneratedAcceptRunEnvelope,
    finalCertificateEnvelope: envelope.FinalCertificateEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkConcreteGeneratedAcceptRun: false,
    checkFinalCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'checkPCCPackexpRecordPresent']);
});

test('CheckConcreteMaterializedFinalCertificate0 rejects missing GeneratedPCCPackexp0 evidence', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  delete envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedPCCPackexpEnvelope;

  envelope.ConcreteGeneratedAcceptRunEnvelope.Linkage = {
    ...envelope.ConcreteGeneratedAcceptRunEnvelope.Linkage,
    generatedPCCPackexpEnvelopeDigest: undefined,
    generatedPCCPackDigest: undefined,
  };

  envelope.ConcreteChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope: envelope.ConcreteGeneratedAcceptRunEnvelope,
    finalCertificateEnvelope: envelope.FinalCertificateEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkConcreteGeneratedAcceptRun: false,
    checkFinalCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'generatedPCCPackexpEnvelopePresent']);
});

test('CheckConcreteMaterializedFinalCertificate0 rejects missing CheckGeneratedPCCPackexp0 evidence', async () => {
  const envelope = await makeConcreteMaterializedFinalCertificate0();

  delete envelope.ConcreteGeneratedAcceptRunEnvelope.CheckGeneratedPCCPackexpRecord;

  envelope.ConcreteGeneratedAcceptRunEnvelope.Linkage = {
    ...envelope.ConcreteGeneratedAcceptRunEnvelope.Linkage,
    checkGeneratedPCCPackexpRecordDigest: undefined,
  };

  envelope.ConcreteChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope: envelope.ConcreteGeneratedAcceptRunEnvelope,
    finalCertificateEnvelope: envelope.FinalCertificateEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalCertificate0(envelope, {
    checkConcreteGeneratedAcceptRun: false,
    checkFinalCertificate: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalCertificate0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalCertificate0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'checkGeneratedPCCPackexpRecordPresent']);
});

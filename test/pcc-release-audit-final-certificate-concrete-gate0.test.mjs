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
  assert.equal(out.NF.concreteKBundle, true);
  assert.equal(out.NF.kBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.kBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.kBundleReflectionProofRefsResolve, true);

  assert.equal(out.NF.concreteHardCheck, true);
  assert.equal(out.NF.hardCheckerCoverageComplete, true);
  assert.equal(out.NF.hardNoMinCoverageComplete, true);
  assert.equal(out.NF.hardImportPolicyComplete, true);

  assert.equal(out.NF.concreteFinalIntegration, true);
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
  assert.equal(out.NF.generatedPCCPackexpBoot0B0Accepted, true);
  assert.match(out.NF.generatedPCCPackexpBoot0B0Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.generatedPCCPackexpBoot0B0CoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0FamilyCount, 12);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0RequiredFamilyCount, 12);
  assert.deepEqual(out.NF.generatedPCCPackexpBoot0B0Families, [
    'BIface',
    'BSched',
    'BNF',
    'BTruthEval',
    'BRel',
    'BCharge',
    'BObl',
    'BArith',
    'BMode',
    'BRoute',
    'BHash',
    'BImport',
  ]);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversIface, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversSched, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversNF, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversTruthEval, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversRel, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversCharge, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversObl, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversArith, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversMode, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversRoute, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversHash, true);
  assert.equal(out.NF.generatedPCCPackexpBoot0B0CoversImport, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0Accepted, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0Kind, 'KernelSeed0');
  assert.match(out.NF.generatedPCCPackexpKernelSeed0Digest.hex, /^[0-9a-f]{64}$/);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0RuleCount, 16);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0RequiredRuleCount, 16);
  assert.deepEqual(out.NF.generatedPCCPackexpKernelSeed0Rules, [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
    'LedgerInd',
    'OblTopoInd',
    'TraceInd',
    'FiniteExhaust',
    'DPInd',
    'Hall',
    'RankInd',
    'MinCounterexample',
    'IntArith',
    'Transport',
    'TruthVec',
    'FiniteRel',
  ]);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0AllRequiredRulesPresent, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasEq, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasSubst, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasRecord, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasDAGInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasLedgerInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasOblTopoInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasTraceInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasFiniteExhaust, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasDPInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasHall, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasRankInd, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasMinCounterexample, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasIntArith, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasTransport, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasTruthVec, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0HasFiniteRel, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0ProofNodeKindCount, 5);
  assert.deepEqual(out.NF.generatedPCCPackexpKernelSeed0ProofNodeKinds, [
    'PrimitiveRule',
    'SigmaInstance',
    'ReflectionInstance',
    'RowProof',
    'PackageTheorem',
  ]);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0ProofRefsHashIndependent, true);
  assert.equal(out.NF.generatedPCCPackexpKernelSeed0PiBootDigestMatches, true);

  assert.equal(out.NF.finalCertificateUsesConcreteAcceptRun, true);
  assert.equal(out.NF.statusUsesConcreteFinalCertificate, true);

  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects missing concrete PCCPack evidence', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain = {
    ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain,
    concretePCCPack: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concretePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, ['ConcreteFinalCertificatePublicStatusEnvelope', 'ConcreteChain', 'concretePCCPack']);
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

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects incomplete concrete HardCheck coverage', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain = {
    ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain,
    hardNoMinCoverageComplete: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concretePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, ['ConcreteFinalCertificatePublicStatusEnvelope', 'ConcreteChain', 'hardNoMinCoverageComplete']);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects missing CheckPCCPackexp0 evidence', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain = {
    ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain,
    checkPCCPackexpRecordPresent: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concretePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, [
    'ConcreteFinalCertificatePublicStatusEnvelope',
    'ConcreteChain',
    'checkPCCPackexpRecordPresent',
  ]);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects missing GeneratedPCCPackexp0 evidence', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain = {
    ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain,
    generatedPCCPackexpEnvelopePresent: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concretePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, [
    'ConcreteFinalCertificatePublicStatusEnvelope',
    'ConcreteChain',
    'generatedPCCPackexpEnvelopePresent',
  ]);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects missing CheckGeneratedPCCPackexp0 record evidence', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain = {
    ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain,
    checkGeneratedPCCPackexpRecordPresent: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concretePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, [
    'ConcreteFinalCertificatePublicStatusEnvelope',
    'ConcreteChain',
    'checkGeneratedPCCPackexpRecordPresent',
  ]);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects missing Boot0 bridge evidence', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain = {
    ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain,
    generatedPCCPackexpBoot0: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concretePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, [
    'ConcreteFinalCertificatePublicStatusEnvelope',
    'ConcreteChain',
    'generatedPCCPackexpBoot0',
  ]);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects missing B0 row-family coverage', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain = {
    ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain,
    generatedPCCPackexpBoot0B0CoversTruthEval: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concretePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, [
    'ConcreteFinalCertificatePublicStatusEnvelope',
    'ConcreteChain',
    'generatedPCCPackexpBoot0B0CoversTruthEval',
  ]);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects missing KernelSeed0 primitive rule evidence', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain = {
    ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain,
    generatedPCCPackexpKernelSeed0HasHall: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concretePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, [
    'ConcreteFinalCertificatePublicStatusEnvelope',
    'ConcreteChain',
    'generatedPCCPackexpKernelSeed0HasHall',
  ]);
});

test('CheckReleaseAuditConcreteFinalCertificateGate0 rejects unsafe KernelSeed0 proof-reference policy evidence', async () => {
  const releaseAuditRecord = makeAcceptedReleaseAuditRecord0();
  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0({
    ReleaseAuditRecord: releaseAuditRecord,
    runReleaseAudit: false,
  });

  envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain = {
    ...envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteChain,
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque: false,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concretePublicStatusEnvelopeDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, {
    checkConcretePublicStatus: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckReleaseAuditConcreteFinalCertificateGate0');
  assert.equal(out.Coord, 'CheckReleaseAuditConcreteFinalCertificateGate0.PublicConclusion');
  assert.deepEqual(out.Path, [
    'ConcreteFinalCertificatePublicStatusEnvelope',
    'ConcreteChain',
    'generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque',
  ]);
});

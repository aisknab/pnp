import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckFinalCertificatePublicStatus0,
  makeFinalCertificatePublicStatus0,
} from './pcc-final-certificate-public-status0.mjs';

import {
  CheckConcreteMaterializedFinalCertificate0,
  makeConcreteMaterializedFinalCertificate0,
  summarizeConcreteFinalCertificateChain0,
} from './pcc-final-certificate-concrete-materialized0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_PUBLIC_STATUS_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const CONCRETE_PUBLIC_STATUS_SYNTHETIC_MARKER0 = 'synthetic';

export function makeConcreteFinalCertificatePublicStatusConfig0(overrides = {}) {
  return {
    kind: 'ConcreteFinalCertificatePublicStatusConfig0',
    version: CHECKER_VERSION,
    checkConcreteFinalCertificate: true,
    checkFinalCertificatePublicStatus: true,
    checkConcreteChain: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    concreteFinalCertificateConfig: {},
    finalCertificatePublicStatusConfig: {
      checkReleaseAuditRecord: false,
    },
    ...overrides,
  };
}

export async function makeConcreteFinalCertificatePublicStatus0({
  ConcreteFinalCertificateEnvelope = null,
  FinalCertificatePublicStatusEnvelope = null,
  ReleaseAuditRecord = null,
  overrides = {},
} = {}) {
  const concreteFinalCertificateEnvelope = ConcreteFinalCertificateEnvelope ?? await makeConcreteMaterializedFinalCertificate0();

  const finalCertificatePublicStatusEnvelope = FinalCertificatePublicStatusEnvelope ?? await makeFinalCertificatePublicStatus0({
    FinalCertificateEnvelope: concreteFinalCertificateEnvelope.FinalCertificateEnvelope,
    ReleaseAuditRecord,
  });

  const concreteChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope,
  });

  const linkage = {
    kind: 'ConcreteFinalCertificatePublicStatusLinkage0',
    version: CHECKER_VERSION,
    concreteFinalCertificateEnvelopeDigest: digestCanonical0(concreteFinalCertificateEnvelope),
    finalCertificateEnvelopeDigest: digestCanonical0(concreteFinalCertificateEnvelope.FinalCertificateEnvelope),
    finalCertificatePublicStatusEnvelopeDigest: digestCanonical0(finalCertificatePublicStatusEnvelope),
    publicStatusDigest: digestCanonical0(finalCertificatePublicStatusEnvelope.PublicStatus),
    certificateDigest: digestCanonical0(concreteFinalCertificateEnvelope.FinalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(concreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest:
      concreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict.Digest ??
      concreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict.digest ??
      null,
    acceptRunDigest: digestCanonical0(
      concreteFinalCertificateEnvelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun,
    ),
    pccPackDigest: digestCanonical0(
      concreteFinalCertificateEnvelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen,
    ),
    concreteChainDigest: digestCanonical0(concreteChain),
  };

  return {
    kind: 'ConcreteFinalCertificatePublicStatus0',
    version: CHECKER_VERSION,
    ConcreteFinalCertificateEnvelope: concreteFinalCertificateEnvelope,
    FinalCertificatePublicStatusEnvelope: finalCertificatePublicStatusEnvelope,
    ConcreteChain: concreteChain,
    Linkage: linkage,
    PiConcreteFinalCertificatePublicStatus: {
      kind: 'PiConcreteFinalCertificatePublicStatus0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteFinalCertificateEnvelope',
          digest: linkage.concreteFinalCertificateEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalCertificatePublicStatusEnvelope',
          digest: linkage.finalCertificatePublicStatusEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ConcretePublicStatusChain',
          digest: linkage.concreteChainDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function summarizeConcreteFinalCertificatePublicStatusChain0({
  concreteFinalCertificateEnvelope,
  finalCertificatePublicStatusEnvelope,
}) {
  const concreteCertificateChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope: concreteFinalCertificateEnvelope?.ConcreteGeneratedAcceptRunEnvelope ?? null,
    finalCertificateEnvelope: concreteFinalCertificateEnvelope?.FinalCertificateEnvelope ?? null,
  });

  const concreteFinalCertificateInnerEnvelope = concreteFinalCertificateEnvelope?.FinalCertificateEnvelope ?? null;
  const statusFinalCertificateEnvelope = finalCertificatePublicStatusEnvelope?.FinalCertificateEnvelope ?? null;
  const publicStatus = finalCertificatePublicStatusEnvelope?.PublicStatus ?? null;
  const certificate = concreteFinalCertificateInnerEnvelope?.Certificate ?? null;
  const finalVerdict = concreteFinalCertificateInnerEnvelope?.FinalVerdict ?? null;
  const acceptRun = concreteFinalCertificateEnvelope?.ConcreteGeneratedAcceptRunEnvelope?.GeneratedAcceptRunEnvelope?.AcceptRun ?? null;

  const concreteFinalCertificateEnvelopeDigest = digestCanonical0(concreteFinalCertificateInnerEnvelope);
  const statusFinalCertificateEnvelopeDigest = digestCanonical0(statusFinalCertificateEnvelope);
  const certificateDigest = digestCanonical0(certificate);
  const publicStatusCertificateDigest = publicStatus?.certificateDigest ?? null;
  const finalVerdictRecordDigest = finalVerdict?.Digest ?? finalVerdict?.digest ?? null;
  const publicStatusFinalVerdictDigest = publicStatus?.finalVerdictDigest ?? null;
  const acceptRunDigest = digestCanonical0(acceptRun);
  const publicStatusAcceptRunDigest = publicStatus?.acceptRunDigest ?? null;
  const pccPackDigest = digestCanonical0(acceptRun?.Pgen ?? null);
  const publicStatusPccPackDigest = publicStatus?.pccPackDigest ?? null;

  return {
    kind: 'ConcreteFinalCertificatePublicStatusChain0',
    version: CHECKER_VERSION,

    concreteRows: concreteCertificateChain.concreteRows,
    concreteLocalPackages: concreteCertificateChain.concreteLocalPackages,
    concreteGlobalFirewalls: concreteCertificateChain.concreteGlobalFirewalls,
    concreteGlobalProofDAG: concreteCertificateChain.concreteGlobalProofDAG,

    concreteKBundle: concreteCertificateChain.concreteKBundle,
    kBundleKernelRuleCoverageComplete: concreteCertificateChain.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: concreteCertificateChain.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: concreteCertificateChain.kBundleReflectionProofRefsResolve,

    concreteHardCheck: concreteCertificateChain.concreteHardCheck,
    hardCheckerCoverageComplete: concreteCertificateChain.hardCheckerCoverageComplete,
    hardRowKeyCoverageComplete: concreteCertificateChain.hardRowKeyCoverageComplete,
    hardRoutePriorityComplete: concreteCertificateChain.hardRoutePriorityComplete,
    hardProofRefPolicyComplete: concreteCertificateChain.hardProofRefPolicyComplete,
    hardHashDisciplineComplete: concreteCertificateChain.hardHashDisciplineComplete,
    hardNoMinCoverageComplete: concreteCertificateChain.hardNoMinCoverageComplete,
    hardImportPolicyComplete: concreteCertificateChain.hardImportPolicyComplete,
    hardReflectionPolicyComplete: concreteCertificateChain.hardReflectionPolicyComplete,
    hardBoundsPolicyComplete: concreteCertificateChain.hardBoundsPolicyComplete,
    hardDiagnosticsPolicyComplete: concreteCertificateChain.hardDiagnosticsPolicyComplete,

    concreteFinalIntegration: concreteCertificateChain.concreteFinalIntegration,
    finalIntegrationConcreteGlobalProofDAG: concreteCertificateChain.finalIntegrationConcreteGlobalProofDAG,
    finalIntegrationGPackFieldCoverageComplete: concreteCertificateChain.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: concreteCertificateChain.finalIntegrationRowFamGCoverageComplete,
    finalIntegrationUsesGPack: concreteCertificateChain.finalIntegrationUsesGPack,
    rowFamGUsesGPack: concreteCertificateChain.rowFamGUsesGPack,
    finalTheoremUsesFinalIntegration: concreteCertificateChain.finalTheoremUsesFinalIntegration,
    rowFamFinalUsesFinalTheorem: concreteCertificateChain.rowFamFinalUsesFinalTheorem,
    finalMatchUsesGPack: concreteCertificateChain.finalMatchUsesGPack,
    satDecisionUsesGPack: concreteCertificateChain.satDecisionUsesGPack,

    concretePCCPack: concreteCertificateChain.concretePCCPack,
    concretePCCPackCoverageDigest: concreteCertificateChain.concretePCCPackCoverageDigest,
    pccPackPublicConclusionOnlyAfterAcceptRun: concreteCertificateChain.pccPackPublicConclusionOnlyAfterAcceptRun,
    pccPackLinkedToKBundle: concreteCertificateChain.pccPackLinkedToKBundle,
    pccPackLinkedToHardCheck: concreteCertificateChain.pccPackLinkedToHardCheck,
    pccPackLinkedToRows: concreteCertificateChain.pccPackLinkedToRows,
    pccPackLinkedToLocalPackages: concreteCertificateChain.pccPackLinkedToLocalPackages,
    pccPackLinkedToGlobalFirewalls: concreteCertificateChain.pccPackLinkedToGlobalFirewalls,
    pccPackLinkedToGlobalProofDAG: concreteCertificateChain.pccPackLinkedToGlobalProofDAG,
    pccPackLinkedToGPack: concreteCertificateChain.pccPackLinkedToGPack,
    pccPackLinkedToFinalIntegration: concreteCertificateChain.pccPackLinkedToFinalIntegration,
    pccPackLinkedToFinalTheorem: concreteCertificateChain.pccPackLinkedToFinalTheorem,

    checkPCCPackexpRecordPresent: concreteCertificateChain.checkPCCPackexpRecordPresent,
    checkPCCPackexpRecordAccepted: concreteCertificateChain.checkPCCPackexpRecordAccepted,
    checkPCCPackexpRecordChecker: concreteCertificateChain.checkPCCPackexpRecordChecker,
    checkPCCPackexpRecordDigest: concreteCertificateChain.checkPCCPackexpRecordDigest,
    checkPCCPackexpRecordDigestMatchesNF: concreteCertificateChain.checkPCCPackexpRecordDigestMatchesNF,
    checkPCCPackexpRecordConcretePCCPack: concreteCertificateChain.checkPCCPackexpRecordConcretePCCPack,
    checkPCCPackexpRecordPccPackDigest: concreteCertificateChain.checkPCCPackexpRecordPccPackDigest,
    checkPCCPackexpRecordPccPackDigestMatchesConcreteRun: concreteCertificateChain.checkPCCPackexpRecordPccPackDigestMatchesConcreteRun,
    checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: concreteCertificateChain.checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun,
    checkPCCPackexpRecordPublicConclusionNotEmitted: concreteCertificateChain.checkPCCPackexpRecordPublicConclusionNotEmitted,
    checkPCCPackexpRecordClaimBoundaryConditional: concreteCertificateChain.checkPCCPackexpRecordClaimBoundaryConditional,

    generatedPCCPackexpEnvelopePresent: concreteCertificateChain.generatedPCCPackexpEnvelopePresent,
    generatedPCCPackexpEnvelopeDigest: concreteCertificateChain.generatedPCCPackexpEnvelopeDigest,
    generatedPCCPackexpGenCallGeneratePCCPack: concreteCertificateChain.generatedPCCPackexpGenCallGeneratePCCPack,
    generatedPCCPackexpCoreOnly: concreteCertificateChain.generatedPCCPackexpCoreOnly,
    generatedPCCPackexpExcludesAcceptRun: concreteCertificateChain.generatedPCCPackexpExcludesAcceptRun,
    generatedPCCPackexpPackageMatchesConcreteRun: concreteCertificateChain.generatedPCCPackexpPackageMatchesConcreteRun,
    generatedPCCPackexpCheckRecordMatchesConcreteRun: concreteCertificateChain.generatedPCCPackexpCheckRecordMatchesConcreteRun,
    generatedPCCPackexpCheckRecordAccepted: concreteCertificateChain.generatedPCCPackexpCheckRecordAccepted,
    generatedPCCPackexpCheckRecordChecker: concreteCertificateChain.generatedPCCPackexpCheckRecordChecker,
    generatedPCCPackexpCheckRecordDigest: concreteCertificateChain.generatedPCCPackexpCheckRecordDigest,
    generatedPCCPackexpCheckRecordDigestMatchesNF: concreteCertificateChain.generatedPCCPackexpCheckRecordDigestMatchesNF,
    generatedPCCPackexpCheckRecordClaimBoundaryConditional: concreteCertificateChain.generatedPCCPackexpCheckRecordClaimBoundaryConditional,
    generatedPCCPackexpLinkageGeneratedPackageDigestMatches: concreteCertificateChain.generatedPCCPackexpLinkageGeneratedPackageDigestMatches,
    generatedPCCPackexpLinkageCheckRecordDigestMatches: concreteCertificateChain.generatedPCCPackexpLinkageCheckRecordDigestMatches,

    checkGeneratedPCCPackexpRecordPresent:
      concreteCertificateChain.checkGeneratedPCCPackexpRecordPresent,
    checkGeneratedPCCPackexpRecordAccepted:
      concreteCertificateChain.checkGeneratedPCCPackexpRecordAccepted,
    checkGeneratedPCCPackexpRecordChecker:
      concreteCertificateChain.checkGeneratedPCCPackexpRecordChecker,
    checkGeneratedPCCPackexpRecordDigest:
      concreteCertificateChain.checkGeneratedPCCPackexpRecordDigest,
    checkGeneratedPCCPackexpRecordDigestMatchesNF:
      concreteCertificateChain.checkGeneratedPCCPackexpRecordDigestMatchesNF,
    checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope:
      concreteCertificateChain.checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope,
    checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope:
      concreteCertificateChain.checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope,

    generatedPCCPackexpBoot0: concreteCertificateChain.generatedPCCPackexpBoot0,
    generatedPCCPackexpBoot0Accepted: concreteCertificateChain.generatedPCCPackexpBoot0Accepted,
    generatedPCCPackexpBoot0Kind: concreteCertificateChain.generatedPCCPackexpBoot0Kind,
    generatedPCCPackexpBoot0Digest: concreteCertificateChain.generatedPCCPackexpBoot0Digest,
    generatedPCCPackexpBoot0CheckDigest: concreteCertificateChain.generatedPCCPackexpBoot0CheckDigest,
    generatedPCCPackexpBoot0CanonicalByteDigest:
      concreteCertificateChain.generatedPCCPackexpBoot0CanonicalByteDigest,
    generatedPCCPackexpBoot0RowCount: concreteCertificateChain.generatedPCCPackexpBoot0RowCount,
    generatedPCCPackexpBoot0KernelRuleCount:
      concreteCertificateChain.generatedPCCPackexpBoot0KernelRuleCount,
    generatedPCCPackexpBoot0JsonMaterialized:
      concreteCertificateChain.generatedPCCPackexpBoot0JsonMaterialized,
    generatedPCCPackexpBoot0NoFixtureMarkers:
      concreteCertificateChain.generatedPCCPackexpBoot0NoFixtureMarkers,
    generatedPCCPackexpBoot0BootBatchDigest:
      concreteCertificateChain.generatedPCCPackexpBoot0BootBatchDigest,
    generatedPCCPackexpBoot0BootAuditDigest:
      concreteCertificateChain.generatedPCCPackexpBoot0BootAuditDigest,
    generatedPCCPackexpBoot0LinkedToPCCPack:
      concreteCertificateChain.generatedPCCPackexpBoot0LinkedToPCCPack,
    generatedPCCPackexpBoot0LinkedToCoreDigestMap:
      concreteCertificateChain.generatedPCCPackexpBoot0LinkedToCoreDigestMap,
    generatedPCCPackexpBoot0DigestMatchesGeneratedPackage:
      concreteCertificateChain.generatedPCCPackexpBoot0DigestMatchesGeneratedPackage,
    generatedPCCPackexpBoot0DigestMatchesCoreDigestMap:
      concreteCertificateChain.generatedPCCPackexpBoot0DigestMatchesCoreDigestMap,

    generatedPCCPackexpBoot0B0Accepted:
      concreteCertificateChain.generatedPCCPackexpBoot0B0Accepted,
    generatedPCCPackexpBoot0B0Digest:
      concreteCertificateChain.generatedPCCPackexpBoot0B0Digest,
    generatedPCCPackexpBoot0B0CoverageDigest:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoverageDigest,
    generatedPCCPackexpBoot0B0FamilyCount:
      concreteCertificateChain.generatedPCCPackexpBoot0B0FamilyCount,
    generatedPCCPackexpBoot0B0RequiredFamilyCount:
      concreteCertificateChain.generatedPCCPackexpBoot0B0RequiredFamilyCount,
    generatedPCCPackexpBoot0B0Families:
      concreteCertificateChain.generatedPCCPackexpBoot0B0Families,
    generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent:
      concreteCertificateChain.generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent,
    generatedPCCPackexpBoot0B0CoversIface:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversIface,
    generatedPCCPackexpBoot0B0CoversSched:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversSched,
    generatedPCCPackexpBoot0B0CoversNF:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversNF,
    generatedPCCPackexpBoot0B0CoversTruthEval:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversTruthEval,
    generatedPCCPackexpBoot0B0CoversRel:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversRel,
    generatedPCCPackexpBoot0B0CoversCharge:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversCharge,
    generatedPCCPackexpBoot0B0CoversObl:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversObl,
    generatedPCCPackexpBoot0B0CoversArith:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversArith,
    generatedPCCPackexpBoot0B0CoversMode:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversMode,
    generatedPCCPackexpBoot0B0CoversRoute:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversRoute,
    generatedPCCPackexpBoot0B0CoversHash:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversHash,
    generatedPCCPackexpBoot0B0CoversImport:
      concreteCertificateChain.generatedPCCPackexpBoot0B0CoversImport,

    generatedPCCPackexpKernelSeed0:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0,
    generatedPCCPackexpKernelSeed0Accepted:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0Accepted,
    generatedPCCPackexpKernelSeed0Kind:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0Kind,
    generatedPCCPackexpKernelSeed0Digest:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0Digest,
    generatedPCCPackexpKernelSeed0RuleCount:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0RuleCount,
    generatedPCCPackexpKernelSeed0RequiredRuleCount:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0RequiredRuleCount,
    generatedPCCPackexpKernelSeed0Rules:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0Rules,
    generatedPCCPackexpKernelSeed0AllRequiredRulesPresent:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0AllRequiredRulesPresent,
    generatedPCCPackexpKernelSeed0HasEq:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasEq,
    generatedPCCPackexpKernelSeed0HasSubst:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasSubst,
    generatedPCCPackexpKernelSeed0HasRecord:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasRecord,
    generatedPCCPackexpKernelSeed0HasDAGInd:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasDAGInd,
    generatedPCCPackexpKernelSeed0HasLedgerInd:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasLedgerInd,
    generatedPCCPackexpKernelSeed0HasOblTopoInd:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasOblTopoInd,
    generatedPCCPackexpKernelSeed0HasTraceInd:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasTraceInd,
    generatedPCCPackexpKernelSeed0HasFiniteExhaust:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasFiniteExhaust,
    generatedPCCPackexpKernelSeed0HasDPInd:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasDPInd,
    generatedPCCPackexpKernelSeed0HasHall:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasHall,
    generatedPCCPackexpKernelSeed0HasRankInd:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasRankInd,
    generatedPCCPackexpKernelSeed0HasMinCounterexample:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasMinCounterexample,
    generatedPCCPackexpKernelSeed0HasIntArith:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasIntArith,
    generatedPCCPackexpKernelSeed0HasTransport:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasTransport,
    generatedPCCPackexpKernelSeed0HasTruthVec:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasTruthVec,
    generatedPCCPackexpKernelSeed0HasFiniteRel:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0HasFiniteRel,
    generatedPCCPackexpKernelSeed0ProofNodeKindCount:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0ProofNodeKindCount,
    generatedPCCPackexpKernelSeed0ProofNodeKinds:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0ProofNodeKinds,
    generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent,
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque,
    generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic,
    generatedPCCPackexpKernelSeed0ProofRefsHashIndependent:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0ProofRefsHashIndependent,
    generatedPCCPackexpKernelSeed0PiBootDigestMatches:
      concreteCertificateChain.generatedPCCPackexpKernelSeed0PiBootDigestMatches,

    generatedPCCPackexpCodec0:
      concreteCertificateChain.generatedPCCPackexpCodec0,
    generatedPCCPackexpCodec0Accepted:
      concreteCertificateChain.generatedPCCPackexpCodec0Accepted,
    generatedPCCPackexpCodec0Kind:
      concreteCertificateChain.generatedPCCPackexpCodec0Kind,
    generatedPCCPackexpCodec0Digest:
      concreteCertificateChain.generatedPCCPackexpCodec0Digest,
    generatedPCCPackexpCodec0Canonical:
      concreteCertificateChain.generatedPCCPackexpCodec0Canonical,
    generatedPCCPackexpCodec0NaturalEncoding:
      concreteCertificateChain.generatedPCCPackexpCodec0NaturalEncoding,
    generatedPCCPackexpCodec0NaturalEncodingCanonical:
      concreteCertificateChain.generatedPCCPackexpCodec0NaturalEncodingCanonical,
    generatedPCCPackexpCodec0IntegerEncoding:
      concreteCertificateChain.generatedPCCPackexpCodec0IntegerEncoding,
    generatedPCCPackexpCodec0IntegerEncodingCanonical:
      concreteCertificateChain.generatedPCCPackexpCodec0IntegerEncodingCanonical,
    generatedPCCPackexpCodec0StringEncoding:
      concreteCertificateChain.generatedPCCPackexpCodec0StringEncoding,
    generatedPCCPackexpCodec0StringEncodingCanonical:
      concreteCertificateChain.generatedPCCPackexpCodec0StringEncodingCanonical,
    generatedPCCPackexpCodec0TopLevelConsumesAllBytes:
      concreteCertificateChain.generatedPCCPackexpCodec0TopLevelConsumesAllBytes,
    generatedPCCPackexpCodec0NormalFormSerialization:
      concreteCertificateChain.generatedPCCPackexpCodec0NormalFormSerialization,
    generatedPCCPackexpCodec0NormalFormSerializationCanonical:
      concreteCertificateChain.generatedPCCPackexpCodec0NormalFormSerializationCanonical,
    generatedPCCPackexpCodec0PiBootDigestMatches:
      concreteCertificateChain.generatedPCCPackexpCodec0PiBootDigestMatches,

    generatedPCCPackexpDigest0:
      concreteCertificateChain.generatedPCCPackexpDigest0,
    generatedPCCPackexpDigest0Accepted:
      concreteCertificateChain.generatedPCCPackexpDigest0Accepted,
    generatedPCCPackexpDigest0Kind:
      concreteCertificateChain.generatedPCCPackexpDigest0Kind,
    generatedPCCPackexpDigest0Digest:
      concreteCertificateChain.generatedPCCPackexpDigest0Digest,
    generatedPCCPackexpDigest0Alg:
      concreteCertificateChain.generatedPCCPackexpDigest0Alg,
    generatedPCCPackexpDigest0AlgSHA256:
      concreteCertificateChain.generatedPCCPackexpDigest0AlgSHA256,
    generatedPCCPackexpDigest0Bytes:
      concreteCertificateChain.generatedPCCPackexpDigest0Bytes,
    generatedPCCPackexpDigest0BytesCanonicalJson:
      concreteCertificateChain.generatedPCCPackexpDigest0BytesCanonicalJson,
    generatedPCCPackexpDigest0EqualityNotObjectEquality:
      concreteCertificateChain.generatedPCCPackexpDigest0EqualityNotObjectEquality,
    generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup:
      concreteCertificateChain.generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup,
    generatedPCCPackexpDigest0PiBootDigestMatches:
      concreteCertificateChain.generatedPCCPackexpDigest0PiBootDigestMatches,

    generatedPCCPackexpIfaceDict0:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0,
    generatedPCCPackexpIfaceDict0Accepted:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0Accepted,
    generatedPCCPackexpIfaceDict0Kind:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0Kind,
    generatedPCCPackexpIfaceDict0Digest:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0Digest,
    generatedPCCPackexpIfaceDict0ForbiddenSymbolCount:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0ForbiddenSymbolCount,
    generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent,
    generatedPCCPackexpIfaceDict0NoExecutableMinSymbols:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0NoExecutableMinSymbols,
    generatedPCCPackexpIfaceDict0PublicConstructorsPresent:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0PublicConstructorsPresent,
    generatedPCCPackexpIfaceDict0CriticalKindsPresent:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0CriticalKindsPresent,
    generatedPCCPackexpIfaceDict0RouteTokensPresent:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0RouteTokensPresent,
    generatedPCCPackexpIfaceDict0PiBootDigestMatches:
      concreteCertificateChain.generatedPCCPackexpIfaceDict0PiBootDigestMatches,

    generatedPCCPackexpSched0:
      concreteCertificateChain.generatedPCCPackexpSched0,
    generatedPCCPackexpSched0Accepted:
      concreteCertificateChain.generatedPCCPackexpSched0Accepted,
    generatedPCCPackexpSched0Kind:
      concreteCertificateChain.generatedPCCPackexpSched0Kind,
    generatedPCCPackexpSched0Digest:
      concreteCertificateChain.generatedPCCPackexpSched0Digest,
    generatedPCCPackexpSched0CoreMatchesExpected:
      concreteCertificateChain.generatedPCCPackexpSched0CoreMatchesExpected,
    generatedPCCPackexpSched0CoreB0:
      concreteCertificateChain.generatedPCCPackexpSched0CoreB0,
    generatedPCCPackexpSched0CoreK0:
      concreteCertificateChain.generatedPCCPackexpSched0CoreK0,
    generatedPCCPackexpSched0CoreR0:
      concreteCertificateChain.generatedPCCPackexpSched0CoreR0,
    generatedPCCPackexpSched0CoreH0:
      concreteCertificateChain.generatedPCCPackexpSched0CoreH0,
    generatedPCCPackexpSched0CoreO0:
      concreteCertificateChain.generatedPCCPackexpSched0CoreO0,
    generatedPCCPackexpSched0CoreRel0:
      concreteCertificateChain.generatedPCCPackexpSched0CoreRel0,
    generatedPCCPackexpSched0ScaleFactorsPresent:
      concreteCertificateChain.generatedPCCPackexpSched0ScaleFactorsPresent,
    generatedPCCPackexpSched0SelectorBoundsPresent:
      concreteCertificateChain.generatedPCCPackexpSched0SelectorBoundsPresent,
    generatedPCCPackexpSched0SelectorBoundBH:
      concreteCertificateChain.generatedPCCPackexpSched0SelectorBoundBH,
    generatedPCCPackexpSched0SelectorBoundBTheta:
      concreteCertificateChain.generatedPCCPackexpSched0SelectorBoundBTheta,
    generatedPCCPackexpSched0PolynomialExponent:
      concreteCertificateChain.generatedPCCPackexpSched0PolynomialExponent,
    generatedPCCPackexpSched0PiBootDigestMatches:
      concreteCertificateChain.generatedPCCPackexpSched0PiBootDigestMatches,

    generatedPCCPackexpByteLang0:
      concreteCertificateChain.generatedPCCPackexpByteLang0,
    generatedPCCPackexpByteLang0Accepted:
      concreteCertificateChain.generatedPCCPackexpByteLang0Accepted,
    generatedPCCPackexpByteLang0Kind:
      concreteCertificateChain.generatedPCCPackexpByteLang0Kind,
    generatedPCCPackexpByteLang0Digest:
      concreteCertificateChain.generatedPCCPackexpByteLang0Digest,
    generatedPCCPackexpByteLang0TagCount:
      concreteCertificateChain.generatedPCCPackexpByteLang0TagCount,
    generatedPCCPackexpByteLang0TagsUnique:
      concreteCertificateChain.generatedPCCPackexpByteLang0TagsUnique,
    generatedPCCPackexpByteLang0RequiredTagsPresent:
      concreteCertificateChain.generatedPCCPackexpByteLang0RequiredTagsPresent,
    generatedPCCPackexpByteLang0SortCount:
      concreteCertificateChain.generatedPCCPackexpByteLang0SortCount,
    generatedPCCPackexpByteLang0RequiredSortsPresent:
      concreteCertificateChain.generatedPCCPackexpByteLang0RequiredSortsPresent,
    generatedPCCPackexpByteLang0ConstructorCount:
      concreteCertificateChain.generatedPCCPackexpByteLang0ConstructorCount,
    generatedPCCPackexpByteLang0RequiredConstructorsPresent:
      concreteCertificateChain.generatedPCCPackexpByteLang0RequiredConstructorsPresent,
    generatedPCCPackexpByteLang0RecordCount:
      concreteCertificateChain.generatedPCCPackexpByteLang0RecordCount,
    generatedPCCPackexpByteLang0RequiredRecordAritiesPresent:
      concreteCertificateChain.generatedPCCPackexpByteLang0RequiredRecordAritiesPresent,
    generatedPCCPackexpByteLang0PiBootDigestMatches:
      concreteCertificateChain.generatedPCCPackexpByteLang0PiBootDigestMatches,

    generatedPCCPackexpBootAudit0:
      concreteCertificateChain.generatedPCCPackexpBootAudit0,
    generatedPCCPackexpBootAudit0Accepted:
      concreteCertificateChain.generatedPCCPackexpBootAudit0Accepted,
    generatedPCCPackexpBootAudit0Checker:
      concreteCertificateChain.generatedPCCPackexpBootAudit0Checker,
    generatedPCCPackexpBootAudit0Digest:
      concreteCertificateChain.generatedPCCPackexpBootAudit0Digest,
    generatedPCCPackexpBootAudit0DigestMatchesNF:
      concreteCertificateChain.generatedPCCPackexpBootAudit0DigestMatchesNF,
    generatedPCCPackexpBootAudit0NFKind:
      concreteCertificateChain.generatedPCCPackexpBootAudit0NFKind,
    generatedPCCPackexpBootAudit0SuiteId:
      concreteCertificateChain.generatedPCCPackexpBootAudit0SuiteId,
    generatedPCCPackexpBootAudit0CaseCount:
      concreteCertificateChain.generatedPCCPackexpBootAudit0CaseCount,
    generatedPCCPackexpBootAudit0PositiveCount:
      concreteCertificateChain.generatedPCCPackexpBootAudit0PositiveCount,
    generatedPCCPackexpBootAudit0NegativeCount:
      concreteCertificateChain.generatedPCCPackexpBootAudit0NegativeCount,
    generatedPCCPackexpBootAudit0CoversB0Accept:
      concreteCertificateChain.generatedPCCPackexpBootAudit0CoversB0Accept,
    generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject:
      concreteCertificateChain.generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject,
    generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject:
      concreteCertificateChain.generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject,

    generatedPCCPackexpPiBoot0:
      concreteCertificateChain.generatedPCCPackexpPiBoot0,
    generatedPCCPackexpPiBoot0Accepted:
      concreteCertificateChain.generatedPCCPackexpPiBoot0Accepted,
    generatedPCCPackexpPiBoot0Kind:
      concreteCertificateChain.generatedPCCPackexpPiBoot0Kind,
    generatedPCCPackexpPiBoot0Digest:
      concreteCertificateChain.generatedPCCPackexpPiBoot0Digest,
    generatedPCCPackexpPiBoot0Materialized:
      concreteCertificateChain.generatedPCCPackexpPiBoot0Materialized,
    generatedPCCPackexpPiBoot0ExternalJson:
      concreteCertificateChain.generatedPCCPackexpPiBoot0ExternalJson,
    generatedPCCPackexpPiBoot0RefCount:
      concreteCertificateChain.generatedPCCPackexpPiBoot0RefCount,
    generatedPCCPackexpPiBoot0AllBootRefsPresent:
      concreteCertificateChain.generatedPCCPackexpPiBoot0AllBootRefsPresent,
    generatedPCCPackexpPiBoot0RefsMatchBootObjects:
      concreteCertificateChain.generatedPCCPackexpPiBoot0RefsMatchBootObjects,
    generatedPCCPackexpPiBoot0RefsIncludeByteLang0:
      concreteCertificateChain.generatedPCCPackexpPiBoot0RefsIncludeByteLang0,
    generatedPCCPackexpPiBoot0RefsIncludeCodec0:
      concreteCertificateChain.generatedPCCPackexpPiBoot0RefsIncludeCodec0,
    generatedPCCPackexpPiBoot0RefsIncludeDigest0:
      concreteCertificateChain.generatedPCCPackexpPiBoot0RefsIncludeDigest0,
    generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0:
      concreteCertificateChain.generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0,
    generatedPCCPackexpPiBoot0RefsIncludeSched0:
      concreteCertificateChain.generatedPCCPackexpPiBoot0RefsIncludeSched0,
    generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0:
      concreteCertificateChain.generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0,
    generatedPCCPackexpPiBoot0RefsIncludeB0:
      concreteCertificateChain.generatedPCCPackexpPiBoot0RefsIncludeB0,
    generatedPCCPackexpPiBoot0RefsIncludeBootAudit0:
      concreteCertificateChain.generatedPCCPackexpPiBoot0RefsIncludeBootAudit0,

    generatedPCCPackexpConcreteKBundle0:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0,
    generatedPCCPackexpConcreteKBundle0Accepted:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0Accepted,
    generatedPCCPackexpConcreteKBundle0Checker:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0Checker,
    generatedPCCPackexpConcreteKBundle0Digest:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0Digest,
    generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest,
    generatedPCCPackexpConcreteKBundle0BootDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0BootDigest,
    generatedPCCPackexpConcreteKBundle0KImplDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0KImplDigest,
    generatedPCCPackexpConcreteKBundle0K0Digest:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0K0Digest,
    generatedPCCPackexpConcreteKBundle0SigmaDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0SigmaDigest,
    generatedPCCPackexpConcreteKBundle0ReflectionDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0ReflectionDigest,
    generatedPCCPackexpConcreteKBundle0ProofInventoryDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0ProofInventoryDigest,
    generatedPCCPackexpConcreteKBundle0KernelRuleCount:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0KernelRuleCount,
    generatedPCCPackexpConcreteKBundle0ConformanceNodeCount:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0ConformanceNodeCount,
    generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete,
    generatedPCCPackexpConcreteKBundle0SigmaTheoremCount:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0SigmaTheoremCount,
    generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete,
    generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve,
    generatedPCCPackexpConcreteKBundle0ReflectionCount:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0ReflectionCount,
    generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete,
    generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve,
    generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs,
    generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols,
    generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0:
      concreteCertificateChain.generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0,

    generatedPCCPackexpConcreteHard0:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0,
    generatedPCCPackexpConcreteHard0Accepted:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0Accepted,
    generatedPCCPackexpConcreteHard0Checker:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0Checker,
    generatedPCCPackexpConcreteHard0Digest:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0Digest,
    generatedPCCPackexpConcreteHard0MaterializedHardDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0MaterializedHardDigest,
    generatedPCCPackexpConcreteHard0HardCheckDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0HardCheckDigest,
    generatedPCCPackexpConcreteHard0CoverageDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0CoverageDigest,
    generatedPCCPackexpConcreteHard0CheckerCount:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0CheckerCount,
    generatedPCCPackexpConcreteHard0CheckerCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0CheckerCoverageComplete,
    generatedPCCPackexpConcreteHard0RowKeyFieldCount:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0RowKeyFieldCount,
    generatedPCCPackexpConcreteHard0RowKeyCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0RowKeyCoverageComplete,
    generatedPCCPackexpConcreteHard0RoutePriorityComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0RoutePriorityComplete,
    generatedPCCPackexpConcreteHard0ProofRefPolicyComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0ProofRefPolicyComplete,
    generatedPCCPackexpConcreteHard0HashDisciplineComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0HashDisciplineComplete,
    generatedPCCPackexpConcreteHard0NoMinCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0NoMinCoverageComplete,
    generatedPCCPackexpConcreteHard0ForbiddenSymbolCount:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0ForbiddenSymbolCount,
    generatedPCCPackexpConcreteHard0ImportPolicyComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0ImportPolicyComplete,
    generatedPCCPackexpConcreteHard0ForbiddenImportEdgeCount:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0ForbiddenImportEdgeCount,
    generatedPCCPackexpConcreteHard0ReflectionPolicyComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0ReflectionPolicyComplete,
    generatedPCCPackexpConcreteHard0BoundsPolicyComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0BoundsPolicyComplete,
    generatedPCCPackexpConcreteHard0DiagnosticsPolicyComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0DiagnosticsPolicyComplete,
    generatedPCCPackexpConcreteHard0LinkedToPCCPack:
      concreteCertificateChain.generatedPCCPackexpConcreteHard0LinkedToPCCPack,

    generatedPCCPackexpConcreteRows0:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0,
    generatedPCCPackexpConcreteRows0Accepted:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0Accepted,
    generatedPCCPackexpConcreteRows0Checker:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0Checker,
    generatedPCCPackexpConcreteRows0Digest:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0Digest,
    generatedPCCPackexpConcreteRows0RowPackDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0RowPackDigest,
    generatedPCCPackexpConcreteRows0RowPackObjectDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0RowPackObjectDigest,
    generatedPCCPackexpConcreteRows0BootDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0BootDigest,
    generatedPCCPackexpConcreteRows0IfaceHash:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0IfaceHash,
    generatedPCCPackexpConcreteRows0SchedHash:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0SchedHash,
    generatedPCCPackexpConcreteRows0RowCount:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0RowCount,
    generatedPCCPackexpConcreteRows0RowCountComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0RowCountComplete,
    generatedPCCPackexpConcreteRows0BatchCount:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0BatchCount,
    generatedPCCPackexpConcreteRows0BatchCountComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0BatchCountComplete,
    generatedPCCPackexpConcreteRows0FamilyCount:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0FamilyCount,
    generatedPCCPackexpConcreteRows0FamilyCountComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0FamilyCountComplete,
    generatedPCCPackexpConcreteRows0ConcreteIfaceHash:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0ConcreteIfaceHash,
    generatedPCCPackexpConcreteRows0SyntheticIfaceHashCount:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0SyntheticIfaceHashCount,
    generatedPCCPackexpConcreteRows0NoSyntheticIfaceHash:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0NoSyntheticIfaceHash,
    generatedPCCPackexpConcreteRows0ScaffoldMarkerCount:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0ScaffoldMarkerCount,
    generatedPCCPackexpConcreteRows0NoScaffoldMarkers:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0NoScaffoldMarkers,
    generatedPCCPackexpConcreteRows0LinkedToGeneratedBoot0:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0LinkedToGeneratedBoot0,
    generatedPCCPackexpConcreteRows0LinkedToPCCPack:
      concreteCertificateChain.generatedPCCPackexpConcreteRows0LinkedToPCCPack,

    generatedPCCPackexpConcreteGlobalProofDAG0:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0,
    generatedPCCPackexpConcreteGlobalProofDAG0Accepted:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0Accepted,
    generatedPCCPackexpConcreteGlobalProofDAG0Checker:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0Checker,
    generatedPCCPackexpConcreteGlobalProofDAG0Digest:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0Digest,
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGObjectDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGObjectDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0MaterializedGlobalProofDAGDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0MaterializedGlobalProofDAGDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0KImplDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0KImplDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0RowPackDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0RowPackDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0LocalPackagesDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0LocalPackagesDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalFirewallsDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0GlobalFirewallsDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleProofInventoryDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0KBundleProofInventoryDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleKernelRuleCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0KBundleKernelRuleCoverageComplete,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleSigmaProofRefsResolve:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0KBundleSigmaProofRefsResolve,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleReflectionProofRefsResolve:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0KBundleReflectionProofRefsResolve,
    generatedPCCPackexpConcreteGlobalProofDAG0NodeCount:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0NodeCount,
    generatedPCCPackexpConcreteGlobalProofDAG0NodeCountMinimum:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0NodeCountMinimum,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalTheoremCount:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0FinalTheoremCount,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalPackageSoundness:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0FinalPackageSoundness,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalGeneratedPackageSufficiency:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0FinalGeneratedPackageSufficiency,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP,
    generatedPCCPackexpConcreteGlobalProofDAG0IfaceHash:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0IfaceHash,
    generatedPCCPackexpConcreteGlobalProofDAG0SchedHash:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0SchedHash,
    generatedPCCPackexpConcreteGlobalProofDAG0IfaceMatchesRows:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0IfaceMatchesRows,
    generatedPCCPackexpConcreteGlobalProofDAG0SchedMatchesKImpl:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0SchedMatchesKImpl,
    generatedPCCPackexpConcreteGlobalProofDAG0SyntheticMarkerCount:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0SyntheticMarkerCount,
    generatedPCCPackexpConcreteGlobalProofDAG0ForbiddenMarkerCount:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0ForbiddenMarkerCount,
    generatedPCCPackexpConcreteGlobalProofDAG0NoForbiddenMarkers:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0NoForbiddenMarkers,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGeneratedBoot0:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGeneratedBoot0,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToKImpl:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToKImpl,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToConcreteRows:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToConcreteRows,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToLocalPackages:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToLocalPackages,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGlobalFirewalls:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGlobalFirewalls,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToPCCPack:
      concreteCertificateChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToPCCPack,

    generatedPCCPackexpConcreteFinalIntegration0:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0,
    generatedPCCPackexpConcreteFinalIntegration0Accepted:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0Accepted,
    generatedPCCPackexpConcreteFinalIntegration0Checker:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0Checker,
    generatedPCCPackexpConcreteFinalIntegration0Digest:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0Digest,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAGDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAGDigest,
    generatedPCCPackexpConcreteFinalIntegration0MaterializedFinalIntegrationDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0MaterializedFinalIntegrationDigest,
    generatedPCCPackexpConcreteFinalIntegration0GPackDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0GPackDigest,
    generatedPCCPackexpConcreteFinalIntegration0RowFamGDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0RowFamGDigest,
    generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationDigest,
    generatedPCCPackexpConcreteFinalIntegration0FinalTheoremDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0FinalTheoremDigest,
    generatedPCCPackexpConcreteFinalIntegration0RowFamFinalDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0RowFamFinalDigest,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteLinksDigest:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteLinksDigest,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAG:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAG,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteKBundle:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteKBundle,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteRows:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteRows,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteLocalPackages:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteLocalPackages,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalFirewalls:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalFirewalls,
    generatedPCCPackexpConcreteFinalIntegration0KBundleKernelRuleCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0KBundleKernelRuleCoverageComplete,
    generatedPCCPackexpConcreteFinalIntegration0KBundleSigmaProofRefsResolve:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0KBundleSigmaProofRefsResolve,
    generatedPCCPackexpConcreteFinalIntegration0KBundleReflectionProofRefsResolve:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0KBundleReflectionProofRefsResolve,
    generatedPCCPackexpConcreteFinalIntegration0GPackFieldCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0GPackFieldCoverageComplete,
    generatedPCCPackexpConcreteFinalIntegration0RowFamGCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0RowFamGCoverageComplete,
    generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationUsesGPack:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationUsesGPack,
    generatedPCCPackexpConcreteFinalIntegration0RowFamGUsesGPack:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0RowFamGUsesGPack,
    generatedPCCPackexpConcreteFinalIntegration0FinalTheoremUsesFinalIntegration:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0FinalTheoremUsesFinalIntegration,
    generatedPCCPackexpConcreteFinalIntegration0RowFamFinalUsesFinalTheorem:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0RowFamFinalUsesFinalTheorem,
    generatedPCCPackexpConcreteFinalIntegration0FinalMatchUsesGPack:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0FinalMatchUsesGPack,
    generatedPCCPackexpConcreteFinalIntegration0SATDecisionUsesGPack:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0SATDecisionUsesGPack,
    generatedPCCPackexpConcreteFinalIntegration0SyntheticMarkerCount:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0SyntheticMarkerCount,
    generatedPCCPackexpConcreteFinalIntegration0ForbiddenMarkerCount:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0ForbiddenMarkerCount,
    generatedPCCPackexpConcreteFinalIntegration0NoForbiddenMarkers:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0NoForbiddenMarkers,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToGeneratedGlobalProofDAG:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToGeneratedGlobalProofDAG,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToGPack:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToGPack,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamG:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamG,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalIntegration:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalIntegration,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalTheorem:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalTheorem,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamFinal:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamFinal,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToPCCPack:
      concreteCertificateChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToPCCPack,

    generatedPCCPackexpCheckPCCPackexp0:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0,
    generatedPCCPackexpCheckPCCPackexp0Accepted:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0Accepted,
    generatedPCCPackexpCheckPCCPackexp0Checker:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0Checker,
    generatedPCCPackexpCheckPCCPackexp0Digest:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0Digest,
    generatedPCCPackexpCheckPCCPackexp0MaterializedPath:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0MaterializedPath,
    generatedPCCPackexpCheckPCCPackexp0SyntheticRunAll:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0SyntheticRunAll,
    generatedPCCPackexpCheckPCCPackexp0PackageKind:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PackageKind,
    generatedPCCPackexpCheckPCCPackexp0MaterializedPCCPackKind:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0MaterializedPCCPackKind,
    generatedPCCPackexpCheckPCCPackexp0PCCPackDigest:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackDigest,
    generatedPCCPackexpCheckPCCPackexp0MaterializedPCCPackDigest:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0MaterializedPCCPackDigest,
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordDigest:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordDigest,
    generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageDigest:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageDigest,
    generatedPCCPackexpCheckPCCPackexp0PublicConclusionOnlyAfterAcceptRun:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PublicConclusionOnlyAfterAcceptRun,
    generatedPCCPackexpCheckPCCPackexp0PublicConclusionEmitted:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PublicConclusionEmitted,
    generatedPCCPackexpCheckPCCPackexp0NoPrematurePublicConclusion:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0NoPrematurePublicConclusion,
    generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConditional:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConditional,
    generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryAntecedent:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryAntecedent,
    generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConsequent:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConsequent,
    generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication,
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPack:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcretePCCPack,
    generatedPCCPackexpCheckPCCPackexp0ConcreteKBundle:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcreteKBundle,
    generatedPCCPackexpCheckPCCPackexp0ConcreteHardCheck:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcreteHardCheck,
    generatedPCCPackexpCheckPCCPackexp0ConcreteRows:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcreteRows,
    generatedPCCPackexpCheckPCCPackexp0ConcreteLocalPackages:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcreteLocalPackages,
    generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalFirewalls:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalFirewalls,
    generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalProofDAG:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalProofDAG,
    generatedPCCPackexpCheckPCCPackexp0ConcreteFinalIntegration:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcreteFinalIntegration,
    generatedPCCPackexpCheckPCCPackexp0KBundleCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0KBundleCoverageComplete,
    generatedPCCPackexpCheckPCCPackexp0HardCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0HardCoverageComplete,
    generatedPCCPackexpCheckPCCPackexp0FinalIntegrationCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0FinalIntegrationCoverageComplete,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToKBundle:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToKBundle,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToHardCheck:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToHardCheck,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToRows:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToRows,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToLocalPackages:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToLocalPackages,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGlobalFirewalls:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGlobalFirewalls,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGlobalProofDAG:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGlobalProofDAG,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGPack:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGPack,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToFinalIntegration:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToFinalIntegration,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToFinalTheorem:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToFinalTheorem,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkageComplete:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkageComplete,
    generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageComplete:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageComplete,
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordKind:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordKind,
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordAccepted:
      concreteCertificateChain.generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordAccepted,

    kBundleEnvelopeKind: concreteCertificateChain.kBundleEnvelopeKind,
    hardEnvelopeKind: concreteCertificateChain.hardEnvelopeKind,
    finalIntegrationEnvelopeKind: concreteCertificateChain.finalIntegrationEnvelopeKind,

    kBundleCoverageDigest: concreteCertificateChain.kBundleCoverageDigest,
    hardCoverageDigest: concreteCertificateChain.hardCoverageDigest,
    finalIntegrationLinksDigest: concreteCertificateChain.finalIntegrationLinksDigest,

    finalCertificateUsesConcreteAcceptRun: concreteCertificateChain.finalCertificateUsesConcreteAcceptRun,
    certificatePccPackDigestMatchesConcreteRun: concreteCertificateChain.certificatePccPackDigestMatchesConcreteRun,
    certificateAcceptRunDigestMatchesConcreteRun: concreteCertificateChain.certificateAcceptRunDigestMatchesConcreteRun,
    certificateFinalVerdictDigestMatchesRecord: concreteCertificateChain.certificateFinalVerdictDigestMatchesRecord,
    publicTheoremMatchesAcceptedFinalVerdict: concreteCertificateChain.publicTheoremMatchesAcceptedFinalVerdict,

    concreteFinalCertificateEnvelopeDigest,
    statusFinalCertificateEnvelopeDigest,
    statusUsesConcreteFinalCertificate: sameDigestHex0(
      concreteFinalCertificateEnvelopeDigest,
      statusFinalCertificateEnvelopeDigest,
    ),

    certificateDigest,
    publicStatusCertificateDigest,
    publicStatusCertificateDigestMatchesConcrete: sameDigestHex0(
      certificateDigest,
      publicStatusCertificateDigest,
    ),

    finalVerdictRecordDigest,
    publicStatusFinalVerdictDigest,
    publicStatusFinalVerdictDigestMatchesConcrete: sameDigestHex0(
      finalVerdictRecordDigest,
      publicStatusFinalVerdictDigest,
    ),

    acceptRunDigest,
    publicStatusAcceptRunDigest,
    publicStatusAcceptRunDigestMatchesConcrete: sameDigestHex0(
      acceptRunDigest,
      publicStatusAcceptRunDigest,
    ),

    pccPackDigest,
    publicStatusPccPackDigest,
    publicStatusPccPackDigestMatchesConcrete: sameDigestHex0(
      pccPackDigest,
      publicStatusPccPackDigest,
    ),

    publicConclusion: publicStatus?.publicConclusion ?? null,
    publicConclusionMatchesCertificate: samePublicConclusion0(
      publicStatus?.publicConclusion ?? null,
      certificate?.publicTheorem ?? null,
    ),
    publicConclusionMatchesFinalVerdict: samePublicConclusion0(
      publicStatus?.publicConclusion ?? null,
      finalVerdict?.NF?.publicConclusion ?? finalVerdict?.nf?.publicConclusion ?? null,
    ),

    publicConclusionEmitted: publicStatus?.publicConclusionEmitted === true,
    status: publicStatus?.status ?? null,
    verdict: publicStatus?.verdict ?? null,
    canonicalByteRoots: publicStatus?.canonicalByteRoots ?? null,
    acceptanceTranscript: publicStatus?.acceptanceTranscript ?? null,
  };
}

export async function CheckConcreteFinalCertificatePublicStatus0(
  input,
  config = makeConcreteFinalCertificatePublicStatusConfig0(),
) {
  const checker = 'CheckConcreteFinalCertificatePublicStatus0';
  const ledger = [];
  const cfg = makeConcreteFinalCertificatePublicStatusConfig0(config);
  const envelope = input;

  const cfgCheck = validateConfig0(cfg);

  ledger.push({
    phase: 'config',
    status: cfgCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(cfgCheck.nf ?? cfgCheck.witness ?? null),
  });

  if (!cfgCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.config`,
      path: cfgCheck.path,
      witness: cfgCheck.witness,
      ledger,
    });
  }

  const shape = validateShape0(envelope);

  ledger.push({
    phase: 'shape',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  if (cfg.checkConcreteFinalCertificate === true) {
    const record = await CheckConcreteMaterializedFinalCertificate0(
      envelope.ConcreteFinalCertificateEnvelope,
      cfg.concreteFinalCertificateConfig ?? {},
    );
    const result = recordToValidation0(record, ['ConcreteFinalCertificateEnvelope']);

    ledger.push({
      phase: 'CheckConcreteMaterializedFinalCertificate0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteFinalCertificate`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkFinalCertificatePublicStatus === true) {
    const record = await CheckFinalCertificatePublicStatus0(
      envelope.FinalCertificatePublicStatusEnvelope,
      cfg.finalCertificatePublicStatusConfig ?? {},
    );
    const result = recordToValidation0(record, ['FinalCertificatePublicStatusEnvelope']);

    ledger.push({
      phase: 'CheckFinalCertificatePublicStatus0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.FinalCertificatePublicStatus`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const recomputedChain = summarizeConcreteFinalCertificatePublicStatusChain0({
    concreteFinalCertificateEnvelope: envelope.ConcreteFinalCertificateEnvelope,
    finalCertificatePublicStatusEnvelope: envelope.FinalCertificatePublicStatusEnvelope,
  });

  if (cfg.checkConcreteChain === true) {
    const chain = validateConcretePublicStatusChain0(envelope.ConcreteChain, recomputedChain);

    ledger.push({
      phase: 'concreteChain',
      status: chain.ok ? 'pass' : 'fail',
      digest: digestCanonical0(chain.nf ?? chain.witness ?? null),
    });

    if (!chain.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.concreteChain`,
        path: chain.path,
        witness: chain.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope);

    ledger.push({
      phase: 'jsonMaterialized',
      status: json.ok ? 'pass' : 'fail',
      digest: digestCanonical0(json.nf ?? json.witness ?? null),
    });

    if (!json.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.json`,
        path: json.path,
        witness: json.witness,
        ledger,
      });
    }
  }

  const markerInventory = collectFixtureMarkers0(envelope, ['ConcreteFinalCertificatePublicStatus0']);

  ledger.push({
    phase: 'fixtureMarkerInventory',
    status: 'pass',
    digest: digestCanonical0(markerInventory),
  });

  if (cfg.rejectFixtureMarkers === true) {
    const markers = validateNoForbiddenFixtureMarkers0(markerInventory, cfg);

    ledger.push({
      phase: 'fixtureMarkers',
      status: markers.ok ? 'pass' : 'fail',
      digest: digestCanonical0(markers.nf ?? markers.witness ?? null),
    });

    if (!markers.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.fixtureMarkers`,
        path: markers.path,
        witness: markers.witness,
        ledger,
      });
    }
  }

  if (cfg.checkLinkage === true) {
    const linkage = validateLinkage0(envelope, recomputedChain);

    ledger.push({
      phase: 'linkage',
      status: linkage.ok ? 'pass' : 'fail',
      digest: digestCanonical0(linkage.nf ?? linkage.witness ?? null),
    });

    if (!linkage.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.linkage`,
        path: linkage.path,
        witness: linkage.witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'ConcreteFinalCertificatePublicStatus0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,

    concreteRows: recomputedChain.concreteRows,
    concreteLocalPackages: recomputedChain.concreteLocalPackages,
    concreteGlobalFirewalls: recomputedChain.concreteGlobalFirewalls,
    concreteGlobalProofDAG: recomputedChain.concreteGlobalProofDAG,

    concreteKBundle: recomputedChain.concreteKBundle,
    kBundleKernelRuleCoverageComplete: recomputedChain.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: recomputedChain.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: recomputedChain.kBundleReflectionProofRefsResolve,

    concreteHardCheck: recomputedChain.concreteHardCheck,
    hardCheckerCoverageComplete: recomputedChain.hardCheckerCoverageComplete,
    hardRowKeyCoverageComplete: recomputedChain.hardRowKeyCoverageComplete,
    hardRoutePriorityComplete: recomputedChain.hardRoutePriorityComplete,
    hardProofRefPolicyComplete: recomputedChain.hardProofRefPolicyComplete,
    hardHashDisciplineComplete: recomputedChain.hardHashDisciplineComplete,
    hardNoMinCoverageComplete: recomputedChain.hardNoMinCoverageComplete,
    hardImportPolicyComplete: recomputedChain.hardImportPolicyComplete,
    hardReflectionPolicyComplete: recomputedChain.hardReflectionPolicyComplete,
    hardBoundsPolicyComplete: recomputedChain.hardBoundsPolicyComplete,
    hardDiagnosticsPolicyComplete: recomputedChain.hardDiagnosticsPolicyComplete,

    concreteFinalIntegration: recomputedChain.concreteFinalIntegration,
    finalIntegrationConcreteGlobalProofDAG: recomputedChain.finalIntegrationConcreteGlobalProofDAG,
    finalIntegrationGPackFieldCoverageComplete: recomputedChain.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: recomputedChain.finalIntegrationRowFamGCoverageComplete,
    finalIntegrationUsesGPack: recomputedChain.finalIntegrationUsesGPack,
    rowFamGUsesGPack: recomputedChain.rowFamGUsesGPack,
    finalTheoremUsesFinalIntegration: recomputedChain.finalTheoremUsesFinalIntegration,
    rowFamFinalUsesFinalTheorem: recomputedChain.rowFamFinalUsesFinalTheorem,
    finalMatchUsesGPack: recomputedChain.finalMatchUsesGPack,
    satDecisionUsesGPack: recomputedChain.satDecisionUsesGPack,

    concretePCCPack: recomputedChain.concretePCCPack,
    concretePCCPackCoverageDigest: recomputedChain.concretePCCPackCoverageDigest,
    pccPackPublicConclusionOnlyAfterAcceptRun: recomputedChain.pccPackPublicConclusionOnlyAfterAcceptRun,
    pccPackLinkedToKBundle: recomputedChain.pccPackLinkedToKBundle,
    pccPackLinkedToHardCheck: recomputedChain.pccPackLinkedToHardCheck,
    pccPackLinkedToRows: recomputedChain.pccPackLinkedToRows,
    pccPackLinkedToLocalPackages: recomputedChain.pccPackLinkedToLocalPackages,
    pccPackLinkedToGlobalFirewalls: recomputedChain.pccPackLinkedToGlobalFirewalls,
    pccPackLinkedToGlobalProofDAG: recomputedChain.pccPackLinkedToGlobalProofDAG,
    pccPackLinkedToGPack: recomputedChain.pccPackLinkedToGPack,
    pccPackLinkedToFinalIntegration: recomputedChain.pccPackLinkedToFinalIntegration,
    pccPackLinkedToFinalTheorem: recomputedChain.pccPackLinkedToFinalTheorem,

    checkPCCPackexpRecordPresent: recomputedChain.checkPCCPackexpRecordPresent,
    checkPCCPackexpRecordAccepted: recomputedChain.checkPCCPackexpRecordAccepted,
    checkPCCPackexpRecordChecker: recomputedChain.checkPCCPackexpRecordChecker,
    checkPCCPackexpRecordDigest: recomputedChain.checkPCCPackexpRecordDigest,
    checkPCCPackexpRecordDigestMatchesNF: recomputedChain.checkPCCPackexpRecordDigestMatchesNF,
    checkPCCPackexpRecordConcretePCCPack: recomputedChain.checkPCCPackexpRecordConcretePCCPack,
    checkPCCPackexpRecordPccPackDigest: recomputedChain.checkPCCPackexpRecordPccPackDigest,
    checkPCCPackexpRecordPccPackDigestMatchesConcreteRun: recomputedChain.checkPCCPackexpRecordPccPackDigestMatchesConcreteRun,
    checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: recomputedChain.checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun,
    checkPCCPackexpRecordPublicConclusionNotEmitted: recomputedChain.checkPCCPackexpRecordPublicConclusionNotEmitted,
    checkPCCPackexpRecordClaimBoundaryConditional: recomputedChain.checkPCCPackexpRecordClaimBoundaryConditional,

    generatedPCCPackexpEnvelopePresent: recomputedChain.generatedPCCPackexpEnvelopePresent,
    generatedPCCPackexpEnvelopeDigest: recomputedChain.generatedPCCPackexpEnvelopeDigest,
    generatedPCCPackexpGenCallGeneratePCCPack: recomputedChain.generatedPCCPackexpGenCallGeneratePCCPack,
    generatedPCCPackexpCoreOnly: recomputedChain.generatedPCCPackexpCoreOnly,
    generatedPCCPackexpExcludesAcceptRun: recomputedChain.generatedPCCPackexpExcludesAcceptRun,
    generatedPCCPackexpPackageMatchesConcreteRun: recomputedChain.generatedPCCPackexpPackageMatchesConcreteRun,
    generatedPCCPackexpCheckRecordMatchesConcreteRun: recomputedChain.generatedPCCPackexpCheckRecordMatchesConcreteRun,
    generatedPCCPackexpCheckRecordAccepted: recomputedChain.generatedPCCPackexpCheckRecordAccepted,
    generatedPCCPackexpCheckRecordChecker: recomputedChain.generatedPCCPackexpCheckRecordChecker,
    generatedPCCPackexpCheckRecordDigest: recomputedChain.generatedPCCPackexpCheckRecordDigest,
    generatedPCCPackexpCheckRecordDigestMatchesNF: recomputedChain.generatedPCCPackexpCheckRecordDigestMatchesNF,
    generatedPCCPackexpCheckRecordClaimBoundaryConditional: recomputedChain.generatedPCCPackexpCheckRecordClaimBoundaryConditional,
    generatedPCCPackexpLinkageGeneratedPackageDigestMatches: recomputedChain.generatedPCCPackexpLinkageGeneratedPackageDigestMatches,
    generatedPCCPackexpLinkageCheckRecordDigestMatches: recomputedChain.generatedPCCPackexpLinkageCheckRecordDigestMatches,

    checkGeneratedPCCPackexpRecordPresent: recomputedChain.checkGeneratedPCCPackexpRecordPresent,
    checkGeneratedPCCPackexpRecordAccepted: recomputedChain.checkGeneratedPCCPackexpRecordAccepted,
    checkGeneratedPCCPackexpRecordChecker: recomputedChain.checkGeneratedPCCPackexpRecordChecker,
    checkGeneratedPCCPackexpRecordDigest: recomputedChain.checkGeneratedPCCPackexpRecordDigest,
    checkGeneratedPCCPackexpRecordDigestMatchesNF:
      recomputedChain.checkGeneratedPCCPackexpRecordDigestMatchesNF,
    checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope:
      recomputedChain.checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope,
    checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope:
      recomputedChain.checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope,

    generatedPCCPackexpBoot0: recomputedChain.generatedPCCPackexpBoot0,
    generatedPCCPackexpBoot0Accepted: recomputedChain.generatedPCCPackexpBoot0Accepted,
    generatedPCCPackexpBoot0Kind: recomputedChain.generatedPCCPackexpBoot0Kind,
    generatedPCCPackexpBoot0Digest: recomputedChain.generatedPCCPackexpBoot0Digest,
    generatedPCCPackexpBoot0CheckDigest: recomputedChain.generatedPCCPackexpBoot0CheckDigest,
    generatedPCCPackexpBoot0CanonicalByteDigest:
      recomputedChain.generatedPCCPackexpBoot0CanonicalByteDigest,
    generatedPCCPackexpBoot0RowCount: recomputedChain.generatedPCCPackexpBoot0RowCount,
    generatedPCCPackexpBoot0KernelRuleCount: recomputedChain.generatedPCCPackexpBoot0KernelRuleCount,
    generatedPCCPackexpBoot0JsonMaterialized:
      recomputedChain.generatedPCCPackexpBoot0JsonMaterialized,
    generatedPCCPackexpBoot0NoFixtureMarkers:
      recomputedChain.generatedPCCPackexpBoot0NoFixtureMarkers,
    generatedPCCPackexpBoot0BootBatchDigest:
      recomputedChain.generatedPCCPackexpBoot0BootBatchDigest,
    generatedPCCPackexpBoot0BootAuditDigest:
      recomputedChain.generatedPCCPackexpBoot0BootAuditDigest,
    generatedPCCPackexpBoot0LinkedToPCCPack:
      recomputedChain.generatedPCCPackexpBoot0LinkedToPCCPack,
    generatedPCCPackexpBoot0LinkedToCoreDigestMap:
      recomputedChain.generatedPCCPackexpBoot0LinkedToCoreDigestMap,
    generatedPCCPackexpBoot0DigestMatchesGeneratedPackage:
      recomputedChain.generatedPCCPackexpBoot0DigestMatchesGeneratedPackage,
    generatedPCCPackexpBoot0DigestMatchesCoreDigestMap:
      recomputedChain.generatedPCCPackexpBoot0DigestMatchesCoreDigestMap,

    generatedPCCPackexpBoot0B0Accepted:
      recomputedChain.generatedPCCPackexpBoot0B0Accepted,
    generatedPCCPackexpBoot0B0Digest:
      recomputedChain.generatedPCCPackexpBoot0B0Digest,
    generatedPCCPackexpBoot0B0CoverageDigest:
      recomputedChain.generatedPCCPackexpBoot0B0CoverageDigest,
    generatedPCCPackexpBoot0B0FamilyCount:
      recomputedChain.generatedPCCPackexpBoot0B0FamilyCount,
    generatedPCCPackexpBoot0B0RequiredFamilyCount:
      recomputedChain.generatedPCCPackexpBoot0B0RequiredFamilyCount,
    generatedPCCPackexpBoot0B0Families:
      recomputedChain.generatedPCCPackexpBoot0B0Families,
    generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent:
      recomputedChain.generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent,
    generatedPCCPackexpBoot0B0CoversIface:
      recomputedChain.generatedPCCPackexpBoot0B0CoversIface,
    generatedPCCPackexpBoot0B0CoversSched:
      recomputedChain.generatedPCCPackexpBoot0B0CoversSched,
    generatedPCCPackexpBoot0B0CoversNF:
      recomputedChain.generatedPCCPackexpBoot0B0CoversNF,
    generatedPCCPackexpBoot0B0CoversTruthEval:
      recomputedChain.generatedPCCPackexpBoot0B0CoversTruthEval,
    generatedPCCPackexpBoot0B0CoversRel:
      recomputedChain.generatedPCCPackexpBoot0B0CoversRel,
    generatedPCCPackexpBoot0B0CoversCharge:
      recomputedChain.generatedPCCPackexpBoot0B0CoversCharge,
    generatedPCCPackexpBoot0B0CoversObl:
      recomputedChain.generatedPCCPackexpBoot0B0CoversObl,
    generatedPCCPackexpBoot0B0CoversArith:
      recomputedChain.generatedPCCPackexpBoot0B0CoversArith,
    generatedPCCPackexpBoot0B0CoversMode:
      recomputedChain.generatedPCCPackexpBoot0B0CoversMode,
    generatedPCCPackexpBoot0B0CoversRoute:
      recomputedChain.generatedPCCPackexpBoot0B0CoversRoute,
    generatedPCCPackexpBoot0B0CoversHash:
      recomputedChain.generatedPCCPackexpBoot0B0CoversHash,
    generatedPCCPackexpBoot0B0CoversImport:
      recomputedChain.generatedPCCPackexpBoot0B0CoversImport,

    generatedPCCPackexpKernelSeed0:
      recomputedChain.generatedPCCPackexpKernelSeed0,
    generatedPCCPackexpKernelSeed0Accepted:
      recomputedChain.generatedPCCPackexpKernelSeed0Accepted,
    generatedPCCPackexpKernelSeed0Kind:
      recomputedChain.generatedPCCPackexpKernelSeed0Kind,
    generatedPCCPackexpKernelSeed0Digest:
      recomputedChain.generatedPCCPackexpKernelSeed0Digest,
    generatedPCCPackexpKernelSeed0RuleCount:
      recomputedChain.generatedPCCPackexpKernelSeed0RuleCount,
    generatedPCCPackexpKernelSeed0RequiredRuleCount:
      recomputedChain.generatedPCCPackexpKernelSeed0RequiredRuleCount,
    generatedPCCPackexpKernelSeed0Rules:
      recomputedChain.generatedPCCPackexpKernelSeed0Rules,
    generatedPCCPackexpKernelSeed0AllRequiredRulesPresent:
      recomputedChain.generatedPCCPackexpKernelSeed0AllRequiredRulesPresent,
    generatedPCCPackexpKernelSeed0HasEq:
      recomputedChain.generatedPCCPackexpKernelSeed0HasEq,
    generatedPCCPackexpKernelSeed0HasSubst:
      recomputedChain.generatedPCCPackexpKernelSeed0HasSubst,
    generatedPCCPackexpKernelSeed0HasRecord:
      recomputedChain.generatedPCCPackexpKernelSeed0HasRecord,
    generatedPCCPackexpKernelSeed0HasDAGInd:
      recomputedChain.generatedPCCPackexpKernelSeed0HasDAGInd,
    generatedPCCPackexpKernelSeed0HasLedgerInd:
      recomputedChain.generatedPCCPackexpKernelSeed0HasLedgerInd,
    generatedPCCPackexpKernelSeed0HasOblTopoInd:
      recomputedChain.generatedPCCPackexpKernelSeed0HasOblTopoInd,
    generatedPCCPackexpKernelSeed0HasTraceInd:
      recomputedChain.generatedPCCPackexpKernelSeed0HasTraceInd,
    generatedPCCPackexpKernelSeed0HasFiniteExhaust:
      recomputedChain.generatedPCCPackexpKernelSeed0HasFiniteExhaust,
    generatedPCCPackexpKernelSeed0HasDPInd:
      recomputedChain.generatedPCCPackexpKernelSeed0HasDPInd,
    generatedPCCPackexpKernelSeed0HasHall:
      recomputedChain.generatedPCCPackexpKernelSeed0HasHall,
    generatedPCCPackexpKernelSeed0HasRankInd:
      recomputedChain.generatedPCCPackexpKernelSeed0HasRankInd,
    generatedPCCPackexpKernelSeed0HasMinCounterexample:
      recomputedChain.generatedPCCPackexpKernelSeed0HasMinCounterexample,
    generatedPCCPackexpKernelSeed0HasIntArith:
      recomputedChain.generatedPCCPackexpKernelSeed0HasIntArith,
    generatedPCCPackexpKernelSeed0HasTransport:
      recomputedChain.generatedPCCPackexpKernelSeed0HasTransport,
    generatedPCCPackexpKernelSeed0HasTruthVec:
      recomputedChain.generatedPCCPackexpKernelSeed0HasTruthVec,
    generatedPCCPackexpKernelSeed0HasFiniteRel:
      recomputedChain.generatedPCCPackexpKernelSeed0HasFiniteRel,
    generatedPCCPackexpKernelSeed0ProofNodeKindCount:
      recomputedChain.generatedPCCPackexpKernelSeed0ProofNodeKindCount,
    generatedPCCPackexpKernelSeed0ProofNodeKinds:
      recomputedChain.generatedPCCPackexpKernelSeed0ProofNodeKinds,
    generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent:
      recomputedChain.generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent,
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque:
      recomputedChain.generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque,
    generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic:
      recomputedChain.generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic,
    generatedPCCPackexpKernelSeed0ProofRefsHashIndependent:
      recomputedChain.generatedPCCPackexpKernelSeed0ProofRefsHashIndependent,
    generatedPCCPackexpKernelSeed0PiBootDigestMatches:
      recomputedChain.generatedPCCPackexpKernelSeed0PiBootDigestMatches,

    generatedPCCPackexpCodec0:
      recomputedChain.generatedPCCPackexpCodec0,
    generatedPCCPackexpCodec0Accepted:
      recomputedChain.generatedPCCPackexpCodec0Accepted,
    generatedPCCPackexpCodec0Kind:
      recomputedChain.generatedPCCPackexpCodec0Kind,
    generatedPCCPackexpCodec0Digest:
      recomputedChain.generatedPCCPackexpCodec0Digest,
    generatedPCCPackexpCodec0Canonical:
      recomputedChain.generatedPCCPackexpCodec0Canonical,
    generatedPCCPackexpCodec0NaturalEncoding:
      recomputedChain.generatedPCCPackexpCodec0NaturalEncoding,
    generatedPCCPackexpCodec0NaturalEncodingCanonical:
      recomputedChain.generatedPCCPackexpCodec0NaturalEncodingCanonical,
    generatedPCCPackexpCodec0IntegerEncoding:
      recomputedChain.generatedPCCPackexpCodec0IntegerEncoding,
    generatedPCCPackexpCodec0IntegerEncodingCanonical:
      recomputedChain.generatedPCCPackexpCodec0IntegerEncodingCanonical,
    generatedPCCPackexpCodec0StringEncoding:
      recomputedChain.generatedPCCPackexpCodec0StringEncoding,
    generatedPCCPackexpCodec0StringEncodingCanonical:
      recomputedChain.generatedPCCPackexpCodec0StringEncodingCanonical,
    generatedPCCPackexpCodec0TopLevelConsumesAllBytes:
      recomputedChain.generatedPCCPackexpCodec0TopLevelConsumesAllBytes,
    generatedPCCPackexpCodec0NormalFormSerialization:
      recomputedChain.generatedPCCPackexpCodec0NormalFormSerialization,
    generatedPCCPackexpCodec0NormalFormSerializationCanonical:
      recomputedChain.generatedPCCPackexpCodec0NormalFormSerializationCanonical,
    generatedPCCPackexpCodec0PiBootDigestMatches:
      recomputedChain.generatedPCCPackexpCodec0PiBootDigestMatches,

    generatedPCCPackexpDigest0:
      recomputedChain.generatedPCCPackexpDigest0,
    generatedPCCPackexpDigest0Accepted:
      recomputedChain.generatedPCCPackexpDigest0Accepted,
    generatedPCCPackexpDigest0Kind:
      recomputedChain.generatedPCCPackexpDigest0Kind,
    generatedPCCPackexpDigest0Digest:
      recomputedChain.generatedPCCPackexpDigest0Digest,
    generatedPCCPackexpDigest0Alg:
      recomputedChain.generatedPCCPackexpDigest0Alg,
    generatedPCCPackexpDigest0AlgSHA256:
      recomputedChain.generatedPCCPackexpDigest0AlgSHA256,
    generatedPCCPackexpDigest0Bytes:
      recomputedChain.generatedPCCPackexpDigest0Bytes,
    generatedPCCPackexpDigest0BytesCanonicalJson:
      recomputedChain.generatedPCCPackexpDigest0BytesCanonicalJson,
    generatedPCCPackexpDigest0EqualityNotObjectEquality:
      recomputedChain.generatedPCCPackexpDigest0EqualityNotObjectEquality,
    generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup:
      recomputedChain.generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup,
    generatedPCCPackexpDigest0PiBootDigestMatches:
      recomputedChain.generatedPCCPackexpDigest0PiBootDigestMatches,

    generatedPCCPackexpIfaceDict0:
      recomputedChain.generatedPCCPackexpIfaceDict0,
    generatedPCCPackexpIfaceDict0Accepted:
      recomputedChain.generatedPCCPackexpIfaceDict0Accepted,
    generatedPCCPackexpIfaceDict0Kind:
      recomputedChain.generatedPCCPackexpIfaceDict0Kind,
    generatedPCCPackexpIfaceDict0Digest:
      recomputedChain.generatedPCCPackexpIfaceDict0Digest,
    generatedPCCPackexpIfaceDict0ForbiddenSymbolCount:
      recomputedChain.generatedPCCPackexpIfaceDict0ForbiddenSymbolCount,
    generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent:
      recomputedChain.generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent,
    generatedPCCPackexpIfaceDict0NoExecutableMinSymbols:
      recomputedChain.generatedPCCPackexpIfaceDict0NoExecutableMinSymbols,
    generatedPCCPackexpIfaceDict0PublicConstructorsPresent:
      recomputedChain.generatedPCCPackexpIfaceDict0PublicConstructorsPresent,
    generatedPCCPackexpIfaceDict0CriticalKindsPresent:
      recomputedChain.generatedPCCPackexpIfaceDict0CriticalKindsPresent,
    generatedPCCPackexpIfaceDict0RouteTokensPresent:
      recomputedChain.generatedPCCPackexpIfaceDict0RouteTokensPresent,
    generatedPCCPackexpIfaceDict0PiBootDigestMatches:
      recomputedChain.generatedPCCPackexpIfaceDict0PiBootDigestMatches,

    generatedPCCPackexpSched0:
      recomputedChain.generatedPCCPackexpSched0,
    generatedPCCPackexpSched0Accepted:
      recomputedChain.generatedPCCPackexpSched0Accepted,
    generatedPCCPackexpSched0Kind:
      recomputedChain.generatedPCCPackexpSched0Kind,
    generatedPCCPackexpSched0Digest:
      recomputedChain.generatedPCCPackexpSched0Digest,
    generatedPCCPackexpSched0CoreMatchesExpected:
      recomputedChain.generatedPCCPackexpSched0CoreMatchesExpected,
    generatedPCCPackexpSched0CoreB0:
      recomputedChain.generatedPCCPackexpSched0CoreB0,
    generatedPCCPackexpSched0CoreK0:
      recomputedChain.generatedPCCPackexpSched0CoreK0,
    generatedPCCPackexpSched0CoreR0:
      recomputedChain.generatedPCCPackexpSched0CoreR0,
    generatedPCCPackexpSched0CoreH0:
      recomputedChain.generatedPCCPackexpSched0CoreH0,
    generatedPCCPackexpSched0CoreO0:
      recomputedChain.generatedPCCPackexpSched0CoreO0,
    generatedPCCPackexpSched0CoreRel0:
      recomputedChain.generatedPCCPackexpSched0CoreRel0,
    generatedPCCPackexpSched0ScaleFactorsPresent:
      recomputedChain.generatedPCCPackexpSched0ScaleFactorsPresent,
    generatedPCCPackexpSched0SelectorBoundsPresent:
      recomputedChain.generatedPCCPackexpSched0SelectorBoundsPresent,
    generatedPCCPackexpSched0SelectorBoundBH:
      recomputedChain.generatedPCCPackexpSched0SelectorBoundBH,
    generatedPCCPackexpSched0SelectorBoundBTheta:
      recomputedChain.generatedPCCPackexpSched0SelectorBoundBTheta,
    generatedPCCPackexpSched0PolynomialExponent:
      recomputedChain.generatedPCCPackexpSched0PolynomialExponent,
    generatedPCCPackexpSched0PiBootDigestMatches:
      recomputedChain.generatedPCCPackexpSched0PiBootDigestMatches,

    generatedPCCPackexpByteLang0:
      recomputedChain.generatedPCCPackexpByteLang0,
    generatedPCCPackexpByteLang0Accepted:
      recomputedChain.generatedPCCPackexpByteLang0Accepted,
    generatedPCCPackexpByteLang0Kind:
      recomputedChain.generatedPCCPackexpByteLang0Kind,
    generatedPCCPackexpByteLang0Digest:
      recomputedChain.generatedPCCPackexpByteLang0Digest,
    generatedPCCPackexpByteLang0TagCount:
      recomputedChain.generatedPCCPackexpByteLang0TagCount,
    generatedPCCPackexpByteLang0TagsUnique:
      recomputedChain.generatedPCCPackexpByteLang0TagsUnique,
    generatedPCCPackexpByteLang0RequiredTagsPresent:
      recomputedChain.generatedPCCPackexpByteLang0RequiredTagsPresent,
    generatedPCCPackexpByteLang0SortCount:
      recomputedChain.generatedPCCPackexpByteLang0SortCount,
    generatedPCCPackexpByteLang0RequiredSortsPresent:
      recomputedChain.generatedPCCPackexpByteLang0RequiredSortsPresent,
    generatedPCCPackexpByteLang0ConstructorCount:
      recomputedChain.generatedPCCPackexpByteLang0ConstructorCount,
    generatedPCCPackexpByteLang0RequiredConstructorsPresent:
      recomputedChain.generatedPCCPackexpByteLang0RequiredConstructorsPresent,
    generatedPCCPackexpByteLang0RecordCount:
      recomputedChain.generatedPCCPackexpByteLang0RecordCount,
    generatedPCCPackexpByteLang0RequiredRecordAritiesPresent:
      recomputedChain.generatedPCCPackexpByteLang0RequiredRecordAritiesPresent,
    generatedPCCPackexpByteLang0PiBootDigestMatches:
      recomputedChain.generatedPCCPackexpByteLang0PiBootDigestMatches,

    generatedPCCPackexpBootAudit0:
      recomputedChain.generatedPCCPackexpBootAudit0,
    generatedPCCPackexpBootAudit0Accepted:
      recomputedChain.generatedPCCPackexpBootAudit0Accepted,
    generatedPCCPackexpBootAudit0Checker:
      recomputedChain.generatedPCCPackexpBootAudit0Checker,
    generatedPCCPackexpBootAudit0Digest:
      recomputedChain.generatedPCCPackexpBootAudit0Digest,
    generatedPCCPackexpBootAudit0DigestMatchesNF:
      recomputedChain.generatedPCCPackexpBootAudit0DigestMatchesNF,
    generatedPCCPackexpBootAudit0NFKind:
      recomputedChain.generatedPCCPackexpBootAudit0NFKind,
    generatedPCCPackexpBootAudit0SuiteId:
      recomputedChain.generatedPCCPackexpBootAudit0SuiteId,
    generatedPCCPackexpBootAudit0CaseCount:
      recomputedChain.generatedPCCPackexpBootAudit0CaseCount,
    generatedPCCPackexpBootAudit0PositiveCount:
      recomputedChain.generatedPCCPackexpBootAudit0PositiveCount,
    generatedPCCPackexpBootAudit0NegativeCount:
      recomputedChain.generatedPCCPackexpBootAudit0NegativeCount,
    generatedPCCPackexpBootAudit0CoversB0Accept:
      recomputedChain.generatedPCCPackexpBootAudit0CoversB0Accept,
    generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject:
      recomputedChain.generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject,
    generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject:
      recomputedChain.generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject,

    generatedPCCPackexpPiBoot0:
      recomputedChain.generatedPCCPackexpPiBoot0,
    generatedPCCPackexpPiBoot0Accepted:
      recomputedChain.generatedPCCPackexpPiBoot0Accepted,
    generatedPCCPackexpPiBoot0Kind:
      recomputedChain.generatedPCCPackexpPiBoot0Kind,
    generatedPCCPackexpPiBoot0Digest:
      recomputedChain.generatedPCCPackexpPiBoot0Digest,
    generatedPCCPackexpPiBoot0Materialized:
      recomputedChain.generatedPCCPackexpPiBoot0Materialized,
    generatedPCCPackexpPiBoot0ExternalJson:
      recomputedChain.generatedPCCPackexpPiBoot0ExternalJson,
    generatedPCCPackexpPiBoot0RefCount:
      recomputedChain.generatedPCCPackexpPiBoot0RefCount,
    generatedPCCPackexpPiBoot0AllBootRefsPresent:
      recomputedChain.generatedPCCPackexpPiBoot0AllBootRefsPresent,
    generatedPCCPackexpPiBoot0RefsMatchBootObjects:
      recomputedChain.generatedPCCPackexpPiBoot0RefsMatchBootObjects,
    generatedPCCPackexpPiBoot0RefsIncludeByteLang0:
      recomputedChain.generatedPCCPackexpPiBoot0RefsIncludeByteLang0,
    generatedPCCPackexpPiBoot0RefsIncludeCodec0:
      recomputedChain.generatedPCCPackexpPiBoot0RefsIncludeCodec0,
    generatedPCCPackexpPiBoot0RefsIncludeDigest0:
      recomputedChain.generatedPCCPackexpPiBoot0RefsIncludeDigest0,
    generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0:
      recomputedChain.generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0,
    generatedPCCPackexpPiBoot0RefsIncludeSched0:
      recomputedChain.generatedPCCPackexpPiBoot0RefsIncludeSched0,
    generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0:
      recomputedChain.generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0,
    generatedPCCPackexpPiBoot0RefsIncludeB0:
      recomputedChain.generatedPCCPackexpPiBoot0RefsIncludeB0,
    generatedPCCPackexpPiBoot0RefsIncludeBootAudit0:
      recomputedChain.generatedPCCPackexpPiBoot0RefsIncludeBootAudit0,

    generatedPCCPackexpConcreteKBundle0:
      recomputedChain.generatedPCCPackexpConcreteKBundle0,
    generatedPCCPackexpConcreteKBundle0Accepted:
      recomputedChain.generatedPCCPackexpConcreteKBundle0Accepted,
    generatedPCCPackexpConcreteKBundle0Checker:
      recomputedChain.generatedPCCPackexpConcreteKBundle0Checker,
    generatedPCCPackexpConcreteKBundle0Digest:
      recomputedChain.generatedPCCPackexpConcreteKBundle0Digest,
    generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest:
      recomputedChain.generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest,
    generatedPCCPackexpConcreteKBundle0BootDigest:
      recomputedChain.generatedPCCPackexpConcreteKBundle0BootDigest,
    generatedPCCPackexpConcreteKBundle0KImplDigest:
      recomputedChain.generatedPCCPackexpConcreteKBundle0KImplDigest,
    generatedPCCPackexpConcreteKBundle0K0Digest:
      recomputedChain.generatedPCCPackexpConcreteKBundle0K0Digest,
    generatedPCCPackexpConcreteKBundle0SigmaDigest:
      recomputedChain.generatedPCCPackexpConcreteKBundle0SigmaDigest,
    generatedPCCPackexpConcreteKBundle0ReflectionDigest:
      recomputedChain.generatedPCCPackexpConcreteKBundle0ReflectionDigest,
    generatedPCCPackexpConcreteKBundle0ProofInventoryDigest:
      recomputedChain.generatedPCCPackexpConcreteKBundle0ProofInventoryDigest,
    generatedPCCPackexpConcreteKBundle0KernelRuleCount:
      recomputedChain.generatedPCCPackexpConcreteKBundle0KernelRuleCount,
    generatedPCCPackexpConcreteKBundle0ConformanceNodeCount:
      recomputedChain.generatedPCCPackexpConcreteKBundle0ConformanceNodeCount,
    generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete:
      recomputedChain.generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete,
    generatedPCCPackexpConcreteKBundle0SigmaTheoremCount:
      recomputedChain.generatedPCCPackexpConcreteKBundle0SigmaTheoremCount,
    generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete:
      recomputedChain.generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete,
    generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve:
      recomputedChain.generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve,
    generatedPCCPackexpConcreteKBundle0ReflectionCount:
      recomputedChain.generatedPCCPackexpConcreteKBundle0ReflectionCount,
    generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete:
      recomputedChain.generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete,
    generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve:
      recomputedChain.generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve,
    generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs:
      recomputedChain.generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs,
    generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols:
      recomputedChain.generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols,
    generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0:
      recomputedChain.generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0,

    generatedPCCPackexpConcreteHard0:
      recomputedChain.generatedPCCPackexpConcreteHard0,
    generatedPCCPackexpConcreteHard0Accepted:
      recomputedChain.generatedPCCPackexpConcreteHard0Accepted,
    generatedPCCPackexpConcreteHard0Checker:
      recomputedChain.generatedPCCPackexpConcreteHard0Checker,
    generatedPCCPackexpConcreteHard0Digest:
      recomputedChain.generatedPCCPackexpConcreteHard0Digest,
    generatedPCCPackexpConcreteHard0MaterializedHardDigest:
      recomputedChain.generatedPCCPackexpConcreteHard0MaterializedHardDigest,
    generatedPCCPackexpConcreteHard0HardCheckDigest:
      recomputedChain.generatedPCCPackexpConcreteHard0HardCheckDigest,
    generatedPCCPackexpConcreteHard0CoverageDigest:
      recomputedChain.generatedPCCPackexpConcreteHard0CoverageDigest,
    generatedPCCPackexpConcreteHard0CheckerCount:
      recomputedChain.generatedPCCPackexpConcreteHard0CheckerCount,
    generatedPCCPackexpConcreteHard0CheckerCoverageComplete:
      recomputedChain.generatedPCCPackexpConcreteHard0CheckerCoverageComplete,
    generatedPCCPackexpConcreteHard0RowKeyFieldCount:
      recomputedChain.generatedPCCPackexpConcreteHard0RowKeyFieldCount,
    generatedPCCPackexpConcreteHard0RowKeyCoverageComplete:
      recomputedChain.generatedPCCPackexpConcreteHard0RowKeyCoverageComplete,
    generatedPCCPackexpConcreteHard0RoutePriorityComplete:
      recomputedChain.generatedPCCPackexpConcreteHard0RoutePriorityComplete,
    generatedPCCPackexpConcreteHard0ProofRefPolicyComplete:
      recomputedChain.generatedPCCPackexpConcreteHard0ProofRefPolicyComplete,
    generatedPCCPackexpConcreteHard0HashDisciplineComplete:
      recomputedChain.generatedPCCPackexpConcreteHard0HashDisciplineComplete,
    generatedPCCPackexpConcreteHard0NoMinCoverageComplete:
      recomputedChain.generatedPCCPackexpConcreteHard0NoMinCoverageComplete,
    generatedPCCPackexpConcreteHard0ForbiddenSymbolCount:
      recomputedChain.generatedPCCPackexpConcreteHard0ForbiddenSymbolCount,
    generatedPCCPackexpConcreteHard0ImportPolicyComplete:
      recomputedChain.generatedPCCPackexpConcreteHard0ImportPolicyComplete,
    generatedPCCPackexpConcreteHard0ForbiddenImportEdgeCount:
      recomputedChain.generatedPCCPackexpConcreteHard0ForbiddenImportEdgeCount,
    generatedPCCPackexpConcreteHard0ReflectionPolicyComplete:
      recomputedChain.generatedPCCPackexpConcreteHard0ReflectionPolicyComplete,
    generatedPCCPackexpConcreteHard0BoundsPolicyComplete:
      recomputedChain.generatedPCCPackexpConcreteHard0BoundsPolicyComplete,
    generatedPCCPackexpConcreteHard0DiagnosticsPolicyComplete:
      recomputedChain.generatedPCCPackexpConcreteHard0DiagnosticsPolicyComplete,
    generatedPCCPackexpConcreteHard0LinkedToPCCPack:
      recomputedChain.generatedPCCPackexpConcreteHard0LinkedToPCCPack,

    generatedPCCPackexpConcreteRows0:
      recomputedChain.generatedPCCPackexpConcreteRows0,
    generatedPCCPackexpConcreteRows0Accepted:
      recomputedChain.generatedPCCPackexpConcreteRows0Accepted,
    generatedPCCPackexpConcreteRows0Checker:
      recomputedChain.generatedPCCPackexpConcreteRows0Checker,
    generatedPCCPackexpConcreteRows0Digest:
      recomputedChain.generatedPCCPackexpConcreteRows0Digest,
    generatedPCCPackexpConcreteRows0RowPackDigest:
      recomputedChain.generatedPCCPackexpConcreteRows0RowPackDigest,
    generatedPCCPackexpConcreteRows0RowPackObjectDigest:
      recomputedChain.generatedPCCPackexpConcreteRows0RowPackObjectDigest,
    generatedPCCPackexpConcreteRows0BootDigest:
      recomputedChain.generatedPCCPackexpConcreteRows0BootDigest,
    generatedPCCPackexpConcreteRows0IfaceHash:
      recomputedChain.generatedPCCPackexpConcreteRows0IfaceHash,
    generatedPCCPackexpConcreteRows0SchedHash:
      recomputedChain.generatedPCCPackexpConcreteRows0SchedHash,
    generatedPCCPackexpConcreteRows0RowCount:
      recomputedChain.generatedPCCPackexpConcreteRows0RowCount,
    generatedPCCPackexpConcreteRows0RowCountComplete:
      recomputedChain.generatedPCCPackexpConcreteRows0RowCountComplete,
    generatedPCCPackexpConcreteRows0BatchCount:
      recomputedChain.generatedPCCPackexpConcreteRows0BatchCount,
    generatedPCCPackexpConcreteRows0BatchCountComplete:
      recomputedChain.generatedPCCPackexpConcreteRows0BatchCountComplete,
    generatedPCCPackexpConcreteRows0FamilyCount:
      recomputedChain.generatedPCCPackexpConcreteRows0FamilyCount,
    generatedPCCPackexpConcreteRows0FamilyCountComplete:
      recomputedChain.generatedPCCPackexpConcreteRows0FamilyCountComplete,
    generatedPCCPackexpConcreteRows0ConcreteIfaceHash:
      recomputedChain.generatedPCCPackexpConcreteRows0ConcreteIfaceHash,
    generatedPCCPackexpConcreteRows0SyntheticIfaceHashCount:
      recomputedChain.generatedPCCPackexpConcreteRows0SyntheticIfaceHashCount,
    generatedPCCPackexpConcreteRows0NoSyntheticIfaceHash:
      recomputedChain.generatedPCCPackexpConcreteRows0NoSyntheticIfaceHash,
    generatedPCCPackexpConcreteRows0ScaffoldMarkerCount:
      recomputedChain.generatedPCCPackexpConcreteRows0ScaffoldMarkerCount,
    generatedPCCPackexpConcreteRows0NoScaffoldMarkers:
      recomputedChain.generatedPCCPackexpConcreteRows0NoScaffoldMarkers,
    generatedPCCPackexpConcreteRows0LinkedToGeneratedBoot0:
      recomputedChain.generatedPCCPackexpConcreteRows0LinkedToGeneratedBoot0,
    generatedPCCPackexpConcreteRows0LinkedToPCCPack:
      recomputedChain.generatedPCCPackexpConcreteRows0LinkedToPCCPack,

    generatedPCCPackexpConcreteGlobalProofDAG0:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0,
    generatedPCCPackexpConcreteGlobalProofDAG0Accepted:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0Accepted,
    generatedPCCPackexpConcreteGlobalProofDAG0Checker:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0Checker,
    generatedPCCPackexpConcreteGlobalProofDAG0Digest:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0Digest,
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGDigest:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGObjectDigest:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGObjectDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0MaterializedGlobalProofDAGDigest:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0MaterializedGlobalProofDAGDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0KImplDigest:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0KImplDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0RowPackDigest:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0RowPackDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0LocalPackagesDigest:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0LocalPackagesDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalFirewallsDigest:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0GlobalFirewallsDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleProofInventoryDigest:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0KBundleProofInventoryDigest,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleKernelRuleCoverageComplete:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0KBundleKernelRuleCoverageComplete,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleSigmaProofRefsResolve:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0KBundleSigmaProofRefsResolve,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleReflectionProofRefsResolve:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0KBundleReflectionProofRefsResolve,
    generatedPCCPackexpConcreteGlobalProofDAG0NodeCount:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0NodeCount,
    generatedPCCPackexpConcreteGlobalProofDAG0NodeCountMinimum:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0NodeCountMinimum,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalTheoremCount:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0FinalTheoremCount,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalPackageSoundness:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0FinalPackageSoundness,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalGeneratedPackageSufficiency:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0FinalGeneratedPackageSufficiency,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP,
    generatedPCCPackexpConcreteGlobalProofDAG0IfaceHash:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0IfaceHash,
    generatedPCCPackexpConcreteGlobalProofDAG0SchedHash:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0SchedHash,
    generatedPCCPackexpConcreteGlobalProofDAG0IfaceMatchesRows:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0IfaceMatchesRows,
    generatedPCCPackexpConcreteGlobalProofDAG0SchedMatchesKImpl:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0SchedMatchesKImpl,
    generatedPCCPackexpConcreteGlobalProofDAG0SyntheticMarkerCount:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0SyntheticMarkerCount,
    generatedPCCPackexpConcreteGlobalProofDAG0ForbiddenMarkerCount:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0ForbiddenMarkerCount,
    generatedPCCPackexpConcreteGlobalProofDAG0NoForbiddenMarkers:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0NoForbiddenMarkers,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGeneratedBoot0:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGeneratedBoot0,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToKImpl:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToKImpl,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToConcreteRows:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToConcreteRows,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToLocalPackages:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToLocalPackages,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGlobalFirewalls:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGlobalFirewalls,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToPCCPack:
      recomputedChain.generatedPCCPackexpConcreteGlobalProofDAG0LinkedToPCCPack,

    generatedPCCPackexpConcreteFinalIntegration0:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0,
    generatedPCCPackexpConcreteFinalIntegration0Accepted:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0Accepted,
    generatedPCCPackexpConcreteFinalIntegration0Checker:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0Checker,
    generatedPCCPackexpConcreteFinalIntegration0Digest:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0Digest,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAGDigest:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAGDigest,
    generatedPCCPackexpConcreteFinalIntegration0MaterializedFinalIntegrationDigest:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0MaterializedFinalIntegrationDigest,
    generatedPCCPackexpConcreteFinalIntegration0GPackDigest:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0GPackDigest,
    generatedPCCPackexpConcreteFinalIntegration0RowFamGDigest:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0RowFamGDigest,
    generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationDigest:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationDigest,
    generatedPCCPackexpConcreteFinalIntegration0FinalTheoremDigest:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0FinalTheoremDigest,
    generatedPCCPackexpConcreteFinalIntegration0RowFamFinalDigest:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0RowFamFinalDigest,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteLinksDigest:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteLinksDigest,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAG:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAG,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteKBundle:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteKBundle,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteRows:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteRows,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteLocalPackages:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteLocalPackages,
    generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalFirewalls:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalFirewalls,
    generatedPCCPackexpConcreteFinalIntegration0KBundleKernelRuleCoverageComplete:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0KBundleKernelRuleCoverageComplete,
    generatedPCCPackexpConcreteFinalIntegration0KBundleSigmaProofRefsResolve:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0KBundleSigmaProofRefsResolve,
    generatedPCCPackexpConcreteFinalIntegration0KBundleReflectionProofRefsResolve:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0KBundleReflectionProofRefsResolve,
    generatedPCCPackexpConcreteFinalIntegration0GPackFieldCoverageComplete:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0GPackFieldCoverageComplete,
    generatedPCCPackexpConcreteFinalIntegration0RowFamGCoverageComplete:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0RowFamGCoverageComplete,
    generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationUsesGPack:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationUsesGPack,
    generatedPCCPackexpConcreteFinalIntegration0RowFamGUsesGPack:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0RowFamGUsesGPack,
    generatedPCCPackexpConcreteFinalIntegration0FinalTheoremUsesFinalIntegration:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0FinalTheoremUsesFinalIntegration,
    generatedPCCPackexpConcreteFinalIntegration0RowFamFinalUsesFinalTheorem:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0RowFamFinalUsesFinalTheorem,
    generatedPCCPackexpConcreteFinalIntegration0FinalMatchUsesGPack:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0FinalMatchUsesGPack,
    generatedPCCPackexpConcreteFinalIntegration0SATDecisionUsesGPack:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0SATDecisionUsesGPack,
    generatedPCCPackexpConcreteFinalIntegration0SyntheticMarkerCount:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0SyntheticMarkerCount,
    generatedPCCPackexpConcreteFinalIntegration0ForbiddenMarkerCount:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0ForbiddenMarkerCount,
    generatedPCCPackexpConcreteFinalIntegration0NoForbiddenMarkers:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0NoForbiddenMarkers,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToGeneratedGlobalProofDAG:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToGeneratedGlobalProofDAG,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToGPack:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToGPack,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamG:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamG,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalIntegration:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalIntegration,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalTheorem:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalTheorem,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamFinal:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamFinal,
    generatedPCCPackexpConcreteFinalIntegration0LinkedToPCCPack:
      recomputedChain.generatedPCCPackexpConcreteFinalIntegration0LinkedToPCCPack,

    generatedPCCPackexpCheckPCCPackexp0:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0,
    generatedPCCPackexpCheckPCCPackexp0Accepted:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0Accepted,
    generatedPCCPackexpCheckPCCPackexp0Checker:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0Checker,
    generatedPCCPackexpCheckPCCPackexp0Digest:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0Digest,
    generatedPCCPackexpCheckPCCPackexp0MaterializedPath:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0MaterializedPath,
    generatedPCCPackexpCheckPCCPackexp0SyntheticRunAll:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0SyntheticRunAll,
    generatedPCCPackexpCheckPCCPackexp0PackageKind:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PackageKind,
    generatedPCCPackexpCheckPCCPackexp0MaterializedPCCPackKind:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0MaterializedPCCPackKind,
    generatedPCCPackexpCheckPCCPackexp0PCCPackDigest:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackDigest,
    generatedPCCPackexpCheckPCCPackexp0MaterializedPCCPackDigest:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0MaterializedPCCPackDigest,
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordDigest:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordDigest,
    generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageDigest:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageDigest,
    generatedPCCPackexpCheckPCCPackexp0PublicConclusionOnlyAfterAcceptRun:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PublicConclusionOnlyAfterAcceptRun,
    generatedPCCPackexpCheckPCCPackexp0PublicConclusionEmitted:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PublicConclusionEmitted,
    generatedPCCPackexpCheckPCCPackexp0NoPrematurePublicConclusion:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0NoPrematurePublicConclusion,
    generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConditional:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConditional,
    generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryAntecedent:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryAntecedent,
    generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConsequent:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConsequent,
    generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication,
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPack:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcretePCCPack,
    generatedPCCPackexpCheckPCCPackexp0ConcreteKBundle:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcreteKBundle,
    generatedPCCPackexpCheckPCCPackexp0ConcreteHardCheck:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcreteHardCheck,
    generatedPCCPackexpCheckPCCPackexp0ConcreteRows:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcreteRows,
    generatedPCCPackexpCheckPCCPackexp0ConcreteLocalPackages:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcreteLocalPackages,
    generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalFirewalls:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalFirewalls,
    generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalProofDAG:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalProofDAG,
    generatedPCCPackexpCheckPCCPackexp0ConcreteFinalIntegration:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcreteFinalIntegration,
    generatedPCCPackexpCheckPCCPackexp0KBundleCoverageComplete:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0KBundleCoverageComplete,
    generatedPCCPackexpCheckPCCPackexp0HardCoverageComplete:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0HardCoverageComplete,
    generatedPCCPackexpCheckPCCPackexp0FinalIntegrationCoverageComplete:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0FinalIntegrationCoverageComplete,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToKBundle:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToKBundle,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToHardCheck:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToHardCheck,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToRows:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToRows,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToLocalPackages:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToLocalPackages,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGlobalFirewalls:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGlobalFirewalls,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGlobalProofDAG:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGlobalProofDAG,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGPack:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGPack,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToFinalIntegration:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToFinalIntegration,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToFinalTheorem:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToFinalTheorem,
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkageComplete:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0PCCPackLinkageComplete,
    generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageComplete:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageComplete,
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordKind:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordKind,
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordAccepted:
      recomputedChain.generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordAccepted,

    kBundleEnvelopeKind: recomputedChain.kBundleEnvelopeKind,
    hardEnvelopeKind: recomputedChain.hardEnvelopeKind,
    finalIntegrationEnvelopeKind: recomputedChain.finalIntegrationEnvelopeKind,

    kBundleCoverageDigest: recomputedChain.kBundleCoverageDigest,
    hardCoverageDigest: recomputedChain.hardCoverageDigest,
    finalIntegrationLinksDigest: recomputedChain.finalIntegrationLinksDigest,

    finalCertificateUsesConcreteAcceptRun: recomputedChain.finalCertificateUsesConcreteAcceptRun,
    statusUsesConcreteFinalCertificate: recomputedChain.statusUsesConcreteFinalCertificate,
    publicStatusCertificateDigestMatchesConcrete: recomputedChain.publicStatusCertificateDigestMatchesConcrete,
    publicStatusFinalVerdictDigestMatchesConcrete: recomputedChain.publicStatusFinalVerdictDigestMatchesConcrete,
    publicStatusAcceptRunDigestMatchesConcrete: recomputedChain.publicStatusAcceptRunDigestMatchesConcrete,
    publicStatusPccPackDigestMatchesConcrete: recomputedChain.publicStatusPccPackDigestMatchesConcrete,
    publicConclusionMatchesCertificate: recomputedChain.publicConclusionMatchesCertificate,
    publicConclusionMatchesFinalVerdict: recomputedChain.publicConclusionMatchesFinalVerdict,

    status: recomputedChain.status,
    verdict: recomputedChain.verdict,
    publicConclusionEmitted: recomputedChain.publicConclusionEmitted,
    publicConclusion: recomputedChain.publicConclusion,

    certificateDigest: recomputedChain.certificateDigest,
    finalVerdictDigest: recomputedChain.finalVerdictRecordDigest,
    acceptRunDigest: recomputedChain.acceptRunDigest,
    pccPackDigest: recomputedChain.pccPackDigest,
    canonicalByteRoots: recomputedChain.canonicalByteRoots,
    acceptanceTranscript: recomputedChain.acceptanceTranscript,

    concreteFinalCertificateEnvelopeDigest: digestCanonical0(envelope.ConcreteFinalCertificateEnvelope),
    finalCertificatePublicStatusEnvelopeDigest: digestCanonical0(envelope.FinalCertificatePublicStatusEnvelope),
    concreteChainDigest: digestCanonical0(recomputedChain),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),

    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
    allowSyntheticScaffoldMarker: cfg.allowSyntheticScaffoldMarker,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeConcreteFinalCertificatePublicStatusFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteFinalCertificatePublicStatusFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteFinalCertificatePublicStatus0(options);
  const checked = await CheckConcreteFinalCertificatePublicStatus0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteFinalCertificatePublicStatus0.json');
  const concreteFinalCertificatePath = path.join(outDir, 'ConcreteMaterializedFinalCertificate0.json');
  const finalCertificatePublicStatusPath = path.join(outDir, 'FinalCertificatePublicStatus0.json');
  const publicStatusPath = path.join(outDir, 'FinalCertificatePublicStatusEmission0.json');
  const concreteChainPath = path.join(outDir, 'ConcreteFinalCertificatePublicStatusChain0.json');
  const checkPath = path.join(outDir, 'ConcreteFinalCertificatePublicStatus0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(concreteFinalCertificatePath, envelope.ConcreteFinalCertificateEnvelope);
  await writeJsonFile0(finalCertificatePublicStatusPath, envelope.FinalCertificatePublicStatusEnvelope);
  await writeJsonFile0(publicStatusPath, envelope.FinalCertificatePublicStatusEnvelope.PublicStatus);
  await writeJsonFile0(concreteChainPath, envelope.ConcreteChain);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      concreteFinalCertificatePath,
      finalCertificatePublicStatusPath,
      publicStatusPath,
      concreteChainPath,
      checkPath,
    },
  };
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteFinalCertificatePublicStatusConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteFinalCertificatePublicStatusConfig0') {
    return validationReject0(['kind'], 'ConcreteFinalCertificatePublicStatusConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteFinalCertificatePublicStatusConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkConcreteFinalCertificate',
    'checkFinalCertificatePublicStatus',
    'checkConcreteChain',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteFinalCertificatePublicStatusConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.concreteFinalCertificateConfig)) {
    return validationReject0(['concreteFinalCertificateConfig'], 'concreteFinalCertificateConfig must be an object', {
      actual: typeof config.concreteFinalCertificateConfig,
    });
  }

  if (!isPlainObject(config.finalCertificatePublicStatusConfig)) {
    return validationReject0(['finalCertificatePublicStatusConfig'], 'finalCertificatePublicStatusConfig must be an object', {
      actual: typeof config.finalCertificatePublicStatusConfig,
    });
  }

  return validationAccept0({
    kind: 'ConcreteFinalCertificatePublicStatusConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteFinalCertificatePublicStatus0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteFinalCertificatePublicStatus0') {
    return validationReject0(['kind'], 'ConcreteFinalCertificatePublicStatus0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteFinalCertificatePublicStatus0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.ConcreteFinalCertificateEnvelope)) {
    return validationReject0(['ConcreteFinalCertificateEnvelope'], 'ConcreteFinalCertificatePublicStatus0 must include ConcreteFinalCertificateEnvelope', {
      actual: typeof envelope.ConcreteFinalCertificateEnvelope,
    });
  }

  if (!isPlainObject(envelope.FinalCertificatePublicStatusEnvelope)) {
    return validationReject0(['FinalCertificatePublicStatusEnvelope'], 'ConcreteFinalCertificatePublicStatus0 must include FinalCertificatePublicStatusEnvelope', {
      actual: typeof envelope.FinalCertificatePublicStatusEnvelope,
    });
  }

  if (!isPlainObject(envelope.ConcreteChain)) {
    return validationReject0(['ConcreteChain'], 'ConcreteFinalCertificatePublicStatus0 must include ConcreteChain', {
      actual: typeof envelope.ConcreteChain,
    });
  }

  return validationAccept0({
    kind: 'ConcreteFinalCertificatePublicStatusShape0NF',
  });
}

function validateConcretePublicStatusChain0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['ConcreteChain'], 'Concrete public-status chain must match recomputed chain summary', {
      expectedDigest: digestCanonical0(expected),
      actualDigest: digestCanonical0(actual),
    });
  }

  const requiredTrue = [
    'concreteRows',
    'concreteLocalPackages',
    'concreteGlobalFirewalls',
    'concreteGlobalProofDAG',

    'concreteKBundle',
    'kBundleKernelRuleCoverageComplete',
    'kBundleSigmaProofRefsResolve',
    'kBundleReflectionProofRefsResolve',

    'concreteHardCheck',
    'hardCheckerCoverageComplete',
    'hardRowKeyCoverageComplete',
    'hardRoutePriorityComplete',
    'hardProofRefPolicyComplete',
    'hardHashDisciplineComplete',
    'hardNoMinCoverageComplete',
    'hardImportPolicyComplete',
    'hardReflectionPolicyComplete',
    'hardBoundsPolicyComplete',
    'hardDiagnosticsPolicyComplete',

    'concreteFinalIntegration',
    'finalIntegrationConcreteGlobalProofDAG',
    'finalIntegrationGPackFieldCoverageComplete',
    'finalIntegrationRowFamGCoverageComplete',
    'finalIntegrationUsesGPack',
    'rowFamGUsesGPack',
    'finalTheoremUsesFinalIntegration',
    'rowFamFinalUsesFinalTheorem',
    'finalMatchUsesGPack',
    'satDecisionUsesGPack',

    'concretePCCPack',
    'pccPackPublicConclusionOnlyAfterAcceptRun',
    'pccPackLinkedToKBundle',
    'pccPackLinkedToHardCheck',
    'pccPackLinkedToRows',
    'pccPackLinkedToLocalPackages',
    'pccPackLinkedToGlobalFirewalls',
    'pccPackLinkedToGlobalProofDAG',
    'pccPackLinkedToGPack',
    'pccPackLinkedToFinalIntegration',
    'pccPackLinkedToFinalTheorem',

    'checkPCCPackexpRecordPresent',
    'checkPCCPackexpRecordAccepted',
    'checkPCCPackexpRecordDigestMatchesNF',
    'checkPCCPackexpRecordConcretePCCPack',
    'checkPCCPackexpRecordPccPackDigestMatchesConcreteRun',
    'checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun',
    'checkPCCPackexpRecordPublicConclusionNotEmitted',
    'checkPCCPackexpRecordClaimBoundaryConditional',

    'generatedPCCPackexpEnvelopePresent',
    'generatedPCCPackexpGenCallGeneratePCCPack',
    'generatedPCCPackexpCoreOnly',
    'generatedPCCPackexpExcludesAcceptRun',
    'generatedPCCPackexpPackageMatchesConcreteRun',
    'generatedPCCPackexpCheckRecordMatchesConcreteRun',
    'generatedPCCPackexpCheckRecordAccepted',
    'generatedPCCPackexpCheckRecordDigestMatchesNF',
    'generatedPCCPackexpCheckRecordClaimBoundaryConditional',
    'generatedPCCPackexpLinkageGeneratedPackageDigestMatches',
    'generatedPCCPackexpLinkageCheckRecordDigestMatches',

    'checkGeneratedPCCPackexpRecordPresent',
    'checkGeneratedPCCPackexpRecordAccepted',
    'checkGeneratedPCCPackexpRecordDigestMatchesNF',
    'checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope',
    'checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope',

    'generatedPCCPackexpBoot0',
    'generatedPCCPackexpBoot0Accepted',
    'generatedPCCPackexpBoot0JsonMaterialized',
    'generatedPCCPackexpBoot0NoFixtureMarkers',
    'generatedPCCPackexpBoot0LinkedToPCCPack',
    'generatedPCCPackexpBoot0LinkedToCoreDigestMap',
    'generatedPCCPackexpBoot0DigestMatchesGeneratedPackage',
    'generatedPCCPackexpBoot0DigestMatchesCoreDigestMap',

    'generatedPCCPackexpBoot0B0Accepted',
    'generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent',
    'generatedPCCPackexpBoot0B0CoversIface',
    'generatedPCCPackexpBoot0B0CoversSched',
    'generatedPCCPackexpBoot0B0CoversNF',
    'generatedPCCPackexpBoot0B0CoversTruthEval',
    'generatedPCCPackexpBoot0B0CoversRel',
    'generatedPCCPackexpBoot0B0CoversCharge',
    'generatedPCCPackexpBoot0B0CoversObl',
    'generatedPCCPackexpBoot0B0CoversArith',
    'generatedPCCPackexpBoot0B0CoversMode',
    'generatedPCCPackexpBoot0B0CoversRoute',
    'generatedPCCPackexpBoot0B0CoversHash',
    'generatedPCCPackexpBoot0B0CoversImport',

    'generatedPCCPackexpKernelSeed0',
    'generatedPCCPackexpKernelSeed0Accepted',
    'generatedPCCPackexpKernelSeed0AllRequiredRulesPresent',
    'generatedPCCPackexpKernelSeed0HasEq',
    'generatedPCCPackexpKernelSeed0HasSubst',
    'generatedPCCPackexpKernelSeed0HasRecord',
    'generatedPCCPackexpKernelSeed0HasDAGInd',
    'generatedPCCPackexpKernelSeed0HasLedgerInd',
    'generatedPCCPackexpKernelSeed0HasOblTopoInd',
    'generatedPCCPackexpKernelSeed0HasTraceInd',
    'generatedPCCPackexpKernelSeed0HasFiniteExhaust',
    'generatedPCCPackexpKernelSeed0HasDPInd',
    'generatedPCCPackexpKernelSeed0HasHall',
    'generatedPCCPackexpKernelSeed0HasRankInd',
    'generatedPCCPackexpKernelSeed0HasMinCounterexample',
    'generatedPCCPackexpKernelSeed0HasIntArith',
    'generatedPCCPackexpKernelSeed0HasTransport',
    'generatedPCCPackexpKernelSeed0HasTruthVec',
    'generatedPCCPackexpKernelSeed0HasFiniteRel',
    'generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent',
    'generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque',
    'generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic',
    'generatedPCCPackexpKernelSeed0ProofRefsHashIndependent',
    'generatedPCCPackexpKernelSeed0PiBootDigestMatches',

    'generatedPCCPackexpCodec0',
    'generatedPCCPackexpCodec0Accepted',
    'generatedPCCPackexpCodec0Canonical',
    'generatedPCCPackexpCodec0NaturalEncodingCanonical',
    'generatedPCCPackexpCodec0IntegerEncodingCanonical',
    'generatedPCCPackexpCodec0StringEncodingCanonical',
    'generatedPCCPackexpCodec0TopLevelConsumesAllBytes',
    'generatedPCCPackexpCodec0NormalFormSerializationCanonical',
    'generatedPCCPackexpCodec0PiBootDigestMatches',
    'generatedPCCPackexpDigest0',
    'generatedPCCPackexpDigest0Accepted',
    'generatedPCCPackexpDigest0AlgSHA256',
    'generatedPCCPackexpDigest0BytesCanonicalJson',
    'generatedPCCPackexpDigest0EqualityNotObjectEquality',
    'generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup',
    'generatedPCCPackexpDigest0PiBootDigestMatches',

    'generatedPCCPackexpIfaceDict0',
    'generatedPCCPackexpIfaceDict0Accepted',
    'generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent',
    'generatedPCCPackexpIfaceDict0NoExecutableMinSymbols',
    'generatedPCCPackexpIfaceDict0PublicConstructorsPresent',
    'generatedPCCPackexpIfaceDict0CriticalKindsPresent',
    'generatedPCCPackexpIfaceDict0RouteTokensPresent',
    'generatedPCCPackexpIfaceDict0PiBootDigestMatches',
    'generatedPCCPackexpSched0',
    'generatedPCCPackexpSched0Accepted',
    'generatedPCCPackexpSched0CoreMatchesExpected',
    'generatedPCCPackexpSched0ScaleFactorsPresent',
    'generatedPCCPackexpSched0SelectorBoundsPresent',
    'generatedPCCPackexpSched0PiBootDigestMatches',

    'generatedPCCPackexpByteLang0',
    'generatedPCCPackexpByteLang0Accepted',
    'generatedPCCPackexpByteLang0TagsUnique',
    'generatedPCCPackexpByteLang0RequiredTagsPresent',
    'generatedPCCPackexpByteLang0RequiredSortsPresent',
    'generatedPCCPackexpByteLang0RequiredConstructorsPresent',
    'generatedPCCPackexpByteLang0RequiredRecordAritiesPresent',
    'generatedPCCPackexpByteLang0PiBootDigestMatches',

    'generatedPCCPackexpBootAudit0',
    'generatedPCCPackexpBootAudit0Accepted',
    'generatedPCCPackexpBootAudit0DigestMatchesNF',
    'generatedPCCPackexpBootAudit0CoversB0Accept',
    'generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject',
    'generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject',
    'generatedPCCPackexpPiBoot0',
    'generatedPCCPackexpPiBoot0Accepted',
    'generatedPCCPackexpPiBoot0Materialized',
    'generatedPCCPackexpPiBoot0ExternalJson',
    'generatedPCCPackexpPiBoot0AllBootRefsPresent',
    'generatedPCCPackexpPiBoot0RefsMatchBootObjects',
    'generatedPCCPackexpPiBoot0RefsIncludeByteLang0',
    'generatedPCCPackexpPiBoot0RefsIncludeCodec0',
    'generatedPCCPackexpPiBoot0RefsIncludeDigest0',
    'generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0',
    'generatedPCCPackexpPiBoot0RefsIncludeSched0',
    'generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0',
    'generatedPCCPackexpPiBoot0RefsIncludeB0',
    'generatedPCCPackexpPiBoot0RefsIncludeBootAudit0',

    'generatedPCCPackexpConcreteKBundle0',
    'generatedPCCPackexpConcreteKBundle0Accepted',
    'generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete',
    'generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete',
    'generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve',
    'generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete',
    'generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve',
    'generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs',
    'generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols',
    'generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0',

    'generatedPCCPackexpConcreteHard0',
    'generatedPCCPackexpConcreteHard0Accepted',
    'generatedPCCPackexpConcreteHard0CheckerCoverageComplete',
    'generatedPCCPackexpConcreteHard0RowKeyCoverageComplete',
    'generatedPCCPackexpConcreteHard0RoutePriorityComplete',
    'generatedPCCPackexpConcreteHard0ProofRefPolicyComplete',
    'generatedPCCPackexpConcreteHard0HashDisciplineComplete',
    'generatedPCCPackexpConcreteHard0NoMinCoverageComplete',
    'generatedPCCPackexpConcreteHard0ImportPolicyComplete',
    'generatedPCCPackexpConcreteHard0ReflectionPolicyComplete',
    'generatedPCCPackexpConcreteHard0BoundsPolicyComplete',
    'generatedPCCPackexpConcreteHard0DiagnosticsPolicyComplete',
    'generatedPCCPackexpConcreteHard0LinkedToPCCPack',

    'generatedPCCPackexpConcreteRows0',
    'generatedPCCPackexpConcreteRows0Accepted',
    'generatedPCCPackexpConcreteRows0RowCountComplete',
    'generatedPCCPackexpConcreteRows0BatchCountComplete',
    'generatedPCCPackexpConcreteRows0FamilyCountComplete',
    'generatedPCCPackexpConcreteRows0ConcreteIfaceHash',
    'generatedPCCPackexpConcreteRows0NoSyntheticIfaceHash',
    'generatedPCCPackexpConcreteRows0NoScaffoldMarkers',
    'generatedPCCPackexpConcreteRows0LinkedToGeneratedBoot0',
    'generatedPCCPackexpConcreteRows0LinkedToPCCPack',

    'generatedPCCPackexpConcreteGlobalProofDAG0',
    'generatedPCCPackexpConcreteGlobalProofDAG0Accepted',
    'generatedPCCPackexpConcreteGlobalProofDAG0KBundleKernelRuleCoverageComplete',
    'generatedPCCPackexpConcreteGlobalProofDAG0KBundleSigmaProofRefsResolve',
    'generatedPCCPackexpConcreteGlobalProofDAG0KBundleReflectionProofRefsResolve',
    'generatedPCCPackexpConcreteGlobalProofDAG0NodeCountMinimum',
    'generatedPCCPackexpConcreteGlobalProofDAG0FinalPackageSoundness',
    'generatedPCCPackexpConcreteGlobalProofDAG0FinalGeneratedPackageSufficiency',
    'generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP',
    'generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP',
    'generatedPCCPackexpConcreteGlobalProofDAG0IfaceMatchesRows',
    'generatedPCCPackexpConcreteGlobalProofDAG0SchedMatchesKImpl',
    'generatedPCCPackexpConcreteGlobalProofDAG0NoForbiddenMarkers',
    'generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGeneratedBoot0',
    'generatedPCCPackexpConcreteGlobalProofDAG0LinkedToKImpl',
    'generatedPCCPackexpConcreteGlobalProofDAG0LinkedToConcreteRows',
    'generatedPCCPackexpConcreteGlobalProofDAG0LinkedToLocalPackages',
    'generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGlobalFirewalls',
    'generatedPCCPackexpConcreteGlobalProofDAG0LinkedToPCCPack',

    'generatedPCCPackexpConcreteFinalIntegration0',
    'generatedPCCPackexpConcreteFinalIntegration0Accepted',
    'generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAG',
    'generatedPCCPackexpConcreteFinalIntegration0ConcreteKBundle',
    'generatedPCCPackexpConcreteFinalIntegration0ConcreteRows',
    'generatedPCCPackexpConcreteFinalIntegration0ConcreteLocalPackages',
    'generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalFirewalls',
    'generatedPCCPackexpConcreteFinalIntegration0KBundleKernelRuleCoverageComplete',
    'generatedPCCPackexpConcreteFinalIntegration0KBundleSigmaProofRefsResolve',
    'generatedPCCPackexpConcreteFinalIntegration0KBundleReflectionProofRefsResolve',
    'generatedPCCPackexpConcreteFinalIntegration0GPackFieldCoverageComplete',
    'generatedPCCPackexpConcreteFinalIntegration0RowFamGCoverageComplete',
    'generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationUsesGPack',
    'generatedPCCPackexpConcreteFinalIntegration0RowFamGUsesGPack',
    'generatedPCCPackexpConcreteFinalIntegration0FinalTheoremUsesFinalIntegration',
    'generatedPCCPackexpConcreteFinalIntegration0RowFamFinalUsesFinalTheorem',
    'generatedPCCPackexpConcreteFinalIntegration0FinalMatchUsesGPack',
    'generatedPCCPackexpConcreteFinalIntegration0SATDecisionUsesGPack',
    'generatedPCCPackexpConcreteFinalIntegration0NoForbiddenMarkers',
    'generatedPCCPackexpConcreteFinalIntegration0LinkedToGeneratedGlobalProofDAG',
    'generatedPCCPackexpConcreteFinalIntegration0LinkedToGPack',
    'generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamG',
    'generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalIntegration',
    'generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalTheorem',
    'generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamFinal',
    'generatedPCCPackexpConcreteFinalIntegration0LinkedToPCCPack',

    'generatedPCCPackexpCheckPCCPackexp0',
    'generatedPCCPackexpCheckPCCPackexp0Accepted',
    'generatedPCCPackexpCheckPCCPackexp0MaterializedPath',
    'generatedPCCPackexpCheckPCCPackexp0SyntheticRunAll',
    'generatedPCCPackexpCheckPCCPackexp0PublicConclusionOnlyAfterAcceptRun',
    'generatedPCCPackexpCheckPCCPackexp0PublicConclusionEmitted',
    'generatedPCCPackexpCheckPCCPackexp0NoPrematurePublicConclusion',
    'generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConditional',
    'generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication',
    'generatedPCCPackexpCheckPCCPackexp0ConcretePCCPack',
    'generatedPCCPackexpCheckPCCPackexp0ConcreteKBundle',
    'generatedPCCPackexpCheckPCCPackexp0ConcreteHardCheck',
    'generatedPCCPackexpCheckPCCPackexp0ConcreteRows',
    'generatedPCCPackexpCheckPCCPackexp0ConcreteLocalPackages',
    'generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalFirewalls',
    'generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalProofDAG',
    'generatedPCCPackexpCheckPCCPackexp0ConcreteFinalIntegration',
    'generatedPCCPackexpCheckPCCPackexp0KBundleCoverageComplete',
    'generatedPCCPackexpCheckPCCPackexp0HardCoverageComplete',
    'generatedPCCPackexpCheckPCCPackexp0FinalIntegrationCoverageComplete',
    'generatedPCCPackexpCheckPCCPackexp0PCCPackLinkageComplete',
    'generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageComplete',
    'generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordAccepted',

    'finalCertificateUsesConcreteAcceptRun',
    'statusUsesConcreteFinalCertificate',
    'publicStatusCertificateDigestMatchesConcrete',
    'publicStatusFinalVerdictDigestMatchesConcrete',
    'publicStatusAcceptRunDigestMatchesConcrete',
    'publicStatusPccPackDigestMatchesConcrete',
    'publicConclusionMatchesCertificate',
    'publicConclusionMatchesFinalVerdict',
    'publicConclusionEmitted',
  ];

  for (const field of requiredTrue) {
    if (expected[field] !== true) {
      return validationReject0(['ConcreteChain', field], `Concrete public-status chain must certify ${field}`, {
        actual: expected[field],
      });
    }
  }

  if (expected.status !== 'accepted' || expected.verdict !== 'accept') {
    return validationReject0(['ConcreteChain', 'status'], 'Concrete public-status chain must be accepted', {
      status: expected.status,
      verdict: expected.verdict,
    });
  }

  return validationAccept0({
    kind: 'ConcreteFinalCertificatePublicStatusChain0NF',
    concreteChainDigest: digestCanonical0(expected),
    certificateDigest: expected.certificateDigest,
    finalVerdictDigest: expected.finalVerdictRecordDigest,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['ConcreteFinalCertificatePublicStatus0'], 'ConcreteFinalCertificatePublicStatus0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ConcreteFinalCertificatePublicStatus0'], 'ConcreteFinalCertificatePublicStatus0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteFinalCertificatePublicStatusJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope, concreteChain) {
  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteFinalCertificatePublicStatusLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteFinalCertificatePublicStatus0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const concreteFinalCertificate = envelope.ConcreteFinalCertificateEnvelope;
  const statusEnvelope = envelope.FinalCertificatePublicStatusEnvelope;

  const expected = {
    concreteFinalCertificateEnvelopeDigest: digestCanonical0(concreteFinalCertificate),
    finalCertificateEnvelopeDigest: digestCanonical0(concreteFinalCertificate.FinalCertificateEnvelope),
    finalCertificatePublicStatusEnvelopeDigest: digestCanonical0(statusEnvelope),
    publicStatusDigest: digestCanonical0(statusEnvelope.PublicStatus),
    certificateDigest: digestCanonical0(concreteFinalCertificate.FinalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(concreteFinalCertificate.FinalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest:
      concreteFinalCertificate.FinalCertificateEnvelope.FinalVerdict.Digest ??
      concreteFinalCertificate.FinalCertificateEnvelope.FinalVerdict.digest,
    acceptRunDigest: digestCanonical0(
      concreteFinalCertificate.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun,
    ),
    pccPackDigest: digestCanonical0(
      concreteFinalCertificate.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen,
    ),
    concreteChainDigest: digestCanonical0(concreteChain),
  };

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteFinalCertificatePublicStatusLinkage0NF',
    present: true,
    ...expected,
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ConcreteFinalCertificatePublicStatusFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === CONCRETE_PUBLIC_STATUS_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== CONCRETE_PUBLIC_STATUS_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== CONCRETE_PUBLIC_STATUS_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'concrete final-certificate public status contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ConcreteFinalCertificatePublicStatusNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function scanFixtureMarkers0(value, path, hits) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of [
      CONCRETE_PUBLIC_STATUS_SYNTHETIC_MARKER0,
      ...CONCRETE_PUBLIC_STATUS_FORBIDDEN_MARKERS0,
    ]) {
      if (lower.includes(marker)) {
        hits.push({
          path,
          marker,
          value,
        });
      }
    }

    return;
  }

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      scanFixtureMarkers0(value[index], [...path, index], hits);
    }

    return;
  }

  if (!isPlainObject(value)) {
    return;
  }

  for (const key of Object.keys(value)) {
    scanFixtureMarkers0(value[key], [...path, key], hits);
  }
}

function makeClaimBoundary0() {
  return {
    antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
    consequent: 'P = NP',
    conditional: true,
  };
}

function digestFromRecord0(record) {
  if (!isPlainObject(record)) {
    return null;
  }

  return record.Digest ?? record.digest ?? null;
}

function samePublicConclusion0(a, b) {
  return (
    isPlainObject(a) &&
    isPlainObject(b) &&
    a.antecedent === b.antecedent &&
    a.consequent === b.consequent &&
    a.conditional === b.conditional
  );
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}

function sameDigestHex0(actual, expected) {
  return (
    isPlainObject(actual) &&
    isPlainObject(expected) &&
    typeof actual.hex === 'string' &&
    typeof expected.hex === 'string' &&
    actual.hex === expected.hex &&
    (
      actual.alg === undefined ||
      expected.alg === undefined ||
      actual.alg === expected.alg
    )
  );
}

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
}

function makeAcceptRecord({
  checker,
  nf,
  ledger,
}) {
  const digest = digestCanonical0(nf);

  return {
    tag: 'accept',
    kind: 'accept',
    checker,
    version: CHECKER_VERSION,
    NF: nf,
    Digest: digest,
    Ledger: ledger,
    nf,
    digest,
    ledger,
  };
}

function makeRejectRecord({
  checker,
  coord,
  path,
  witness,
  ledger,
}) {
  const rejectNF = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };

  const digest = digestCanonical0(rejectNF);

  return {
    tag: 'reject',
    kind: 'reject',
    checker,
    version: CHECKER_VERSION,
    Coord: coord,
    Path: path,
    Witness: witness,
    Digest: digest,
    Ledger: ledger,
    coord,
    path,
    witness,
    digest,
    ledger,
  };
}

function validationAccept0(nf) {
  return {
    ok: true,
    nf,
  };
}

function validationReject0(path, reason, detail) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      detail,
    },
  };
}

function isRejectRecord0(value) {
  return classifyRecord0(value) === 'reject';
}

function classifyRecord0(value) {
  if (!isPlainObject(value)) {
    return 'unknown';
  }

  const raw =
    value.tag ??
    value.kind ??
    value.verdict ??
    value.status ??
    value.result ??
    value.outcome;

  if (typeof raw !== 'string') {
    return 'unknown';
  }

  const normalized = raw.trim().toLowerCase();

  if (
    normalized === 'accept' ||
    normalized === 'accepted' ||
    normalized === 'ok' ||
    normalized === 'pass' ||
    normalized === 'passed'
  ) {
    return 'accept';
  }

  if (
    normalized === 'reject' ||
    normalized === 'rejected' ||
    normalized === 'err' ||
    normalized === 'error' ||
    normalized === 'fail' ||
    normalized === 'failed'
  ) {
    return 'reject';
  }

  return 'unknown';
}

function compactReject0(value) {
  if (!isPlainObject(value)) {
    return value;
  }

  return {
    checker: value.checker ?? null,
    coord: value.Coord ?? value.coord ?? null,
    path: value.Path ?? value.path ?? null,
    witness: value.Witness ?? value.witness ?? null,
    digest: value.Digest ?? value.digest ?? null,
  };
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedFinalCertificate0,
  makeMaterializedFinalCertificate0,
} from './pcc-final-certificate-materialized0.mjs';

import {
  CheckConcreteMaterializedGeneratedAcceptRun0,
  makeConcreteMaterializedGeneratedAcceptRun0,
  summarizeConcreteGeneratedAcceptRunChain0,
} from './pcc-accept-run-concrete-materialized0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_CERT_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const CONCRETE_CERT_SYNTHETIC_MARKER0 = 'synthetic';

export function makeConcreteMaterializedFinalCertificateConfig0(overrides = {}) {
  return {
    kind: 'ConcreteMaterializedFinalCertificateConfig0',
    version: CHECKER_VERSION,
    checkConcreteGeneratedAcceptRun: true,
    checkFinalCertificate: true,
    checkConcreteChain: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    concreteGeneratedAcceptRunConfig: {},
    finalCertificateConfig: {},
    ...overrides,
  };
}

export async function makeConcreteMaterializedFinalCertificate0({
  ConcreteGeneratedAcceptRunEnvelope = null,
  FinalCertificateEnvelope = null,
  overrides = {},
} = {}) {
  const concreteGeneratedAcceptRunEnvelope = ConcreteGeneratedAcceptRunEnvelope ?? await makeConcreteMaterializedGeneratedAcceptRun0();

  const finalCertificateEnvelope = FinalCertificateEnvelope ?? await makeMaterializedFinalCertificate0({
    GeneratedAcceptRunEnvelope: concreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope,
  });

  const concreteChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope,
    finalCertificateEnvelope,
  });

  const linkage = {
    kind: 'ConcreteMaterializedFinalCertificateLinkage0',
    version: CHECKER_VERSION,
    concreteGeneratedAcceptRunEnvelopeDigest: digestCanonical0(concreteGeneratedAcceptRunEnvelope),
    generatedAcceptRunEnvelopeDigest: digestCanonical0(concreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope),
    finalCertificateEnvelopeDigest: digestCanonical0(finalCertificateEnvelope),
    finalCertificateDigest: digestCanonical0(finalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(finalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest: finalCertificateEnvelope.FinalVerdict.Digest ?? finalCertificateEnvelope.FinalVerdict.digest ?? null,
    acceptRunDigest: digestCanonical0(concreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun),
    pccPackDigest: digestCanonical0(concreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen),
    concreteChainDigest: digestCanonical0(concreteChain),
  };

  return {
    kind: 'ConcreteMaterializedFinalCertificate0',
    version: CHECKER_VERSION,
    ConcreteGeneratedAcceptRunEnvelope: concreteGeneratedAcceptRunEnvelope,
    FinalCertificateEnvelope: finalCertificateEnvelope,
    ConcreteChain: concreteChain,
    Linkage: linkage,
    PiConcreteMaterializedFinalCertificate: {
      kind: 'PiConcreteMaterializedFinalCertificate0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteGeneratedAcceptRunEnvelope',
          digest: linkage.concreteGeneratedAcceptRunEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalCertificateEnvelope',
          digest: linkage.finalCertificateEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteFinalCertificateChain',
          digest: linkage.concreteChainDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function summarizeConcreteFinalCertificateChain0({
  concreteGeneratedAcceptRunEnvelope,
  finalCertificateEnvelope,
}) {
  const generatedAcceptRunEnvelope = concreteGeneratedAcceptRunEnvelope?.GeneratedAcceptRunEnvelope ?? null;
  const finalGeneratedAcceptRunEnvelope = finalCertificateEnvelope?.GeneratedAcceptRunEnvelope ?? null;
  const concreteGeneratedChain = summarizeConcreteGeneratedAcceptRunChain0(generatedAcceptRunEnvelope);
  const certificate = finalCertificateEnvelope?.Certificate ?? null;
  const finalVerdict = finalCertificateEnvelope?.FinalVerdict ?? null;

  const checkPCCPackexpRecord = concreteGeneratedAcceptRunEnvelope?.CheckPCCPackexpRecord ?? null;
  const checkPCCPackexpRecordNF = checkPCCPackexpRecord?.NF ?? checkPCCPackexpRecord?.nf ?? null;
  const checkPCCPackexpRecordDigest = digestFromRecord0(checkPCCPackexpRecord);
  const checkPCCPackexpRecordNFDigest = isPlainObject(checkPCCPackexpRecordNF)
    ? digestCanonical0(checkPCCPackexpRecordNF)
    : null;

  const generatedPCCPackexpEnvelope = concreteGeneratedAcceptRunEnvelope?.GeneratedPCCPackexpEnvelope ?? null;
  const generatedPCCPackexpGeneratedPackage = generatedPCCPackexpEnvelope?.GeneratedPCCPack ?? null;
  const generatedPCCPackexpMaterializedPackage =
    generatedPCCPackexpGeneratedPackage?.MaterializedPCCPackEnvelope ?? null;
  const generatedPCCPackexpCheckRecord = generatedPCCPackexpEnvelope?.CheckPCCPackexpRecord ?? null;
  const generatedPCCPackexpCheckRecordNF =
    generatedPCCPackexpCheckRecord?.NF ?? generatedPCCPackexpCheckRecord?.nf ?? null;
  const generatedPCCPackexpCheckRecordDigest = digestFromRecord0(generatedPCCPackexpCheckRecord);
  const generatedPCCPackexpCheckRecordNFDigest = isPlainObject(generatedPCCPackexpCheckRecordNF)
    ? digestCanonical0(generatedPCCPackexpCheckRecordNF)
    : null;

  const checkGeneratedPCCPackexpRecord =
    concreteGeneratedAcceptRunEnvelope?.CheckGeneratedPCCPackexpRecord ?? null;
  const checkGeneratedPCCPackexpRecordNF =
    checkGeneratedPCCPackexpRecord?.NF ?? checkGeneratedPCCPackexpRecord?.nf ?? null;
  const checkGeneratedPCCPackexpRecordDigest = digestFromRecord0(checkGeneratedPCCPackexpRecord);
  const checkGeneratedPCCPackexpRecordNFDigest = isPlainObject(checkGeneratedPCCPackexpRecordNF)
    ? digestCanonical0(checkGeneratedPCCPackexpRecordNF)
    : null;
  const generatedPCCPackexpBoot0 =
    generatedPCCPackexpEnvelope?.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.MaterializedBoot0 ?? null;
  const generatedPCCPackexpCoreBootDigest =
    generatedPCCPackexpEnvelope
      ?.GeneratedPCCPack
      ?.MaterializedPCCPackEnvelope
      ?.PCCPack
      ?.Core
      ?.artefactDigests
      ?.Boot0 ?? null;

  const generatedAcceptRunDigest = digestCanonical0(generatedAcceptRunEnvelope);
  const finalGeneratedAcceptRunDigest = digestCanonical0(finalGeneratedAcceptRunEnvelope);

  const pccPackDigest = concreteGeneratedChain.pccPackDigest;
  const certificatePccPackDigest = certificate?.artefactDigests?.pccPackDigest ?? null;

  const acceptRunDigest = digestCanonical0(generatedAcceptRunEnvelope?.AcceptRun ?? null);
  const certificateAcceptRunDigest = certificate?.artefactDigests?.acceptRunDigest ?? null;

  const finalVerdictRecordDigest = finalVerdict?.Digest ?? finalVerdict?.digest ?? null;
  const certificateFinalVerdictRecordDigest = certificate?.artefactDigests?.finalVerdictRecordDigest ?? null;

  return {
    kind: 'ConcreteFinalCertificateChain0',
    version: CHECKER_VERSION,

    concreteRows: concreteGeneratedChain.concreteRows,
    concreteLocalPackages: concreteGeneratedChain.concreteLocalPackages,
    concreteGlobalFirewalls: concreteGeneratedChain.concreteGlobalFirewalls,
    concreteGlobalProofDAG: concreteGeneratedChain.concreteGlobalProofDAG,

    concreteKBundle: concreteGeneratedChain.concreteKBundle,
    kBundleKernelRuleCoverageComplete: concreteGeneratedChain.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: concreteGeneratedChain.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: concreteGeneratedChain.kBundleReflectionProofRefsResolve,

    concreteHardCheck: concreteGeneratedChain.concreteHardCheck,
    hardCheckerCoverageComplete: concreteGeneratedChain.hardCheckerCoverageComplete,
    hardRowKeyCoverageComplete: concreteGeneratedChain.hardRowKeyCoverageComplete,
    hardRoutePriorityComplete: concreteGeneratedChain.hardRoutePriorityComplete,
    hardProofRefPolicyComplete: concreteGeneratedChain.hardProofRefPolicyComplete,
    hardHashDisciplineComplete: concreteGeneratedChain.hardHashDisciplineComplete,
    hardNoMinCoverageComplete: concreteGeneratedChain.hardNoMinCoverageComplete,
    hardImportPolicyComplete: concreteGeneratedChain.hardImportPolicyComplete,
    hardReflectionPolicyComplete: concreteGeneratedChain.hardReflectionPolicyComplete,
    hardBoundsPolicyComplete: concreteGeneratedChain.hardBoundsPolicyComplete,
    hardDiagnosticsPolicyComplete: concreteGeneratedChain.hardDiagnosticsPolicyComplete,

    concreteFinalIntegration: concreteGeneratedChain.concreteFinalIntegration,
    finalIntegrationConcreteGlobalProofDAG: concreteGeneratedChain.finalIntegrationConcreteGlobalProofDAG,
    finalIntegrationGPackFieldCoverageComplete: concreteGeneratedChain.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: concreteGeneratedChain.finalIntegrationRowFamGCoverageComplete,
    finalIntegrationUsesGPack: concreteGeneratedChain.finalIntegrationUsesGPack,
    rowFamGUsesGPack: concreteGeneratedChain.rowFamGUsesGPack,
    finalTheoremUsesFinalIntegration: concreteGeneratedChain.finalTheoremUsesFinalIntegration,
    rowFamFinalUsesFinalTheorem: concreteGeneratedChain.rowFamFinalUsesFinalTheorem,
    finalMatchUsesGPack: concreteGeneratedChain.finalMatchUsesGPack,
    satDecisionUsesGPack: concreteGeneratedChain.satDecisionUsesGPack,

    concretePCCPack: concreteGeneratedChain.concretePCCPack,
    concretePCCPackCoverageDigest: concreteGeneratedChain.concretePCCPackCoverageDigest,
    pccPackPublicConclusionOnlyAfterAcceptRun: concreteGeneratedChain.pccPackPublicConclusionOnlyAfterAcceptRun,
    pccPackLinkedToKBundle: concreteGeneratedChain.pccPackLinkedToKBundle,
    pccPackLinkedToHardCheck: concreteGeneratedChain.pccPackLinkedToHardCheck,
    pccPackLinkedToRows: concreteGeneratedChain.pccPackLinkedToRows,
    pccPackLinkedToLocalPackages: concreteGeneratedChain.pccPackLinkedToLocalPackages,
    pccPackLinkedToGlobalFirewalls: concreteGeneratedChain.pccPackLinkedToGlobalFirewalls,
    pccPackLinkedToGlobalProofDAG: concreteGeneratedChain.pccPackLinkedToGlobalProofDAG,
    pccPackLinkedToGPack: concreteGeneratedChain.pccPackLinkedToGPack,
    pccPackLinkedToFinalIntegration: concreteGeneratedChain.pccPackLinkedToFinalIntegration,
    pccPackLinkedToFinalTheorem: concreteGeneratedChain.pccPackLinkedToFinalTheorem,

    checkPCCPackexpRecordPresent: isPlainObject(checkPCCPackexpRecord),
    checkPCCPackexpRecordAccepted: checkPCCPackexpRecord?.tag === 'accept',
    checkPCCPackexpRecordChecker: checkPCCPackexpRecord?.checker ?? null,
    checkPCCPackexpRecordDigest,
    checkPCCPackexpRecordDigestMatchesNF: sameDigestHex0(
      checkPCCPackexpRecordDigest,
      checkPCCPackexpRecordNFDigest,
    ),
    checkPCCPackexpRecordConcretePCCPack: checkPCCPackexpRecordNF?.concretePCCPack === true,
    checkPCCPackexpRecordPccPackDigest: checkPCCPackexpRecordNF?.pccPackDigest ?? null,
    checkPCCPackexpRecordPccPackDigestMatchesConcreteRun: sameDigestHex0(
      checkPCCPackexpRecordNF?.pccPackDigest ?? null,
      concreteGeneratedChain.pccPackDigest,
    ),
    checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: (
      checkPCCPackexpRecordNF?.publicConclusionOnlyAfterAcceptRun === true
    ),
    checkPCCPackexpRecordPublicConclusionNotEmitted: (
      checkPCCPackexpRecordNF?.publicConclusionEmitted === false
    ),
    checkPCCPackexpRecordClaimBoundaryConditional: samePublicConclusion0(
      checkPCCPackexpRecordNF?.publicConclusion ?? null,
      makeClaimBoundary0(),
    ),

    generatedPCCPackexpEnvelopePresent: isPlainObject(generatedPCCPackexpEnvelope),
    generatedPCCPackexpEnvelopeDigest: isPlainObject(generatedPCCPackexpEnvelope)
      ? digestCanonical0(generatedPCCPackexpEnvelope)
      : null,
    generatedPCCPackexpGenCallGeneratePCCPack: generatedPCCPackexpEnvelope?.GenCall?.generator === 'GeneratePCCPack0',
    generatedPCCPackexpCoreOnly: generatedPCCPackexpEnvelope?.GenCall?.coreOnly === true,
    generatedPCCPackexpExcludesAcceptRun: generatedPCCPackexpEnvelope?.GenCall?.excludesAcceptRun === true,
    generatedPCCPackexpPackageMatchesConcreteRun: sameDigestHex0(
      digestCanonical0(generatedPCCPackexpMaterializedPackage ?? null),
      digestCanonical0(generatedAcceptRunEnvelope?.MaterializedPCCPack ?? null),
    ),
    generatedPCCPackexpCheckRecordMatchesConcreteRun: sameDigestHex0(
      generatedPCCPackexpCheckRecordDigest,
      checkPCCPackexpRecordDigest,
    ),
    generatedPCCPackexpCheckRecordAccepted: generatedPCCPackexpCheckRecord?.tag === 'accept',
    generatedPCCPackexpCheckRecordChecker: generatedPCCPackexpCheckRecord?.checker ?? null,
    generatedPCCPackexpCheckRecordDigest,
    generatedPCCPackexpCheckRecordDigestMatchesNF: sameDigestHex0(
      generatedPCCPackexpCheckRecordDigest,
      generatedPCCPackexpCheckRecordNFDigest,
    ),
    generatedPCCPackexpCheckRecordClaimBoundaryConditional: samePublicConclusion0(
      generatedPCCPackexpCheckRecordNF?.publicConclusion ?? null,
      makeClaimBoundary0(),
    ),
    generatedPCCPackexpLinkageGeneratedPackageDigestMatches: sameDigestHex0(
      generatedPCCPackexpEnvelope?.Linkage?.generatedPackageDigest ?? null,
      digestCanonical0(generatedPCCPackexpGeneratedPackage ?? null),
    ),
    generatedPCCPackexpLinkageCheckRecordDigestMatches: sameDigestHex0(
      generatedPCCPackexpEnvelope?.Linkage?.checkPCCPackexpRecordDigest ?? null,
      generatedPCCPackexpCheckRecordDigest,
    ),

    checkGeneratedPCCPackexpRecordPresent: isPlainObject(checkGeneratedPCCPackexpRecord),
    checkGeneratedPCCPackexpRecordAccepted: checkGeneratedPCCPackexpRecord?.tag === 'accept',
    checkGeneratedPCCPackexpRecordChecker: checkGeneratedPCCPackexpRecord?.checker ?? null,
    checkGeneratedPCCPackexpRecordDigest,
    checkGeneratedPCCPackexpRecordDigestMatchesNF: sameDigestHex0(
      checkGeneratedPCCPackexpRecordDigest,
      checkGeneratedPCCPackexpRecordNFDigest,
    ),
    checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope: sameDigestHex0(
      checkGeneratedPCCPackexpRecordNF?.generatedPackageDigest ?? null,
      digestCanonical0(generatedPCCPackexpEnvelope?.GeneratedPCCPack ?? null),
    ),
    checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope: sameDigestHex0(
      checkGeneratedPCCPackexpRecordNF?.checkPCCPackexpRecordDigest ?? null,
      digestFromRecord0(generatedPCCPackexpEnvelope?.CheckPCCPackexpRecord ?? null),
    ),

    generatedPCCPackexpBoot0: checkGeneratedPCCPackexpRecordNF?.generatedPackageBoot0 === true,
    generatedPCCPackexpBoot0Accepted: checkGeneratedPCCPackexpRecordNF?.boot0Accepted === true,
    generatedPCCPackexpBoot0Kind: checkGeneratedPCCPackexpRecordNF?.boot0Kind ?? null,
    generatedPCCPackexpBoot0Digest: checkGeneratedPCCPackexpRecordNF?.boot0Digest ?? null,
    generatedPCCPackexpBoot0CheckDigest: checkGeneratedPCCPackexpRecordNF?.boot0CheckDigest ?? null,
    generatedPCCPackexpBoot0CanonicalByteDigest:
      checkGeneratedPCCPackexpRecordNF?.boot0CanonicalByteDigest ?? null,
    generatedPCCPackexpBoot0RowCount: checkGeneratedPCCPackexpRecordNF?.boot0RowCount ?? null,
    generatedPCCPackexpBoot0KernelRuleCount:
      checkGeneratedPCCPackexpRecordNF?.boot0KernelRuleCount ?? null,
    generatedPCCPackexpBoot0JsonMaterialized:
      checkGeneratedPCCPackexpRecordNF?.boot0JsonMaterialized === true,
    generatedPCCPackexpBoot0NoFixtureMarkers:
      checkGeneratedPCCPackexpRecordNF?.boot0NoFixtureMarkers === true,
    generatedPCCPackexpBoot0BootBatchDigest:
      checkGeneratedPCCPackexpRecordNF?.boot0BootBatchDigest ?? null,
    generatedPCCPackexpBoot0BootAuditDigest:
      checkGeneratedPCCPackexpRecordNF?.boot0BootAuditDigest ?? null,
    generatedPCCPackexpBoot0LinkedToPCCPack:
      checkGeneratedPCCPackexpRecordNF?.boot0LinkedToPCCPack === true,
    generatedPCCPackexpBoot0LinkedToCoreDigestMap:
      checkGeneratedPCCPackexpRecordNF?.boot0LinkedToCoreDigestMap === true,
    generatedPCCPackexpBoot0DigestMatchesGeneratedPackage: sameDigestHex0(
      checkGeneratedPCCPackexpRecordNF?.boot0Digest ?? null,
      digestCanonical0(generatedPCCPackexpBoot0),
    ),
    generatedPCCPackexpBoot0DigestMatchesCoreDigestMap: sameDigestHex0(
      checkGeneratedPCCPackexpRecordNF?.boot0Digest ?? null,
      generatedPCCPackexpCoreBootDigest,
    ),

    generatedPCCPackexpBoot0B0Accepted:
      checkGeneratedPCCPackexpRecordNF?.boot0B0Accepted === true,
    generatedPCCPackexpBoot0B0Digest:
      checkGeneratedPCCPackexpRecordNF?.boot0B0Digest ?? null,
    generatedPCCPackexpBoot0B0CoverageDigest:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoverageDigest ?? null,
    generatedPCCPackexpBoot0B0FamilyCount:
      checkGeneratedPCCPackexpRecordNF?.boot0B0FamilyCount ?? null,
    generatedPCCPackexpBoot0B0RequiredFamilyCount:
      checkGeneratedPCCPackexpRecordNF?.boot0B0RequiredFamilyCount ?? null,
    generatedPCCPackexpBoot0B0Families:
      checkGeneratedPCCPackexpRecordNF?.boot0B0Families ?? null,
    generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent:
      checkGeneratedPCCPackexpRecordNF?.boot0B0AllRequiredFamiliesPresent === true,
    generatedPCCPackexpBoot0B0CoversIface:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversIface === true,
    generatedPCCPackexpBoot0B0CoversSched:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversSched === true,
    generatedPCCPackexpBoot0B0CoversNF:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversNF === true,
    generatedPCCPackexpBoot0B0CoversTruthEval:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversTruthEval === true,
    generatedPCCPackexpBoot0B0CoversRel:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversRel === true,
    generatedPCCPackexpBoot0B0CoversCharge:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversCharge === true,
    generatedPCCPackexpBoot0B0CoversObl:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversObl === true,
    generatedPCCPackexpBoot0B0CoversArith:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversArith === true,
    generatedPCCPackexpBoot0B0CoversMode:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversMode === true,
    generatedPCCPackexpBoot0B0CoversRoute:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversRoute === true,
    generatedPCCPackexpBoot0B0CoversHash:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversHash === true,
    generatedPCCPackexpBoot0B0CoversImport:
      checkGeneratedPCCPackexpRecordNF?.boot0B0CoversImport === true,

    generatedPCCPackexpKernelSeed0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageKernelSeed0 === true,
    generatedPCCPackexpKernelSeed0Accepted:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0Accepted === true,
    generatedPCCPackexpKernelSeed0Kind:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0Kind ?? null,
    generatedPCCPackexpKernelSeed0Digest:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0Digest ?? null,
    generatedPCCPackexpKernelSeed0RuleCount:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0RuleCount ?? null,
    generatedPCCPackexpKernelSeed0RequiredRuleCount:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0RequiredRuleCount ?? null,
    generatedPCCPackexpKernelSeed0Rules:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0Rules ?? null,
    generatedPCCPackexpKernelSeed0AllRequiredRulesPresent:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0AllRequiredRulesPresent === true,
    generatedPCCPackexpKernelSeed0HasEq:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasEq === true,
    generatedPCCPackexpKernelSeed0HasSubst:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasSubst === true,
    generatedPCCPackexpKernelSeed0HasRecord:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasRecord === true,
    generatedPCCPackexpKernelSeed0HasDAGInd:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasDAGInd === true,
    generatedPCCPackexpKernelSeed0HasLedgerInd:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasLedgerInd === true,
    generatedPCCPackexpKernelSeed0HasOblTopoInd:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasOblTopoInd === true,
    generatedPCCPackexpKernelSeed0HasTraceInd:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasTraceInd === true,
    generatedPCCPackexpKernelSeed0HasFiniteExhaust:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasFiniteExhaust === true,
    generatedPCCPackexpKernelSeed0HasDPInd:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasDPInd === true,
    generatedPCCPackexpKernelSeed0HasHall:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasHall === true,
    generatedPCCPackexpKernelSeed0HasRankInd:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasRankInd === true,
    generatedPCCPackexpKernelSeed0HasMinCounterexample:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasMinCounterexample === true,
    generatedPCCPackexpKernelSeed0HasIntArith:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasIntArith === true,
    generatedPCCPackexpKernelSeed0HasTransport:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasTransport === true,
    generatedPCCPackexpKernelSeed0HasTruthVec:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasTruthVec === true,
    generatedPCCPackexpKernelSeed0HasFiniteRel:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0HasFiniteRel === true,
    generatedPCCPackexpKernelSeed0ProofNodeKindCount:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0ProofNodeKindCount ?? null,
    generatedPCCPackexpKernelSeed0ProofNodeKinds:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0ProofNodeKinds ?? null,
    generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0AllRequiredProofNodeKindsPresent === true,
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0ProofRefsRejectOpaque === true,
    generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0ProofRefsTypedAcyclic === true,
    generatedPCCPackexpKernelSeed0ProofRefsHashIndependent:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0ProofRefsHashIndependent === true,
    generatedPCCPackexpKernelSeed0PiBootDigestMatches:
      checkGeneratedPCCPackexpRecordNF?.kernelSeed0PiBootDigestMatches === true,

    generatedPCCPackexpCodec0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageCodec0 === true,
    generatedPCCPackexpCodec0Accepted:
      checkGeneratedPCCPackexpRecordNF?.codec0Accepted === true,
    generatedPCCPackexpCodec0Kind:
      checkGeneratedPCCPackexpRecordNF?.codec0Kind ?? null,
    generatedPCCPackexpCodec0Digest:
      checkGeneratedPCCPackexpRecordNF?.codec0Digest ?? null,
    generatedPCCPackexpCodec0Canonical:
      checkGeneratedPCCPackexpRecordNF?.codec0Canonical === true,
    generatedPCCPackexpCodec0NaturalEncoding:
      checkGeneratedPCCPackexpRecordNF?.codec0NaturalEncoding ?? null,
    generatedPCCPackexpCodec0NaturalEncodingCanonical:
      checkGeneratedPCCPackexpRecordNF?.codec0NaturalEncoding === 'u32be-length-shortest-big-endian-magnitude',
    generatedPCCPackexpCodec0IntegerEncoding:
      checkGeneratedPCCPackexpRecordNF?.codec0IntegerEncoding ?? null,
    generatedPCCPackexpCodec0IntegerEncodingCanonical:
      checkGeneratedPCCPackexpRecordNF?.codec0IntegerEncoding === 'sign-byte-plus-canonical-natural-no-negative-zero',
    generatedPCCPackexpCodec0StringEncoding:
      checkGeneratedPCCPackexpRecordNF?.codec0StringEncoding ?? null,
    generatedPCCPackexpCodec0StringEncodingCanonical:
      checkGeneratedPCCPackexpRecordNF?.codec0StringEncoding === 'utf8-nfc-length-prefixed',
    generatedPCCPackexpCodec0TopLevelConsumesAllBytes:
      checkGeneratedPCCPackexpRecordNF?.codec0TopLevelConsumesAllBytes === true,
    generatedPCCPackexpCodec0NormalFormSerialization:
      checkGeneratedPCCPackexpRecordNF?.codec0NormalFormSerialization ?? null,
    generatedPCCPackexpCodec0NormalFormSerializationCanonical:
      checkGeneratedPCCPackexpRecordNF?.codec0NormalFormSerialization === 'canonical-json-v0',
    generatedPCCPackexpCodec0PiBootDigestMatches:
      checkGeneratedPCCPackexpRecordNF?.codec0PiBootDigestMatches === true,

    generatedPCCPackexpDigest0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageDigest0 === true,
    generatedPCCPackexpDigest0Accepted:
      checkGeneratedPCCPackexpRecordNF?.digest0Accepted === true,
    generatedPCCPackexpDigest0Kind:
      checkGeneratedPCCPackexpRecordNF?.digest0Kind ?? null,
    generatedPCCPackexpDigest0Digest:
      checkGeneratedPCCPackexpRecordNF?.digest0Digest ?? null,
    generatedPCCPackexpDigest0Alg:
      checkGeneratedPCCPackexpRecordNF?.digest0Alg ?? null,
    generatedPCCPackexpDigest0AlgSHA256:
      checkGeneratedPCCPackexpRecordNF?.digest0Alg === 'SHA256',
    generatedPCCPackexpDigest0Bytes:
      checkGeneratedPCCPackexpRecordNF?.digest0Bytes ?? null,
    generatedPCCPackexpDigest0BytesCanonicalJson:
      checkGeneratedPCCPackexpRecordNF?.digest0Bytes === 'canonical-json-v0',
    generatedPCCPackexpDigest0EqualityNotObjectEquality:
      checkGeneratedPCCPackexpRecordNF?.digest0EqualityNotObjectEquality === true,
    generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup:
      checkGeneratedPCCPackexpRecordNF?.digest0FullKeyComparisonAfterHashLookup === true,
    generatedPCCPackexpDigest0PiBootDigestMatches:
      checkGeneratedPCCPackexpRecordNF?.digest0PiBootDigestMatches === true,

    rowsEnvelopeKind: concreteGeneratedChain.rowsEnvelopeKind,
    localPackagesEnvelopeKind: concreteGeneratedChain.localPackagesEnvelopeKind,
    globalFirewallsEnvelopeKind: concreteGeneratedChain.globalFirewallsEnvelopeKind,
    globalProofDAGEnvelopeKind: concreteGeneratedChain.globalProofDAGEnvelopeKind,
    kBundleEnvelopeKind: concreteGeneratedChain.kBundleEnvelopeKind,
    hardEnvelopeKind: concreteGeneratedChain.hardEnvelopeKind,
    finalIntegrationEnvelopeKind: concreteGeneratedChain.finalIntegrationEnvelopeKind,

    kBundleCoverageDigest: concreteGeneratedChain.kBundleCoverageDigest,
    hardCoverageDigest: concreteGeneratedChain.hardCoverageDigest,
    finalIntegrationLinksDigest: concreteGeneratedChain.finalIntegrationLinksDigest,

    generatedAcceptRunDigest,
    finalCertificateGeneratedAcceptRunDigest: finalGeneratedAcceptRunDigest,
    finalCertificateUsesConcreteAcceptRun: sameDigestHex0(generatedAcceptRunDigest, finalGeneratedAcceptRunDigest),

    pccPackDigest,
    certificatePccPackDigest,
    certificatePccPackDigestMatchesConcreteRun: sameDigestHex0(pccPackDigest, certificatePccPackDigest),

    acceptRunDigest,
    certificateAcceptRunDigest,
    certificateAcceptRunDigestMatchesConcreteRun: sameDigestHex0(acceptRunDigest, certificateAcceptRunDigest),

    finalVerdictRecordDigest,
    certificateFinalVerdictRecordDigest,
    certificateFinalVerdictDigestMatchesRecord: sameDigestHex0(finalVerdictRecordDigest, certificateFinalVerdictRecordDigest),

    publicTheorem: certificate?.publicTheorem ?? null,
    publicTheoremMatchesAcceptedFinalVerdict: samePublicConclusion0(
      certificate?.publicTheorem ?? null,
      finalVerdict?.NF?.publicConclusion ?? finalVerdict?.nf?.publicConclusion ?? null,
    ),

    canonicalByteRoots: certificate?.canonicalByteRoots ?? null,
    acceptanceTranscript: certificate?.acceptanceTranscript ?? null,
  };
}

export async function CheckConcreteMaterializedFinalCertificate0(
  input,
  config = makeConcreteMaterializedFinalCertificateConfig0(),
) {
  const checker = 'CheckConcreteMaterializedFinalCertificate0';
  const ledger = [];
  const cfg = makeConcreteMaterializedFinalCertificateConfig0(config);
  const envelope = normalizeInput0(input);

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

  if (cfg.checkConcreteGeneratedAcceptRun === true) {
    const record = await CheckConcreteMaterializedGeneratedAcceptRun0(
      envelope.ConcreteGeneratedAcceptRunEnvelope,
      cfg.concreteGeneratedAcceptRunConfig ?? {},
    );
    const result = recordToValidation0(record, ['ConcreteGeneratedAcceptRunEnvelope']);

    ledger.push({
      phase: 'CheckConcreteMaterializedGeneratedAcceptRun0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteGeneratedAcceptRun`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkFinalCertificate === true) {
    const record = await CheckMaterializedFinalCertificate0(
      envelope.FinalCertificateEnvelope,
      cfg.finalCertificateConfig ?? {},
    );
    const result = recordToValidation0(record, ['FinalCertificateEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedFinalCertificate0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.FinalCertificate`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const recomputedChain = summarizeConcreteFinalCertificateChain0({
    concreteGeneratedAcceptRunEnvelope: envelope.ConcreteGeneratedAcceptRunEnvelope,
    finalCertificateEnvelope: envelope.FinalCertificateEnvelope,
  });

  if (cfg.checkConcreteChain === true) {
    const chain = validateConcreteFinalCertificateChain0(envelope.ConcreteChain, recomputedChain);

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

  const markerInventory = collectFixtureMarkers0(envelope, ['ConcreteMaterializedFinalCertificate0']);

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
    kind: 'ConcreteMaterializedFinalCertificate0NF',
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

    kBundleEnvelopeKind: recomputedChain.kBundleEnvelopeKind,
    hardEnvelopeKind: recomputedChain.hardEnvelopeKind,
    finalIntegrationEnvelopeKind: recomputedChain.finalIntegrationEnvelopeKind,

    kBundleCoverageDigest: recomputedChain.kBundleCoverageDigest,
    hardCoverageDigest: recomputedChain.hardCoverageDigest,
    finalIntegrationLinksDigest: recomputedChain.finalIntegrationLinksDigest,

    finalCertificateUsesConcreteAcceptRun: recomputedChain.finalCertificateUsesConcreteAcceptRun,
    certificatePccPackDigestMatchesConcreteRun: recomputedChain.certificatePccPackDigestMatchesConcreteRun,
    certificateAcceptRunDigestMatchesConcreteRun: recomputedChain.certificateAcceptRunDigestMatchesConcreteRun,
    certificateFinalVerdictDigestMatchesRecord: recomputedChain.certificateFinalVerdictDigestMatchesRecord,
    publicTheoremMatchesAcceptedFinalVerdict: recomputedChain.publicTheoremMatchesAcceptedFinalVerdict,

    pccPackDigest: recomputedChain.pccPackDigest,
    acceptRunDigest: recomputedChain.acceptRunDigest,
    finalVerdictRecordDigest: recomputedChain.finalVerdictRecordDigest,
    finalCertificateDigest: digestCanonical0(envelope.FinalCertificateEnvelope.Certificate),
    finalCertificateEnvelopeDigest: digestCanonical0(envelope.FinalCertificateEnvelope),
    concreteGeneratedAcceptRunEnvelopeDigest: digestCanonical0(envelope.ConcreteGeneratedAcceptRunEnvelope),
    concreteChainDigest: digestCanonical0(recomputedChain),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),

    publicTheorem: recomputedChain.publicTheorem,
    canonicalByteRoots: recomputedChain.canonicalByteRoots,
    acceptanceTranscript: recomputedChain.acceptanceTranscript,

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

export async function writeConcreteMaterializedFinalCertificateFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteMaterializedFinalCertificateFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteMaterializedFinalCertificate0(options);
  const checked = await CheckConcreteMaterializedFinalCertificate0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteMaterializedFinalCertificate0.json');
  const concreteAcceptRunPath = path.join(outDir, 'ConcreteMaterializedGeneratedAcceptRun0.json');
  const finalCertificateEnvelopePath = path.join(outDir, 'MaterializedFinalCertificate0.json');
  const certificatePath = path.join(outDir, 'FinalCertificate0.json');
  const chainPath = path.join(outDir, 'ConcreteFinalCertificateChain0.json');
  const checkPath = path.join(outDir, 'ConcreteMaterializedFinalCertificate0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(concreteAcceptRunPath, envelope.ConcreteGeneratedAcceptRunEnvelope);
  await writeJsonFile0(finalCertificateEnvelopePath, envelope.FinalCertificateEnvelope);
  await writeJsonFile0(certificatePath, envelope.FinalCertificateEnvelope.Certificate);
  await writeJsonFile0(chainPath, envelope.ConcreteChain);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      concreteAcceptRunPath,
      finalCertificateEnvelopePath,
      certificatePath,
      chainPath,
      checkPath,
    },
  };
}

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'MaterializedFinalCertificate0') {
    return {
      kind: 'ConcreteMaterializedFinalCertificate0',
      version: CHECKER_VERSION,
      ConcreteGeneratedAcceptRunEnvelope: null,
      FinalCertificateEnvelope: input,
      ConcreteChain: null,
      Linkage: null,
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteMaterializedFinalCertificateConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteMaterializedFinalCertificateConfig0') {
    return validationReject0(['kind'], 'ConcreteMaterializedFinalCertificateConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedFinalCertificateConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkConcreteGeneratedAcceptRun',
    'checkFinalCertificate',
    'checkConcreteChain',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteMaterializedFinalCertificateConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.concreteGeneratedAcceptRunConfig)) {
    return validationReject0(['concreteGeneratedAcceptRunConfig'], 'concreteGeneratedAcceptRunConfig must be an object', {
      actual: typeof config.concreteGeneratedAcceptRunConfig,
    });
  }

  if (!isPlainObject(config.finalCertificateConfig)) {
    return validationReject0(['finalCertificateConfig'], 'finalCertificateConfig must be an object', {
      actual: typeof config.finalCertificateConfig,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedFinalCertificateConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteMaterializedFinalCertificate0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteMaterializedFinalCertificate0') {
    return validationReject0(['kind'], 'ConcreteMaterializedFinalCertificate0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedFinalCertificate0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.ConcreteGeneratedAcceptRunEnvelope)) {
    return validationReject0(['ConcreteGeneratedAcceptRunEnvelope'], 'ConcreteMaterializedFinalCertificate0 must include ConcreteGeneratedAcceptRunEnvelope', {
      actual: typeof envelope.ConcreteGeneratedAcceptRunEnvelope,
    });
  }

  if (!isPlainObject(envelope.FinalCertificateEnvelope)) {
    return validationReject0(['FinalCertificateEnvelope'], 'ConcreteMaterializedFinalCertificate0 must include FinalCertificateEnvelope', {
      actual: typeof envelope.FinalCertificateEnvelope,
    });
  }

  if (!isPlainObject(envelope.ConcreteChain)) {
    return validationReject0(['ConcreteChain'], 'ConcreteMaterializedFinalCertificate0 must include ConcreteChain', {
      actual: typeof envelope.ConcreteChain,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedFinalCertificateShape0NF',
  });
}

function validateConcreteFinalCertificateChain0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['ConcreteChain'], 'Concrete final-certificate chain must match recomputed chain summary', {
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

    'finalCertificateUsesConcreteAcceptRun',
    'certificatePccPackDigestMatchesConcreteRun',
    'certificateAcceptRunDigestMatchesConcreteRun',
    'certificateFinalVerdictDigestMatchesRecord',
    'publicTheoremMatchesAcceptedFinalVerdict',
  ];

  for (const field of requiredTrue) {
    if (expected[field] !== true) {
      return validationReject0(['ConcreteChain', field], `Concrete final-certificate chain must certify ${field}`, {
        actual: expected[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteFinalCertificateChain0NF',
    concreteChainDigest: digestCanonical0(expected),
    pccPackDigest: expected.pccPackDigest,
    finalVerdictRecordDigest: expected.finalVerdictRecordDigest,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['ConcreteMaterializedFinalCertificate0'], 'ConcreteMaterializedFinalCertificate0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ConcreteMaterializedFinalCertificate0'], 'ConcreteMaterializedFinalCertificate0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteFinalCertificateJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope, concreteChain) {
  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteFinalCertificateLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteMaterializedFinalCertificate0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const expected = {
    concreteGeneratedAcceptRunEnvelopeDigest: digestCanonical0(envelope.ConcreteGeneratedAcceptRunEnvelope),
    generatedAcceptRunEnvelopeDigest: digestCanonical0(envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope),
    finalCertificateEnvelopeDigest: digestCanonical0(envelope.FinalCertificateEnvelope),
    finalCertificateDigest: digestCanonical0(envelope.FinalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(envelope.FinalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest: envelope.FinalCertificateEnvelope.FinalVerdict.Digest ?? envelope.FinalCertificateEnvelope.FinalVerdict.digest,
    acceptRunDigest: digestCanonical0(envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun),
    pccPackDigest: digestCanonical0(envelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen),
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
    kind: 'ConcreteFinalCertificateLinkage0NF',
    present: true,
    ...expected,
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ConcreteFinalCertificateFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === CONCRETE_CERT_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== CONCRETE_CERT_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== CONCRETE_CERT_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'concrete materialized final certificate contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ConcreteFinalCertificateNoForbiddenFixtureMarkers0NF',
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
      CONCRETE_CERT_SYNTHETIC_MARKER0,
      ...CONCRETE_CERT_FORBIDDEN_MARKERS0,
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

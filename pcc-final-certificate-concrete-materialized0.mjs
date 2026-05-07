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

    generatedPCCPackexpIfaceDict0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageIfaceDict0 === true,
    generatedPCCPackexpIfaceDict0Accepted:
      checkGeneratedPCCPackexpRecordNF?.ifaceDict0Accepted === true,
    generatedPCCPackexpIfaceDict0Kind:
      checkGeneratedPCCPackexpRecordNF?.ifaceDict0Kind ?? null,
    generatedPCCPackexpIfaceDict0Digest:
      checkGeneratedPCCPackexpRecordNF?.ifaceDict0Digest ?? null,
    generatedPCCPackexpIfaceDict0ForbiddenSymbolCount:
      checkGeneratedPCCPackexpRecordNF?.ifaceDict0ForbiddenSymbolCount ?? null,
    generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent:
      checkGeneratedPCCPackexpRecordNF?.ifaceDict0RequiredForbiddenSymbolsPresent === true,
    generatedPCCPackexpIfaceDict0NoExecutableMinSymbols:
      checkGeneratedPCCPackexpRecordNF?.ifaceDict0NoExecutableMinSymbols === true,
    generatedPCCPackexpIfaceDict0PublicConstructorsPresent:
      checkGeneratedPCCPackexpRecordNF?.ifaceDict0PublicConstructorsPresent === true,
    generatedPCCPackexpIfaceDict0CriticalKindsPresent:
      checkGeneratedPCCPackexpRecordNF?.ifaceDict0CriticalKindsPresent === true,
    generatedPCCPackexpIfaceDict0RouteTokensPresent:
      checkGeneratedPCCPackexpRecordNF?.ifaceDict0RouteTokensPresent === true,
    generatedPCCPackexpIfaceDict0PiBootDigestMatches:
      checkGeneratedPCCPackexpRecordNF?.ifaceDict0PiBootDigestMatches === true,

    generatedPCCPackexpSched0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageSched0 === true,
    generatedPCCPackexpSched0Accepted:
      checkGeneratedPCCPackexpRecordNF?.sched0Accepted === true,
    generatedPCCPackexpSched0Kind:
      checkGeneratedPCCPackexpRecordNF?.sched0Kind ?? null,
    generatedPCCPackexpSched0Digest:
      checkGeneratedPCCPackexpRecordNF?.sched0Digest ?? null,
    generatedPCCPackexpSched0CoreMatchesExpected:
      checkGeneratedPCCPackexpRecordNF?.sched0CoreMatchesExpected === true,
    generatedPCCPackexpSched0CoreB0:
      checkGeneratedPCCPackexpRecordNF?.sched0CoreB0 ?? null,
    generatedPCCPackexpSched0CoreK0:
      checkGeneratedPCCPackexpRecordNF?.sched0CoreK0 ?? null,
    generatedPCCPackexpSched0CoreR0:
      checkGeneratedPCCPackexpRecordNF?.sched0CoreR0 ?? null,
    generatedPCCPackexpSched0CoreH0:
      checkGeneratedPCCPackexpRecordNF?.sched0CoreH0 ?? null,
    generatedPCCPackexpSched0CoreO0:
      checkGeneratedPCCPackexpRecordNF?.sched0CoreO0 ?? null,
    generatedPCCPackexpSched0CoreRel0:
      checkGeneratedPCCPackexpRecordNF?.sched0CoreRel0 ?? null,
    generatedPCCPackexpSched0ScaleFactorsPresent:
      checkGeneratedPCCPackexpRecordNF?.sched0ScaleFactorsPresent === true,
    generatedPCCPackexpSched0SelectorBoundsPresent:
      checkGeneratedPCCPackexpRecordNF?.sched0SelectorBoundsPresent === true,
    generatedPCCPackexpSched0SelectorBoundBH:
      checkGeneratedPCCPackexpRecordNF?.sched0SelectorBoundBH ?? null,
    generatedPCCPackexpSched0SelectorBoundBTheta:
      checkGeneratedPCCPackexpRecordNF?.sched0SelectorBoundBTheta ?? null,
    generatedPCCPackexpSched0PolynomialExponent:
      checkGeneratedPCCPackexpRecordNF?.sched0PolynomialExponent ?? null,
    generatedPCCPackexpSched0PiBootDigestMatches:
      checkGeneratedPCCPackexpRecordNF?.sched0PiBootDigestMatches === true,

    generatedPCCPackexpByteLang0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageByteLang0 === true,
    generatedPCCPackexpByteLang0Accepted:
      checkGeneratedPCCPackexpRecordNF?.byteLang0Accepted === true,
    generatedPCCPackexpByteLang0Kind:
      checkGeneratedPCCPackexpRecordNF?.byteLang0Kind ?? null,
    generatedPCCPackexpByteLang0Digest:
      checkGeneratedPCCPackexpRecordNF?.byteLang0Digest ?? null,
    generatedPCCPackexpByteLang0TagCount:
      checkGeneratedPCCPackexpRecordNF?.byteLang0TagCount ?? null,
    generatedPCCPackexpByteLang0TagsUnique:
      checkGeneratedPCCPackexpRecordNF?.byteLang0TagsUnique === true,
    generatedPCCPackexpByteLang0RequiredTagsPresent:
      checkGeneratedPCCPackexpRecordNF?.byteLang0RequiredTagsPresent === true,
    generatedPCCPackexpByteLang0SortCount:
      checkGeneratedPCCPackexpRecordNF?.byteLang0SortCount ?? null,
    generatedPCCPackexpByteLang0RequiredSortsPresent:
      checkGeneratedPCCPackexpRecordNF?.byteLang0RequiredSortsPresent === true,
    generatedPCCPackexpByteLang0ConstructorCount:
      checkGeneratedPCCPackexpRecordNF?.byteLang0ConstructorCount ?? null,
    generatedPCCPackexpByteLang0RequiredConstructorsPresent:
      checkGeneratedPCCPackexpRecordNF?.byteLang0RequiredConstructorsPresent === true,
    generatedPCCPackexpByteLang0RecordCount:
      checkGeneratedPCCPackexpRecordNF?.byteLang0RecordCount ?? null,
    generatedPCCPackexpByteLang0RequiredRecordAritiesPresent:
      checkGeneratedPCCPackexpRecordNF?.byteLang0RequiredRecordAritiesPresent === true,
    generatedPCCPackexpByteLang0PiBootDigestMatches:
      checkGeneratedPCCPackexpRecordNF?.byteLang0PiBootDigestMatches === true,

    generatedPCCPackexpBootAudit0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageBootAudit0 === true,
    generatedPCCPackexpBootAudit0Accepted:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0Accepted === true,
    generatedPCCPackexpBootAudit0Checker:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0Checker ?? null,
    generatedPCCPackexpBootAudit0Digest:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0Digest ?? null,
    generatedPCCPackexpBootAudit0DigestMatchesNF:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0DigestMatchesNF === true,
    generatedPCCPackexpBootAudit0NFKind:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0NFKind ?? null,
    generatedPCCPackexpBootAudit0SuiteId:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0SuiteId ?? null,
    generatedPCCPackexpBootAudit0CaseCount:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0CaseCount ?? null,
    generatedPCCPackexpBootAudit0PositiveCount:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0PositiveCount ?? null,
    generatedPCCPackexpBootAudit0NegativeCount:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0NegativeCount ?? null,
    generatedPCCPackexpBootAudit0CoversB0Accept:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0CoversB0Accept === true,
    generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0CoversB0MissingCoverageReject === true,
    generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject:
      checkGeneratedPCCPackexpRecordNF?.bootAudit0CoversB0HashKeyTamperReject === true,

    generatedPCCPackexpPiBoot0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackagePiBoot0 === true,
    generatedPCCPackexpPiBoot0Accepted:
      checkGeneratedPCCPackexpRecordNF?.piBoot0Accepted === true,
    generatedPCCPackexpPiBoot0Kind:
      checkGeneratedPCCPackexpRecordNF?.piBoot0Kind ?? null,
    generatedPCCPackexpPiBoot0Digest:
      checkGeneratedPCCPackexpRecordNF?.piBoot0Digest ?? null,
    generatedPCCPackexpPiBoot0Materialized:
      checkGeneratedPCCPackexpRecordNF?.piBoot0Materialized === true,
    generatedPCCPackexpPiBoot0ExternalJson:
      checkGeneratedPCCPackexpRecordNF?.piBoot0ExternalJson === true,
    generatedPCCPackexpPiBoot0RefCount:
      checkGeneratedPCCPackexpRecordNF?.piBoot0RefCount ?? null,
    generatedPCCPackexpPiBoot0AllBootRefsPresent:
      checkGeneratedPCCPackexpRecordNF?.piBoot0AllBootRefsPresent === true,
    generatedPCCPackexpPiBoot0RefsMatchBootObjects:
      checkGeneratedPCCPackexpRecordNF?.piBoot0RefsMatchBootObjects === true,
    generatedPCCPackexpPiBoot0RefsIncludeByteLang0:
      checkGeneratedPCCPackexpRecordNF?.piBoot0RefsIncludeByteLang0 === true,
    generatedPCCPackexpPiBoot0RefsIncludeCodec0:
      checkGeneratedPCCPackexpRecordNF?.piBoot0RefsIncludeCodec0 === true,
    generatedPCCPackexpPiBoot0RefsIncludeDigest0:
      checkGeneratedPCCPackexpRecordNF?.piBoot0RefsIncludeDigest0 === true,
    generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0:
      checkGeneratedPCCPackexpRecordNF?.piBoot0RefsIncludeIfaceDict0 === true,
    generatedPCCPackexpPiBoot0RefsIncludeSched0:
      checkGeneratedPCCPackexpRecordNF?.piBoot0RefsIncludeSched0 === true,
    generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0:
      checkGeneratedPCCPackexpRecordNF?.piBoot0RefsIncludeKernelSeed0 === true,
    generatedPCCPackexpPiBoot0RefsIncludeB0:
      checkGeneratedPCCPackexpRecordNF?.piBoot0RefsIncludeB0 === true,
    generatedPCCPackexpPiBoot0RefsIncludeBootAudit0:
      checkGeneratedPCCPackexpRecordNF?.piBoot0RefsIncludeBootAudit0 === true,

    generatedPCCPackexpConcreteKBundle0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageConcreteKBundle0 === true,
    generatedPCCPackexpConcreteKBundle0Accepted:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0Accepted === true,
    generatedPCCPackexpConcreteKBundle0Checker:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0Checker ?? null,
    generatedPCCPackexpConcreteKBundle0Digest:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0Digest ?? null,
    generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0MaterializedKBundleDigest ?? null,
    generatedPCCPackexpConcreteKBundle0BootDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0BootDigest ?? null,
    generatedPCCPackexpConcreteKBundle0KImplDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0KImplDigest ?? null,
    generatedPCCPackexpConcreteKBundle0K0Digest:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0K0Digest ?? null,
    generatedPCCPackexpConcreteKBundle0SigmaDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0SigmaDigest ?? null,
    generatedPCCPackexpConcreteKBundle0ReflectionDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0ReflectionDigest ?? null,
    generatedPCCPackexpConcreteKBundle0ProofInventoryDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0ProofInventoryDigest ?? null,
    generatedPCCPackexpConcreteKBundle0KernelRuleCount:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0KernelRuleCount ?? null,
    generatedPCCPackexpConcreteKBundle0ConformanceNodeCount:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0ConformanceNodeCount ?? null,
    generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0KernelRuleCoverageComplete === true,
    generatedPCCPackexpConcreteKBundle0SigmaTheoremCount:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0SigmaTheoremCount ?? null,
    generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0SigmaCoverageComplete === true,
    generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0SigmaProofRefsResolve === true,
    generatedPCCPackexpConcreteKBundle0ReflectionCount:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0ReflectionCount ?? null,
    generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0ReflectionCoverageComplete === true,
    generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0ReflectionProofRefsResolve === true,
    generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0NoOpaqueProofRefs === true,
    generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0NoExecutableMinSymbols === true,
    generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0:
      checkGeneratedPCCPackexpRecordNF?.concreteKBundle0LinkedToGeneratedBoot0 === true,

    generatedPCCPackexpConcreteHard0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageConcreteHard0 === true,
    generatedPCCPackexpConcreteHard0Accepted:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0Accepted === true,
    generatedPCCPackexpConcreteHard0Checker:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0Checker ?? null,
    generatedPCCPackexpConcreteHard0Digest:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0Digest ?? null,
    generatedPCCPackexpConcreteHard0MaterializedHardDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0MaterializedHardDigest ?? null,
    generatedPCCPackexpConcreteHard0HardCheckDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0HardCheckDigest ?? null,
    generatedPCCPackexpConcreteHard0CoverageDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0CoverageDigest ?? null,
    generatedPCCPackexpConcreteHard0CheckerCount:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0CheckerCount ?? null,
    generatedPCCPackexpConcreteHard0CheckerCoverageComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0CheckerCoverageComplete === true,
    generatedPCCPackexpConcreteHard0RowKeyFieldCount:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0RowKeyFieldCount ?? null,
    generatedPCCPackexpConcreteHard0RowKeyCoverageComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0RowKeyCoverageComplete === true,
    generatedPCCPackexpConcreteHard0RoutePriorityComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0RoutePriorityComplete === true,
    generatedPCCPackexpConcreteHard0ProofRefPolicyComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0ProofRefPolicyComplete === true,
    generatedPCCPackexpConcreteHard0HashDisciplineComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0HashDisciplineComplete === true,
    generatedPCCPackexpConcreteHard0NoMinCoverageComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0NoMinCoverageComplete === true,
    generatedPCCPackexpConcreteHard0ForbiddenSymbolCount:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0ForbiddenSymbolCount ?? null,
    generatedPCCPackexpConcreteHard0ImportPolicyComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0ImportPolicyComplete === true,
    generatedPCCPackexpConcreteHard0ForbiddenImportEdgeCount:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0ForbiddenImportEdgeCount ?? null,
    generatedPCCPackexpConcreteHard0ReflectionPolicyComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0ReflectionPolicyComplete === true,
    generatedPCCPackexpConcreteHard0BoundsPolicyComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0BoundsPolicyComplete === true,
    generatedPCCPackexpConcreteHard0DiagnosticsPolicyComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0DiagnosticsPolicyComplete === true,
    generatedPCCPackexpConcreteHard0LinkedToPCCPack:
      checkGeneratedPCCPackexpRecordNF?.concreteHard0LinkedToPCCPack === true,

    generatedPCCPackexpConcreteRows0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageConcreteRows0 === true,
    generatedPCCPackexpConcreteRows0Accepted:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0Accepted === true,
    generatedPCCPackexpConcreteRows0Checker:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0Checker ?? null,
    generatedPCCPackexpConcreteRows0Digest:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0Digest ?? null,
    generatedPCCPackexpConcreteRows0RowPackDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0RowPackDigest ?? null,
    generatedPCCPackexpConcreteRows0RowPackObjectDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0RowPackObjectDigest ?? null,
    generatedPCCPackexpConcreteRows0BootDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0BootDigest ?? null,
    generatedPCCPackexpConcreteRows0IfaceHash:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0IfaceHash ?? null,
    generatedPCCPackexpConcreteRows0SchedHash:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0SchedHash ?? null,
    generatedPCCPackexpConcreteRows0RowCount:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0RowCount ?? null,
    generatedPCCPackexpConcreteRows0RowCountComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0RowCount === 39,
    generatedPCCPackexpConcreteRows0BatchCount:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0BatchCount ?? null,
    generatedPCCPackexpConcreteRows0BatchCountComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0BatchCount === 13,
    generatedPCCPackexpConcreteRows0FamilyCount:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0FamilyCount ?? null,
    generatedPCCPackexpConcreteRows0FamilyCountComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0FamilyCount === 39,
    generatedPCCPackexpConcreteRows0ConcreteIfaceHash:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0ConcreteIfaceHash === true,
    generatedPCCPackexpConcreteRows0SyntheticIfaceHashCount:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0SyntheticIfaceHashCount ?? null,
    generatedPCCPackexpConcreteRows0NoSyntheticIfaceHash:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0SyntheticIfaceHashCount === 0,
    generatedPCCPackexpConcreteRows0ScaffoldMarkerCount:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0ScaffoldMarkerCount ?? null,
    generatedPCCPackexpConcreteRows0NoScaffoldMarkers:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0ScaffoldMarkerCount === 0,
    generatedPCCPackexpConcreteRows0LinkedToGeneratedBoot0:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0LinkedToGeneratedBoot0 === true,
    generatedPCCPackexpConcreteRows0LinkedToPCCPack:
      checkGeneratedPCCPackexpRecordNF?.concreteRows0LinkedToPCCPack === true,

    generatedPCCPackexpConcreteGlobalProofDAG0:
      checkGeneratedPCCPackexpRecordNF?.generatedPackageConcreteGlobalProofDAG0 === true,
    generatedPCCPackexpConcreteGlobalProofDAG0Accepted:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0Accepted === true,
    generatedPCCPackexpConcreteGlobalProofDAG0Checker:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0Checker ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0Digest:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0Digest ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0GlobalProofDAGDigest ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGObjectDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0GlobalProofDAGObjectDigest ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0MaterializedGlobalProofDAGDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0MaterializedGlobalProofDAGDigest ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0KImplDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0KImplDigest ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0RowPackDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0RowPackDigest ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0LocalPackagesDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0LocalPackagesDigest ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalFirewallsDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0GlobalFirewallsDigest ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleProofInventoryDigest:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0KBundleProofInventoryDigest ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleKernelRuleCoverageComplete:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0KBundleKernelRuleCoverageComplete === true,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleSigmaProofRefsResolve:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0KBundleSigmaProofRefsResolve === true,
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleReflectionProofRefsResolve:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0KBundleReflectionProofRefsResolve === true,
    generatedPCCPackexpConcreteGlobalProofDAG0NodeCount:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0NodeCount ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0NodeCountMinimum:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0NodeCountMinimum === true,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalTheoremCount:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0FinalTheoremCount ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalPackageSoundness:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0FinalPackageSoundness === true,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalGeneratedPackageSufficiency:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0FinalGeneratedPackageSufficiency === true,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP === true,
    generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP === true,
    generatedPCCPackexpConcreteGlobalProofDAG0IfaceHash:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0IfaceHash ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0SchedHash:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0SchedHash ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0IfaceMatchesRows:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0IfaceMatchesRows === true,
    generatedPCCPackexpConcreteGlobalProofDAG0SchedMatchesKImpl:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0SchedMatchesKImpl === true,
    generatedPCCPackexpConcreteGlobalProofDAG0SyntheticMarkerCount:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0SyntheticMarkerCount ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0ForbiddenMarkerCount:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0ForbiddenMarkerCount ?? null,
    generatedPCCPackexpConcreteGlobalProofDAG0NoForbiddenMarkers:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0NoForbiddenMarkers === true,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGeneratedBoot0:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0LinkedToGeneratedBoot0 === true,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToKImpl:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0LinkedToKImpl === true,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToConcreteRows:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0LinkedToConcreteRows === true,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToLocalPackages:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0LinkedToLocalPackages === true,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGlobalFirewalls:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0LinkedToGlobalFirewalls === true,
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToPCCPack:
      checkGeneratedPCCPackexpRecordNF?.concreteGlobalProofDAG0LinkedToPCCPack === true,

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

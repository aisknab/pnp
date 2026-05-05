import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckReleaseAudit0,
  makeReleaseAuditConfig0,
} from './pcc-release-audit0.mjs';

import {
  CheckConcreteFinalCertificatePublicStatus0,
  makeConcreteFinalCertificatePublicStatus0,
} from './pcc-final-certificate-public-status-concrete0.mjs';

const CHECKER_VERSION = 0;

export const RELEASE_AUDIT_CONCRETE_FINAL_CERTIFICATE_GATE_PHASES0 = Object.freeze([
  'CheckReleaseAuditConcreteFinalCertificateGateInput0',
  'CheckReleaseAuditRecord0',
  'CheckConcreteFinalCertificatePublicStatus0',
  'CheckConcreteReleaseAuditPublicConclusion0',
  'CheckConcreteReleaseAuditFinalCertificateGateLinkage0',
  'EmitConcreteReleaseAuditFinalCertificateGate0',
]);

const CONCRETE_RELEASE_GATE_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const CONCRETE_RELEASE_GATE_SYNTHETIC_MARKER0 = 'synthetic';

export function makeReleaseAuditConcreteFinalCertificateGateConfig0(overrides = {}) {
  return {
    kind: 'ReleaseAuditConcreteFinalCertificateGateConfig0',
    version: CHECKER_VERSION,
    checkReleaseAuditRecord: true,
    checkConcretePublicStatus: true,
    checkPublicConclusionAlignment: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    concretePublicStatusConfig: {
      finalCertificatePublicStatusConfig: {
        checkReleaseAuditRecord: true,
      },
    },
    ...overrides,
  };
}

export async function makeReleaseAuditConcreteFinalCertificateGate0({
  ReleaseAuditRecord = null,
  ConcreteFinalCertificatePublicStatusEnvelope = null,
  runReleaseAudit = ReleaseAuditRecord === null,
  releaseAuditConfig = {},
  releaseAuditRunner = null,
  overrides = {},
} = {}) {
  const effectiveReleaseAuditRecord = ReleaseAuditRecord ?? (
    runReleaseAudit === true
      ? await runReleaseAudit0(releaseAuditRunner, releaseAuditConfig)
      : null
  );

  const concretePublicStatusEnvelope = ConcreteFinalCertificatePublicStatusEnvelope ?? await makeConcreteFinalCertificatePublicStatus0({
    ReleaseAuditRecord: effectiveReleaseAuditRecord,
  });

  const linkage = {
    kind: 'ReleaseAuditConcreteFinalCertificateGateLinkage0',
    version: CHECKER_VERSION,
    releaseAuditAttached: isPlainObject(effectiveReleaseAuditRecord),
    releaseAuditDigest: isPlainObject(effectiveReleaseAuditRecord)
      ? effectiveReleaseAuditRecord.Digest ?? effectiveReleaseAuditRecord.digest ?? digestCanonical0(effectiveReleaseAuditRecord)
      : null,
    concretePublicStatusEnvelopeDigest: digestCanonical0(concretePublicStatusEnvelope),
    publicStatusDigest: digestCanonical0(concretePublicStatusEnvelope.FinalCertificatePublicStatusEnvelope.PublicStatus),
    concreteFinalCertificateDigest: digestCanonical0(concretePublicStatusEnvelope.ConcreteFinalCertificateEnvelope),
    certificateDigest: digestCanonical0(concretePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(concretePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest:
      concretePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict.Digest ??
      concretePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict.digest ??
      null,
    acceptRunDigest: digestCanonical0(
      concretePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun,
    ),
    pccPackDigest: digestCanonical0(
      concretePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen,
    ),
    concreteChainDigest: digestCanonical0(concretePublicStatusEnvelope.ConcreteChain),
  };

  return {
    kind: 'ReleaseAuditConcreteFinalCertificateGate0',
    version: CHECKER_VERSION,
    ReleaseAuditRecord: effectiveReleaseAuditRecord,
    ConcreteFinalCertificatePublicStatusEnvelope: concretePublicStatusEnvelope,
    Linkage: linkage,
    PiReleaseAuditConcreteFinalCertificateGate: {
      kind: 'PiReleaseAuditConcreteFinalCertificateGate0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'ReleaseAuditRecord',
          digest: linkage.releaseAuditDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteFinalCertificatePublicStatus',
          digest: linkage.concretePublicStatusEnvelopeDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckReleaseAuditConcreteFinalCertificateGate0(
  input,
  config = makeReleaseAuditConcreteFinalCertificateGateConfig0(),
) {
  const checker = 'CheckReleaseAuditConcreteFinalCertificateGate0';
  const ledger = [];
  const cfg = makeReleaseAuditConcreteFinalCertificateGateConfig0(config);
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
    phase: 'CheckReleaseAuditConcreteFinalCertificateGateInput0',
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

  if (cfg.checkReleaseAuditRecord === true) {
    const releaseAudit = validateReleaseAuditRecord0(envelope.ReleaseAuditRecord);

    ledger.push({
      phase: 'CheckReleaseAuditRecord0',
      status: releaseAudit.ok ? 'pass' : 'fail',
      digest: digestCanonical0(releaseAudit.nf ?? releaseAudit.witness ?? null),
    });

    if (!releaseAudit.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ReleaseAuditRecord`,
        path: releaseAudit.path,
        witness: releaseAudit.witness,
        ledger,
      });
    }
  }

  if (cfg.checkConcretePublicStatus === true) {
    const statusRecord = await CheckConcreteFinalCertificatePublicStatus0(
      envelope.ConcreteFinalCertificatePublicStatusEnvelope,
      cfg.concretePublicStatusConfig ?? {},
    );
    const status = recordToValidation0(statusRecord, ['ConcreteFinalCertificatePublicStatusEnvelope']);

    ledger.push({
      phase: 'CheckConcreteFinalCertificatePublicStatus0',
      status: status.ok ? 'pass' : 'fail',
      digest: statusRecord.Digest ?? statusRecord.digest ?? digestCanonical0(statusRecord),
    });

    if (!status.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteFinalCertificatePublicStatus`,
        path: status.path,
        witness: status.witness,
        ledger,
      });
    }
  }

  if (cfg.checkPublicConclusionAlignment === true) {
    const alignment = validateConcretePublicConclusionAlignment0(envelope);

    ledger.push({
      phase: 'CheckConcreteReleaseAuditPublicConclusion0',
      status: alignment.ok ? 'pass' : 'fail',
      digest: digestCanonical0(alignment.nf ?? alignment.witness ?? null),
    });

    if (!alignment.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.PublicConclusion`,
        path: alignment.path,
        witness: alignment.witness,
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

  const markerInventory = collectFixtureMarkers0(envelope, ['ReleaseAuditConcreteFinalCertificateGate0']);

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
    const linkage = validateLinkage0(envelope);

    ledger.push({
      phase: 'CheckConcreteReleaseAuditFinalCertificateGateLinkage0',
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

  const releaseAuditNF = envelope.ReleaseAuditRecord.NF ?? envelope.ReleaseAuditRecord.nf ?? {};
  const publicStatus = envelope.ConcreteFinalCertificatePublicStatusEnvelope.FinalCertificatePublicStatusEnvelope.PublicStatus;
  const concreteStatus = envelope.ConcreteFinalCertificatePublicStatusEnvelope;
  const concreteNF = concreteStatus.ConcreteChain;

  const nf = {
    kind: 'ReleaseAuditConcreteFinalCertificateGate0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: RELEASE_AUDIT_CONCRETE_FINAL_CERTIFICATE_GATE_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,

    releaseAuditAttached: true,
    releaseAuditDigest: envelope.ReleaseAuditRecord.Digest ?? envelope.ReleaseAuditRecord.digest,
    releaseAuditChecker: envelope.ReleaseAuditRecord.checker,
    releaseAuditMaterializedPublicStatusGateDigest: releaseAuditNF.materializedPublicStatusGateDigest ?? null,
    releaseAuditFinalCertificatePublicStatusGateDigest: releaseAuditNF.finalCertificatePublicStatusGateDigest ?? null,

    concreteRows: concreteStatus.ConcreteChain.concreteRows,
    concreteLocalPackages: concreteStatus.ConcreteChain.concreteLocalPackages,
    concreteGlobalFirewalls: concreteStatus.ConcreteChain.concreteGlobalFirewalls,
    concreteGlobalProofDAG: concreteStatus.ConcreteChain.concreteGlobalProofDAG,
    concreteKBundle: concreteStatus.ConcreteChain.concreteKBundle,
    kBundleKernelRuleCoverageComplete: concreteStatus.ConcreteChain.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: concreteStatus.ConcreteChain.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: concreteStatus.ConcreteChain.kBundleReflectionProofRefsResolve,

    concreteHardCheck: concreteStatus.ConcreteChain.concreteHardCheck,
    hardCheckerCoverageComplete: concreteStatus.ConcreteChain.hardCheckerCoverageComplete,
    hardRowKeyCoverageComplete: concreteStatus.ConcreteChain.hardRowKeyCoverageComplete,
    hardRoutePriorityComplete: concreteStatus.ConcreteChain.hardRoutePriorityComplete,
    hardProofRefPolicyComplete: concreteStatus.ConcreteChain.hardProofRefPolicyComplete,
    hardHashDisciplineComplete: concreteStatus.ConcreteChain.hardHashDisciplineComplete,
    hardNoMinCoverageComplete: concreteStatus.ConcreteChain.hardNoMinCoverageComplete,
    hardImportPolicyComplete: concreteStatus.ConcreteChain.hardImportPolicyComplete,
    hardReflectionPolicyComplete: concreteStatus.ConcreteChain.hardReflectionPolicyComplete,
    hardBoundsPolicyComplete: concreteStatus.ConcreteChain.hardBoundsPolicyComplete,
    hardDiagnosticsPolicyComplete: concreteStatus.ConcreteChain.hardDiagnosticsPolicyComplete,

    concreteFinalIntegration: concreteStatus.ConcreteChain.concreteFinalIntegration,
    finalIntegrationConcreteGlobalProofDAG: concreteStatus.ConcreteChain.finalIntegrationConcreteGlobalProofDAG,
    finalIntegrationGPackFieldCoverageComplete: concreteStatus.ConcreteChain.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: concreteStatus.ConcreteChain.finalIntegrationRowFamGCoverageComplete,
    finalIntegrationUsesGPack: concreteStatus.ConcreteChain.finalIntegrationUsesGPack,
    rowFamGUsesGPack: concreteStatus.ConcreteChain.rowFamGUsesGPack,
    finalTheoremUsesFinalIntegration: concreteStatus.ConcreteChain.finalTheoremUsesFinalIntegration,
    rowFamFinalUsesFinalTheorem: concreteStatus.ConcreteChain.rowFamFinalUsesFinalTheorem,
    finalMatchUsesGPack: concreteStatus.ConcreteChain.finalMatchUsesGPack,
    satDecisionUsesGPack: concreteStatus.ConcreteChain.satDecisionUsesGPack,

    concretePCCPack: concreteStatus.ConcreteChain.concretePCCPack,
    concretePCCPackCoverageDigest: concreteStatus.ConcreteChain.concretePCCPackCoverageDigest,
    pccPackPublicConclusionOnlyAfterAcceptRun: concreteStatus.ConcreteChain.pccPackPublicConclusionOnlyAfterAcceptRun,
    pccPackLinkedToKBundle: concreteStatus.ConcreteChain.pccPackLinkedToKBundle,
    pccPackLinkedToHardCheck: concreteStatus.ConcreteChain.pccPackLinkedToHardCheck,
    pccPackLinkedToRows: concreteStatus.ConcreteChain.pccPackLinkedToRows,
    pccPackLinkedToLocalPackages: concreteStatus.ConcreteChain.pccPackLinkedToLocalPackages,
    pccPackLinkedToGlobalFirewalls: concreteStatus.ConcreteChain.pccPackLinkedToGlobalFirewalls,
    pccPackLinkedToGlobalProofDAG: concreteStatus.ConcreteChain.pccPackLinkedToGlobalProofDAG,
    pccPackLinkedToGPack: concreteStatus.ConcreteChain.pccPackLinkedToGPack,
    pccPackLinkedToFinalIntegration: concreteStatus.ConcreteChain.pccPackLinkedToFinalIntegration,
    pccPackLinkedToFinalTheorem: concreteStatus.ConcreteChain.pccPackLinkedToFinalTheorem,
    checkPCCPackexpRecordPresent: concreteStatus.ConcreteChain.checkPCCPackexpRecordPresent,
    checkPCCPackexpRecordAccepted: concreteStatus.ConcreteChain.checkPCCPackexpRecordAccepted,
    checkPCCPackexpRecordChecker: concreteStatus.ConcreteChain.checkPCCPackexpRecordChecker,
    checkPCCPackexpRecordDigest: concreteStatus.ConcreteChain.checkPCCPackexpRecordDigest,
    checkPCCPackexpRecordDigestMatchesNF: concreteStatus.ConcreteChain.checkPCCPackexpRecordDigestMatchesNF,
    checkPCCPackexpRecordConcretePCCPack: concreteStatus.ConcreteChain.checkPCCPackexpRecordConcretePCCPack,
    checkPCCPackexpRecordPccPackDigest: concreteStatus.ConcreteChain.checkPCCPackexpRecordPccPackDigest,
    checkPCCPackexpRecordPccPackDigestMatchesConcreteRun: concreteStatus.ConcreteChain.checkPCCPackexpRecordPccPackDigestMatchesConcreteRun,
    checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun: concreteStatus.ConcreteChain.checkPCCPackexpRecordPublicConclusionOnlyAfterAcceptRun,
    checkPCCPackexpRecordPublicConclusionNotEmitted: concreteStatus.ConcreteChain.checkPCCPackexpRecordPublicConclusionNotEmitted,
    checkPCCPackexpRecordClaimBoundaryConditional: concreteStatus.ConcreteChain.checkPCCPackexpRecordClaimBoundaryConditional,
    generatedPCCPackexpEnvelopePresent: concreteStatus.ConcreteChain.generatedPCCPackexpEnvelopePresent,
    generatedPCCPackexpEnvelopeDigest: concreteStatus.ConcreteChain.generatedPCCPackexpEnvelopeDigest,
    generatedPCCPackexpGenCallGeneratePCCPack: concreteStatus.ConcreteChain.generatedPCCPackexpGenCallGeneratePCCPack,
    generatedPCCPackexpCoreOnly: concreteStatus.ConcreteChain.generatedPCCPackexpCoreOnly,
    generatedPCCPackexpExcludesAcceptRun: concreteStatus.ConcreteChain.generatedPCCPackexpExcludesAcceptRun,
    generatedPCCPackexpPackageMatchesConcreteRun: concreteStatus.ConcreteChain.generatedPCCPackexpPackageMatchesConcreteRun,
    generatedPCCPackexpCheckRecordMatchesConcreteRun: concreteStatus.ConcreteChain.generatedPCCPackexpCheckRecordMatchesConcreteRun,
    generatedPCCPackexpCheckRecordAccepted: concreteStatus.ConcreteChain.generatedPCCPackexpCheckRecordAccepted,
    generatedPCCPackexpCheckRecordChecker: concreteStatus.ConcreteChain.generatedPCCPackexpCheckRecordChecker,
    generatedPCCPackexpCheckRecordDigest: concreteStatus.ConcreteChain.generatedPCCPackexpCheckRecordDigest,
    generatedPCCPackexpCheckRecordDigestMatchesNF: concreteStatus.ConcreteChain.generatedPCCPackexpCheckRecordDigestMatchesNF,
    generatedPCCPackexpCheckRecordClaimBoundaryConditional: concreteStatus.ConcreteChain.generatedPCCPackexpCheckRecordClaimBoundaryConditional,
    generatedPCCPackexpLinkageGeneratedPackageDigestMatches: concreteStatus.ConcreteChain.generatedPCCPackexpLinkageGeneratedPackageDigestMatches,
    generatedPCCPackexpLinkageCheckRecordDigestMatches: concreteStatus.ConcreteChain.generatedPCCPackexpLinkageCheckRecordDigestMatches,
    checkGeneratedPCCPackexpRecordPresent: concreteStatus.ConcreteChain.checkGeneratedPCCPackexpRecordPresent,
    checkGeneratedPCCPackexpRecordAccepted: concreteStatus.ConcreteChain.checkGeneratedPCCPackexpRecordAccepted,
    checkGeneratedPCCPackexpRecordChecker: concreteStatus.ConcreteChain.checkGeneratedPCCPackexpRecordChecker,
    checkGeneratedPCCPackexpRecordDigest: concreteStatus.ConcreteChain.checkGeneratedPCCPackexpRecordDigest,
    checkGeneratedPCCPackexpRecordDigestMatchesNF: concreteStatus.ConcreteChain.checkGeneratedPCCPackexpRecordDigestMatchesNF,
    checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope:
      concreteStatus.ConcreteChain.checkGeneratedPCCPackexpRecordGeneratedPackageDigestMatchesEnvelope,
    checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope:
      concreteStatus.ConcreteChain.checkGeneratedPCCPackexpRecordCheckPCCPackexpDigestMatchesEnvelope,

    generatedPCCPackexpBoot0: concreteStatus.ConcreteChain.generatedPCCPackexpBoot0,
    generatedPCCPackexpBoot0Accepted: concreteStatus.ConcreteChain.generatedPCCPackexpBoot0Accepted,
    generatedPCCPackexpBoot0Kind: concreteStatus.ConcreteChain.generatedPCCPackexpBoot0Kind,
    generatedPCCPackexpBoot0Digest: concreteStatus.ConcreteChain.generatedPCCPackexpBoot0Digest,
    generatedPCCPackexpBoot0CheckDigest: concreteStatus.ConcreteChain.generatedPCCPackexpBoot0CheckDigest,
    generatedPCCPackexpBoot0CanonicalByteDigest:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0CanonicalByteDigest,
    generatedPCCPackexpBoot0RowCount: concreteStatus.ConcreteChain.generatedPCCPackexpBoot0RowCount,
    generatedPCCPackexpBoot0KernelRuleCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0KernelRuleCount,
    generatedPCCPackexpBoot0JsonMaterialized:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0JsonMaterialized,
    generatedPCCPackexpBoot0NoFixtureMarkers:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0NoFixtureMarkers,
    generatedPCCPackexpBoot0BootBatchDigest:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0BootBatchDigest,
    generatedPCCPackexpBoot0BootAuditDigest:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0BootAuditDigest,
    generatedPCCPackexpBoot0LinkedToPCCPack:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0LinkedToPCCPack,
    generatedPCCPackexpBoot0LinkedToCoreDigestMap:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0LinkedToCoreDigestMap,
    generatedPCCPackexpBoot0DigestMatchesGeneratedPackage:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0DigestMatchesGeneratedPackage,
    generatedPCCPackexpBoot0DigestMatchesCoreDigestMap:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0DigestMatchesCoreDigestMap,
    generatedPCCPackexpBoot0B0Accepted:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0Accepted,
    generatedPCCPackexpBoot0B0Digest:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0Digest,
    generatedPCCPackexpBoot0B0CoverageDigest:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoverageDigest,
    generatedPCCPackexpBoot0B0FamilyCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0FamilyCount,
    generatedPCCPackexpBoot0B0RequiredFamilyCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0RequiredFamilyCount,
    generatedPCCPackexpBoot0B0Families:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0Families,
    generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent,
    generatedPCCPackexpBoot0B0CoversIface:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversIface,
    generatedPCCPackexpBoot0B0CoversSched:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversSched,
    generatedPCCPackexpBoot0B0CoversNF:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversNF,
    generatedPCCPackexpBoot0B0CoversTruthEval:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversTruthEval,
    generatedPCCPackexpBoot0B0CoversRel:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversRel,
    generatedPCCPackexpBoot0B0CoversCharge:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversCharge,
    generatedPCCPackexpBoot0B0CoversObl:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversObl,
    generatedPCCPackexpBoot0B0CoversArith:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversArith,
    generatedPCCPackexpBoot0B0CoversMode:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversMode,
    generatedPCCPackexpBoot0B0CoversRoute:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversRoute,
    generatedPCCPackexpBoot0B0CoversHash:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversHash,
    generatedPCCPackexpBoot0B0CoversImport:
      concreteStatus.ConcreteChain.generatedPCCPackexpBoot0B0CoversImport,
    generatedPCCPackexpKernelSeed0:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0,
    generatedPCCPackexpKernelSeed0Accepted:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0Accepted,
    generatedPCCPackexpKernelSeed0Kind:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0Kind,
    generatedPCCPackexpKernelSeed0Digest:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0Digest,
    generatedPCCPackexpKernelSeed0RuleCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0RuleCount,
    generatedPCCPackexpKernelSeed0RequiredRuleCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0RequiredRuleCount,
    generatedPCCPackexpKernelSeed0Rules:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0Rules,
    generatedPCCPackexpKernelSeed0AllRequiredRulesPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0AllRequiredRulesPresent,
    generatedPCCPackexpKernelSeed0HasEq:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasEq,
    generatedPCCPackexpKernelSeed0HasSubst:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasSubst,
    generatedPCCPackexpKernelSeed0HasRecord:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasRecord,
    generatedPCCPackexpKernelSeed0HasDAGInd:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasDAGInd,
    generatedPCCPackexpKernelSeed0HasLedgerInd:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasLedgerInd,
    generatedPCCPackexpKernelSeed0HasOblTopoInd:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasOblTopoInd,
    generatedPCCPackexpKernelSeed0HasTraceInd:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasTraceInd,
    generatedPCCPackexpKernelSeed0HasFiniteExhaust:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasFiniteExhaust,
    generatedPCCPackexpKernelSeed0HasDPInd:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasDPInd,
    generatedPCCPackexpKernelSeed0HasHall:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasHall,
    generatedPCCPackexpKernelSeed0HasRankInd:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasRankInd,
    generatedPCCPackexpKernelSeed0HasMinCounterexample:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasMinCounterexample,
    generatedPCCPackexpKernelSeed0HasIntArith:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasIntArith,
    generatedPCCPackexpKernelSeed0HasTransport:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasTransport,
    generatedPCCPackexpKernelSeed0HasTruthVec:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasTruthVec,
    generatedPCCPackexpKernelSeed0HasFiniteRel:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0HasFiniteRel,
    generatedPCCPackexpKernelSeed0ProofNodeKindCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0ProofNodeKindCount,
    generatedPCCPackexpKernelSeed0ProofNodeKinds:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0ProofNodeKinds,
    generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent,
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque,
    generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic,
    generatedPCCPackexpKernelSeed0ProofRefsHashIndependent:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0ProofRefsHashIndependent,
    generatedPCCPackexpKernelSeed0PiBootDigestMatches:
      concreteStatus.ConcreteChain.generatedPCCPackexpKernelSeed0PiBootDigestMatches,
    generatedPCCPackexpCodec0:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0,
    generatedPCCPackexpCodec0Accepted:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0Accepted,
    generatedPCCPackexpCodec0Kind:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0Kind,
    generatedPCCPackexpCodec0Digest:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0Digest,
    generatedPCCPackexpCodec0Canonical:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0Canonical,
    generatedPCCPackexpCodec0NaturalEncoding:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0NaturalEncoding,
    generatedPCCPackexpCodec0NaturalEncodingCanonical:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0NaturalEncodingCanonical,
    generatedPCCPackexpCodec0IntegerEncoding:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0IntegerEncoding,
    generatedPCCPackexpCodec0IntegerEncodingCanonical:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0IntegerEncodingCanonical,
    generatedPCCPackexpCodec0StringEncoding:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0StringEncoding,
    generatedPCCPackexpCodec0StringEncodingCanonical:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0StringEncodingCanonical,
    generatedPCCPackexpCodec0TopLevelConsumesAllBytes:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0TopLevelConsumesAllBytes,
    generatedPCCPackexpCodec0NormalFormSerialization:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0NormalFormSerialization,
    generatedPCCPackexpCodec0NormalFormSerializationCanonical:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0NormalFormSerializationCanonical,
    generatedPCCPackexpCodec0PiBootDigestMatches:
      concreteStatus.ConcreteChain.generatedPCCPackexpCodec0PiBootDigestMatches,

    generatedPCCPackexpDigest0:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0,
    generatedPCCPackexpDigest0Accepted:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0Accepted,
    generatedPCCPackexpDigest0Kind:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0Kind,
    generatedPCCPackexpDigest0Digest:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0Digest,
    generatedPCCPackexpDigest0Alg:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0Alg,
    generatedPCCPackexpDigest0AlgSHA256:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0AlgSHA256,
    generatedPCCPackexpDigest0Bytes:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0Bytes,
    generatedPCCPackexpDigest0BytesCanonicalJson:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0BytesCanonicalJson,
    generatedPCCPackexpDigest0EqualityNotObjectEquality:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0EqualityNotObjectEquality,
    generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup,
    generatedPCCPackexpDigest0PiBootDigestMatches:
      concreteStatus.ConcreteChain.generatedPCCPackexpDigest0PiBootDigestMatches,
    generatedPCCPackexpIfaceDict0:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0,
    generatedPCCPackexpIfaceDict0Accepted:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0Accepted,
    generatedPCCPackexpIfaceDict0Kind:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0Kind,
    generatedPCCPackexpIfaceDict0Digest:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0Digest,
    generatedPCCPackexpIfaceDict0ForbiddenSymbolCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0ForbiddenSymbolCount,
    generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent,
    generatedPCCPackexpIfaceDict0NoExecutableMinSymbols:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0NoExecutableMinSymbols,
    generatedPCCPackexpIfaceDict0PublicConstructorsPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0PublicConstructorsPresent,
    generatedPCCPackexpIfaceDict0CriticalKindsPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0CriticalKindsPresent,
    generatedPCCPackexpIfaceDict0RouteTokensPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0RouteTokensPresent,
    generatedPCCPackexpIfaceDict0PiBootDigestMatches:
      concreteStatus.ConcreteChain.generatedPCCPackexpIfaceDict0PiBootDigestMatches,

    generatedPCCPackexpSched0:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0,
    generatedPCCPackexpSched0Accepted:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0Accepted,
    generatedPCCPackexpSched0Kind:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0Kind,
    generatedPCCPackexpSched0Digest:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0Digest,
    generatedPCCPackexpSched0CoreMatchesExpected:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0CoreMatchesExpected,
    generatedPCCPackexpSched0CoreB0:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0CoreB0,
    generatedPCCPackexpSched0CoreK0:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0CoreK0,
    generatedPCCPackexpSched0CoreR0:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0CoreR0,
    generatedPCCPackexpSched0CoreH0:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0CoreH0,
    generatedPCCPackexpSched0CoreO0:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0CoreO0,
    generatedPCCPackexpSched0CoreRel0:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0CoreRel0,
    generatedPCCPackexpSched0ScaleFactorsPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0ScaleFactorsPresent,
    generatedPCCPackexpSched0SelectorBoundsPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0SelectorBoundsPresent,
    generatedPCCPackexpSched0SelectorBoundBH:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0SelectorBoundBH,
    generatedPCCPackexpSched0SelectorBoundBTheta:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0SelectorBoundBTheta,
    generatedPCCPackexpSched0PolynomialExponent:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0PolynomialExponent,
    generatedPCCPackexpSched0PiBootDigestMatches:
      concreteStatus.ConcreteChain.generatedPCCPackexpSched0PiBootDigestMatches,
    generatedPCCPackexpByteLang0:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0,
    generatedPCCPackexpByteLang0Accepted:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0Accepted,
    generatedPCCPackexpByteLang0Kind:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0Kind,
    generatedPCCPackexpByteLang0Digest:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0Digest,
    generatedPCCPackexpByteLang0TagCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0TagCount,
    generatedPCCPackexpByteLang0TagsUnique:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0TagsUnique,
    generatedPCCPackexpByteLang0RequiredTagsPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0RequiredTagsPresent,
    generatedPCCPackexpByteLang0SortCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0SortCount,
    generatedPCCPackexpByteLang0RequiredSortsPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0RequiredSortsPresent,
    generatedPCCPackexpByteLang0ConstructorCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0ConstructorCount,
    generatedPCCPackexpByteLang0RequiredConstructorsPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0RequiredConstructorsPresent,
    generatedPCCPackexpByteLang0RecordCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0RecordCount,
    generatedPCCPackexpByteLang0RequiredRecordAritiesPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0RequiredRecordAritiesPresent,
    generatedPCCPackexpByteLang0PiBootDigestMatches:
      concreteStatus.ConcreteChain.generatedPCCPackexpByteLang0PiBootDigestMatches,
    generatedPCCPackexpBootAudit0:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0,
    generatedPCCPackexpBootAudit0Accepted:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0Accepted,
    generatedPCCPackexpBootAudit0Checker:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0Checker,
    generatedPCCPackexpBootAudit0Digest:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0Digest,
    generatedPCCPackexpBootAudit0DigestMatchesNF:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0DigestMatchesNF,
    generatedPCCPackexpBootAudit0NFKind:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0NFKind,
    generatedPCCPackexpBootAudit0SuiteId:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0SuiteId,
    generatedPCCPackexpBootAudit0CaseCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0CaseCount,
    generatedPCCPackexpBootAudit0PositiveCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0PositiveCount,
    generatedPCCPackexpBootAudit0NegativeCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0NegativeCount,
    generatedPCCPackexpBootAudit0CoversB0Accept:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0CoversB0Accept,
    generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject,
    generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject:
      concreteStatus.ConcreteChain.generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject,

    generatedPCCPackexpPiBoot0:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0,
    generatedPCCPackexpPiBoot0Accepted:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0Accepted,
    generatedPCCPackexpPiBoot0Kind:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0Kind,
    generatedPCCPackexpPiBoot0Digest:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0Digest,
    generatedPCCPackexpPiBoot0Materialized:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0Materialized,
    generatedPCCPackexpPiBoot0ExternalJson:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0ExternalJson,
    generatedPCCPackexpPiBoot0RefCount:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0RefCount,
    generatedPCCPackexpPiBoot0AllBootRefsPresent:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0AllBootRefsPresent,
    generatedPCCPackexpPiBoot0RefsMatchBootObjects:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0RefsMatchBootObjects,
    generatedPCCPackexpPiBoot0RefsIncludeByteLang0:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0RefsIncludeByteLang0,
    generatedPCCPackexpPiBoot0RefsIncludeCodec0:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0RefsIncludeCodec0,
    generatedPCCPackexpPiBoot0RefsIncludeDigest0:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0RefsIncludeDigest0,
    generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0,
    generatedPCCPackexpPiBoot0RefsIncludeSched0:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0RefsIncludeSched0,
    generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0,
    generatedPCCPackexpPiBoot0RefsIncludeB0:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0RefsIncludeB0,
    generatedPCCPackexpPiBoot0RefsIncludeBootAudit0:
      concreteStatus.ConcreteChain.generatedPCCPackexpPiBoot0RefsIncludeBootAudit0,

    finalCertificateUsesConcreteAcceptRun: concreteStatus.ConcreteChain.finalCertificateUsesConcreteAcceptRun,
    statusUsesConcreteFinalCertificate: concreteStatus.ConcreteChain.statusUsesConcreteFinalCertificate,

    status: publicStatus.status,
    verdict: publicStatus.verdict,
    publicConclusionEmitted: publicStatus.publicConclusionEmitted,
    publicConclusion: publicStatus.publicConclusion,
    claimBoundary: publicStatus.claimBoundary,

    certificateDigest: publicStatus.certificateDigest,
    finalVerdictDigest: publicStatus.finalVerdictDigest,
    acceptRunDigest: publicStatus.acceptRunDigest,
    pccPackDigest: publicStatus.pccPackDigest,
    canonicalByteRoots: publicStatus.canonicalByteRoots,
    acceptanceTranscript: publicStatus.acceptanceTranscript,

    concretePublicStatusEnvelopeDigest: digestCanonical0(concreteStatus),
    publicStatusDigest: digestCanonical0(publicStatus),
    concreteFinalCertificateDigest: digestCanonical0(concreteStatus.ConcreteFinalCertificateEnvelope),
    concreteChainDigest: digestCanonical0(concreteNF),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),

    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
    allowSyntheticScaffoldMarker: cfg.allowSyntheticScaffoldMarker,
  };

  ledger.push({
    phase: 'EmitConcreteReleaseAuditFinalCertificateGate0',
    status: 'pass',
    digest: digestCanonical0(nf),
  });

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeReleaseAuditConcreteFinalCertificateGateFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeReleaseAuditConcreteFinalCertificateGateFiles0 requires a non-empty output directory');
  }

  const envelope = await makeReleaseAuditConcreteFinalCertificateGate0(options);
  const checked = await CheckReleaseAuditConcreteFinalCertificateGate0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ReleaseAuditConcreteFinalCertificateGate0.json');
  const releaseAuditPath = path.join(outDir, 'ReleaseAudit0.json');
  const concretePublicStatusPath = path.join(outDir, 'ConcreteFinalCertificatePublicStatus0.json');
  const publicStatusPath = path.join(outDir, 'FinalCertificatePublicStatusEmission0.json');
  const concreteFinalCertificatePath = path.join(outDir, 'ConcreteMaterializedFinalCertificate0.json');
  const checkPath = path.join(outDir, 'ReleaseAuditConcreteFinalCertificateGate0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(releaseAuditPath, envelope.ReleaseAuditRecord);
  await writeJsonFile0(concretePublicStatusPath, envelope.ConcreteFinalCertificatePublicStatusEnvelope);
  await writeJsonFile0(publicStatusPath, envelope.ConcreteFinalCertificatePublicStatusEnvelope.FinalCertificatePublicStatusEnvelope.PublicStatus);
  await writeJsonFile0(concreteFinalCertificatePath, envelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      releaseAuditPath,
      concretePublicStatusPath,
      publicStatusPath,
      concreteFinalCertificatePath,
      checkPath,
    },
  };
}

async function runReleaseAudit0(releaseAuditRunner, releaseAuditConfig) {
  const runner = typeof releaseAuditRunner === 'function'
    ? releaseAuditRunner
    : CheckReleaseAudit0;

  return runner(makeReleaseAuditConfig0(releaseAuditConfig ?? {}));
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ReleaseAuditConcreteFinalCertificateGateConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ReleaseAuditConcreteFinalCertificateGateConfig0') {
    return validationReject0(['kind'], 'ReleaseAuditConcreteFinalCertificateGateConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ReleaseAuditConcreteFinalCertificateGateConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkReleaseAuditRecord',
    'checkConcretePublicStatus',
    'checkPublicConclusionAlignment',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ReleaseAuditConcreteFinalCertificateGateConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.concretePublicStatusConfig)) {
    return validationReject0(['concretePublicStatusConfig'], 'concretePublicStatusConfig must be an object', {
      actual: typeof config.concretePublicStatusConfig,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditConcreteFinalCertificateGateConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ReleaseAuditConcreteFinalCertificateGate0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ReleaseAuditConcreteFinalCertificateGate0') {
    return validationReject0(['kind'], 'ReleaseAuditConcreteFinalCertificateGate0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ReleaseAuditConcreteFinalCertificateGate0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.ReleaseAuditRecord)) {
    return validationReject0(['ReleaseAuditRecord'], 'ReleaseAuditConcreteFinalCertificateGate0 must include an accepted ReleaseAuditRecord', {
      actual: typeof envelope.ReleaseAuditRecord,
    });
  }

  if (!isPlainObject(envelope.ConcreteFinalCertificatePublicStatusEnvelope)) {
    return validationReject0(['ConcreteFinalCertificatePublicStatusEnvelope'], 'ReleaseAuditConcreteFinalCertificateGate0 must include ConcreteFinalCertificatePublicStatusEnvelope', {
      actual: typeof envelope.ConcreteFinalCertificatePublicStatusEnvelope,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditConcreteFinalCertificateGateShape0NF',
  });
}

function validateReleaseAuditRecord0(record) {
  if (!isPlainObject(record)) {
    return validationReject0(['ReleaseAuditRecord'], 'ReleaseAuditRecord must be an object', {
      actual: typeof record,
    });
  }

  if (record.tag !== 'accept') {
    return validationReject0(['ReleaseAuditRecord', 'tag'], 'ReleaseAuditRecord must be accepted', {
      actual: record.tag,
    });
  }

  if (record.checker !== 'CheckReleaseAudit0') {
    return validationReject0(['ReleaseAuditRecord', 'checker'], 'ReleaseAuditRecord checker mismatch', {
      actual: record.checker,
    });
  }

  const nf = record.NF ?? record.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(['ReleaseAuditRecord', 'NF'], 'ReleaseAuditRecord must expose NF', {
      actual: typeof nf,
    });
  }

  if (nf.kind !== 'ReleaseAudit0NF') {
    return validationReject0(['ReleaseAuditRecord', 'NF', 'kind'], 'ReleaseAuditRecord NF kind mismatch', {
      actual: nf.kind,
    });
  }

  const expectedDigest = digestCanonical0(nf);

  if (!sameDigestHex0(record.Digest ?? record.digest, expectedDigest)) {
    return validationReject0(['ReleaseAuditRecord', 'Digest'], 'ReleaseAuditRecord Digest must match its NF', {
      expected: expectedDigest,
      actual: record.Digest ?? record.digest,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditRecord0NF',
    releaseAuditDigest: record.Digest ?? record.digest,
  });
}

function validateConcretePublicConclusionAlignment0(envelope) {
  const releaseAuditNF = envelope.ReleaseAuditRecord.NF ?? envelope.ReleaseAuditRecord.nf ?? {};
  const concreteStatus = envelope.ConcreteFinalCertificatePublicStatusEnvelope;
  const chain = concreteStatus.ConcreteChain;
  const publicStatus = concreteStatus.FinalCertificatePublicStatusEnvelope.PublicStatus;
  const releaseAuditDigest = envelope.ReleaseAuditRecord.Digest ?? envelope.ReleaseAuditRecord.digest;

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
    if (chain[field] !== true) {
      return validationReject0(['ConcreteFinalCertificatePublicStatusEnvelope', 'ConcreteChain', field], `concrete public-status chain must certify ${field}`, {
        actual: chain[field],
      });
    }
  }

  if (publicStatus.status !== 'accepted' || publicStatus.verdict !== 'accept') {
    return validationReject0(['ConcreteFinalCertificatePublicStatusEnvelope', 'PublicStatus', 'status'], 'concrete public status must be accepted', {
      status: publicStatus.status,
      verdict: publicStatus.verdict,
    });
  }

  if (!samePublicConclusion0(publicStatus.publicConclusion, {
    antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
    consequent: 'P = NP',
    conditional: true,
  })) {
    return validationReject0(['ConcreteFinalCertificatePublicStatusEnvelope', 'PublicStatus', 'publicConclusion'], 'concrete public conclusion mismatch', {
      actual: publicStatus.publicConclusion,
    });
  }

  if (isPlainObject(releaseAuditNF.publicConclusion) && !samePublicConclusion0(publicStatus.publicConclusion, releaseAuditNF.publicConclusion)) {
    return validationReject0(['ReleaseAuditRecord', 'NF', 'publicConclusion'], 'release audit public conclusion must match concrete public status conclusion', {
      expected: publicStatus.publicConclusion,
      actual: releaseAuditNF.publicConclusion,
    });
  }

  if (publicStatus.releaseAuditAttached !== true) {
    return validationReject0(['ConcreteFinalCertificatePublicStatusEnvelope', 'PublicStatus', 'releaseAuditAttached'], 'concrete public status must attach release audit', {
      actual: publicStatus.releaseAuditAttached,
    });
  }

  if (!sameDigestHex0(publicStatus.releaseAuditDigest, releaseAuditDigest)) {
    return validationReject0(['ConcreteFinalCertificatePublicStatusEnvelope', 'PublicStatus', 'releaseAuditDigest'], 'concrete public status release audit digest mismatch', {
      expected: releaseAuditDigest,
      actual: publicStatus.releaseAuditDigest,
    });
  }

  return validationAccept0({
    kind: 'ConcreteReleaseAuditPublicConclusion0NF',
    publicConclusion: publicStatus.publicConclusion,
    releaseAuditDigest,
    pccPackDigest: publicStatus.pccPackDigest,
    finalVerdictDigest: publicStatus.finalVerdictDigest,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['ReleaseAuditConcreteFinalCertificateGate0'], 'ReleaseAuditConcreteFinalCertificateGate0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ReleaseAuditConcreteFinalCertificateGate0'], 'ReleaseAuditConcreteFinalCertificateGate0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditConcreteFinalCertificateGateJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ReleaseAuditConcreteFinalCertificateGateFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === CONCRETE_RELEASE_GATE_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== CONCRETE_RELEASE_GATE_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== CONCRETE_RELEASE_GATE_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'release-audit concrete final-certificate gate contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ReleaseAuditConcreteFinalCertificateGateNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function validateLinkage0(envelope) {
  const concreteStatus = envelope.ConcreteFinalCertificatePublicStatusEnvelope;

  const expected = {
    releaseAuditDigest: envelope.ReleaseAuditRecord.Digest ?? envelope.ReleaseAuditRecord.digest,
    concretePublicStatusEnvelopeDigest: digestCanonical0(concreteStatus),
    publicStatusDigest: digestCanonical0(concreteStatus.FinalCertificatePublicStatusEnvelope.PublicStatus),
    concreteFinalCertificateDigest: digestCanonical0(concreteStatus.ConcreteFinalCertificateEnvelope),
    certificateDigest: digestCanonical0(concreteStatus.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(concreteStatus.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest:
      concreteStatus.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict.Digest ??
      concreteStatus.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict.digest,
    acceptRunDigest: digestCanonical0(
      concreteStatus.ConcreteFinalCertificateEnvelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun,
    ),
    pccPackDigest: digestCanonical0(
      concreteStatus.ConcreteFinalCertificateEnvelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen,
    ),
    concreteChainDigest: digestCanonical0(concreteStatus.ConcreteChain),
  };

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ReleaseAuditConcreteFinalCertificateGateLinkage0NF',
      present: false,
      ...expected,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ReleaseAuditConcreteFinalCertificateGate0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  if (envelope.Linkage.releaseAuditAttached !== true) {
    return validationReject0(['Linkage', 'releaseAuditAttached'], 'Linkage must record releaseAuditAttached=true', {
      actual: envelope.Linkage.releaseAuditAttached,
    });
  }

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ReleaseAuditConcreteFinalCertificateGateLinkage0NF',
    present: true,
    ...expected,
  });
}

function scanFixtureMarkers0(value, path, hits) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of [
      CONCRETE_RELEASE_GATE_SYNTHETIC_MARKER0,
      ...CONCRETE_RELEASE_GATE_FORBIDDEN_MARKERS0,
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

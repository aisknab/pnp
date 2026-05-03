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

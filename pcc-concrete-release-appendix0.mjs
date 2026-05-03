import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckReleaseAuditConcreteFinalCertificateGate0,
  makeReleaseAuditConcreteFinalCertificateGate0,
} from './pcc-release-audit-final-certificate-concrete-gate0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_RELEASE_APPENDIX_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const CONCRETE_RELEASE_APPENDIX_SYNTHETIC_MARKER0 = 'synthetic';

export function makeConcreteReleaseAppendixConfig0(overrides = {}) {
  return {
    kind: 'ConcreteReleaseAppendixConfig0',
    version: CHECKER_VERSION,
    checkConcreteReleaseGate: true,
    checkAppendix: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    concreteReleaseGateConfig: {},
    ...overrides,
  };
}

export async function makeConcreteReleaseAppendix0({
  ReleaseAuditConcreteFinalCertificateGateEnvelope = null,
  Appendix = null,
  overrides = {},
} = {}) {
  const gateEnvelope = ReleaseAuditConcreteFinalCertificateGateEnvelope ??
    await makeReleaseAuditConcreteFinalCertificateGate0();

  const appendix = Appendix ?? makeConcreteReleaseAppendixRecord0(gateEnvelope);

  const linkage = {
    kind: 'ConcreteReleaseAppendixLinkage0',
    version: CHECKER_VERSION,
    concreteReleaseGateEnvelopeDigest: digestCanonical0(gateEnvelope),
    releaseAuditDigest: gateEnvelope.ReleaseAuditRecord.Digest ?? gateEnvelope.ReleaseAuditRecord.digest ?? null,
    concretePublicStatusEnvelopeDigest: digestCanonical0(gateEnvelope.ConcreteFinalCertificatePublicStatusEnvelope),
    publicStatusDigest: digestCanonical0(gateEnvelope.ConcreteFinalCertificatePublicStatusEnvelope.FinalCertificatePublicStatusEnvelope.PublicStatus),
    concreteFinalCertificateDigest: digestCanonical0(gateEnvelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope),
    certificateDigest: digestCanonical0(gateEnvelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(gateEnvelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest:
      gateEnvelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict.Digest ??
      gateEnvelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict.digest ??
      null,
    acceptRunDigest: digestCanonical0(
      gateEnvelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun,
    ),
    pccPackDigest: digestCanonical0(
      gateEnvelope.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen,
    ),
    appendixDigest: digestCanonical0(appendix),
  };

  return {
    kind: 'ConcreteReleaseAppendix0',
    version: CHECKER_VERSION,
    ReleaseAuditConcreteFinalCertificateGateEnvelope: gateEnvelope,
    Appendix: appendix,
    Linkage: linkage,
    PiConcreteReleaseAppendix: {
      kind: 'PiConcreteReleaseAppendix0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'ReleaseAuditConcreteFinalCertificateGateEnvelope',
          digest: linkage.concreteReleaseGateEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteReleaseAppendix',
          digest: linkage.appendixDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function makeConcreteReleaseAppendixRecord0(gateEnvelope) {
  const releaseAuditRecord = gateEnvelope.ReleaseAuditRecord;
  const concreteStatusEnvelope = gateEnvelope.ConcreteFinalCertificatePublicStatusEnvelope;
  const publicStatus = concreteStatusEnvelope.FinalCertificatePublicStatusEnvelope.PublicStatus;
  const concreteFinalCertificate = concreteStatusEnvelope.ConcreteFinalCertificateEnvelope;
  const certificate = concreteFinalCertificate.FinalCertificateEnvelope.Certificate;
  const finalVerdict = concreteFinalCertificate.FinalCertificateEnvelope.FinalVerdict;
  const acceptRun = concreteFinalCertificate.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun;
  const concreteChain = concreteStatusEnvelope.ConcreteChain;
  const hardCoverage = summarizeHardCoverageFromReleaseGate0(gateEnvelope);
  const packageCoverage = summarizeConcretePackageCoverageFromReleaseGate0(gateEnvelope);

  return {
    kind: 'ConcreteReleaseAppendixRecord0',
    version: CHECKER_VERSION,

    status: 'accepted',
    verdict: 'accept',
    claimBoundary: 'conditional-on-accepted-concrete-release-gate',
    noClaimBeforeAccept: true,

    checker: 'CheckPCCPackexp',
    generator: 'GeneratePCCPack',
    runId: acceptRun.RunID,

    releaseAuditAttached: true,
    releaseAuditDigest: releaseAuditRecord.Digest ?? releaseAuditRecord.digest,
    releaseAuditChecker: releaseAuditRecord.checker,

    concreteRows: concreteChain.concreteRows,
    concreteLocalPackages: concreteChain.concreteLocalPackages,
    concreteGlobalFirewalls: concreteChain.concreteGlobalFirewalls,
    concreteGlobalProofDAG: concreteChain.concreteGlobalProofDAG,
    concreteKBundle: packageCoverage.concreteKBundle,
    kBundleEnvelopeKind: packageCoverage.kBundleEnvelopeKind,
    kBundleKernelRuleCoverageComplete: packageCoverage.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: packageCoverage.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: packageCoverage.kBundleReflectionProofRefsResolve,
    kBundleCoverageDigest: packageCoverage.kBundleCoverageDigest,

    concreteFinalIntegration: packageCoverage.concreteFinalIntegration,
    finalIntegrationEnvelopeKind: packageCoverage.finalIntegrationEnvelopeKind,
    finalIntegrationConcreteGlobalProofDAG: packageCoverage.finalIntegrationConcreteGlobalProofDAG,
    finalIntegrationGPackFieldCoverageComplete: packageCoverage.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: packageCoverage.finalIntegrationRowFamGCoverageComplete,
    finalIntegrationUsesGPack: packageCoverage.finalIntegrationUsesGPack,
    rowFamGUsesGPack: packageCoverage.rowFamGUsesGPack,
    finalTheoremUsesFinalIntegration: packageCoverage.finalTheoremUsesFinalIntegration,
    rowFamFinalUsesFinalTheorem: packageCoverage.rowFamFinalUsesFinalTheorem,
    finalMatchUsesGPack: packageCoverage.finalMatchUsesGPack,
    satDecisionUsesGPack: packageCoverage.satDecisionUsesGPack,
    finalIntegrationLinksDigest: packageCoverage.finalIntegrationLinksDigest,


    hardEnvelopeKind: hardCoverage.hardEnvelopeKind,
    concreteHardCheck: hardCoverage.concreteHardCheck,
    hardCheckerCoverageComplete: hardCoverage.hardCheckerCoverageComplete,
    hardRowKeyCoverageComplete: hardCoverage.hardRowKeyCoverageComplete,
    hardRoutePriorityComplete: hardCoverage.hardRoutePriorityComplete,
    hardProofRefPolicyComplete: hardCoverage.hardProofRefPolicyComplete,
    hardHashDisciplineComplete: hardCoverage.hardHashDisciplineComplete,
    hardNoMinCoverageComplete: hardCoverage.hardNoMinCoverageComplete,
    hardImportPolicyComplete: hardCoverage.hardImportPolicyComplete,
    hardReflectionPolicyComplete: hardCoverage.hardReflectionPolicyComplete,
    hardBoundsPolicyComplete: hardCoverage.hardBoundsPolicyComplete,
    hardDiagnosticsPolicyComplete: hardCoverage.hardDiagnosticsPolicyComplete,
    hardCoverageDigest: hardCoverage.hardCoverageDigest,
    hardCheckDigest: hardCoverage.hardCheckDigest,

    finalCertificateUsesConcreteAcceptRun: concreteChain.finalCertificateUsesConcreteAcceptRun,
    statusUsesConcreteFinalCertificate: concreteChain.statusUsesConcreteFinalCertificate,

    publicConclusionEmitted: publicStatus.publicConclusionEmitted,
    publicConclusion: publicStatus.publicConclusion,

    pccPackDigest: publicStatus.pccPackDigest,
    acceptRunDigest: publicStatus.acceptRunDigest,
    finalVerdictDigest: publicStatus.finalVerdictDigest,
    certificateDigest: publicStatus.certificateDigest,
    concretePublicStatusEnvelopeDigest: digestCanonical0(concreteStatusEnvelope),
    concreteFinalCertificateDigest: digestCanonical0(concreteFinalCertificate),
    finalVerdictObjectDigest: digestCanonical0(finalVerdict),

    canonicalByteRoots: publicStatus.canonicalByteRoots,
    acceptanceTranscript: publicStatus.acceptanceTranscript,

    concreteChainDigest: digestCanonical0(concreteChain),
  };
}

export async function CheckConcreteReleaseAppendix0(
  input,
  config = makeConcreteReleaseAppendixConfig0(),
) {
  const checker = 'CheckConcreteReleaseAppendix0';
  const ledger = [];
  const cfg = makeConcreteReleaseAppendixConfig0(config);
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

  if (cfg.checkConcreteReleaseGate === true) {
    const gateRecord = await CheckReleaseAuditConcreteFinalCertificateGate0(
      envelope.ReleaseAuditConcreteFinalCertificateGateEnvelope,
      cfg.concreteReleaseGateConfig ?? {},
    );
    const gate = recordToValidation0(gateRecord, ['ReleaseAuditConcreteFinalCertificateGateEnvelope']);

    ledger.push({
      phase: 'CheckReleaseAuditConcreteFinalCertificateGate0',
      status: gate.ok ? 'pass' : 'fail',
      digest: gateRecord.Digest ?? gateRecord.digest ?? digestCanonical0(gateRecord),
    });

    if (!gate.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcreteReleaseGate`,
        path: gate.path,
        witness: gate.witness,
        ledger,
      });
    }
  }

  if (cfg.checkAppendix === true) {
    const expectedAppendix = makeConcreteReleaseAppendixRecord0(
      envelope.ReleaseAuditConcreteFinalCertificateGateEnvelope,
    );
    const appendix = validateAppendixRecord0(envelope.Appendix, expectedAppendix);

    ledger.push({
      phase: 'appendix',
      status: appendix.ok ? 'pass' : 'fail',
      digest: digestCanonical0(appendix.nf ?? appendix.witness ?? null),
    });

    if (!appendix.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.appendix`,
        path: appendix.path,
        witness: appendix.witness,
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

  const markerInventory = collectFixtureMarkers0(envelope, ['ConcreteReleaseAppendix0']);

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

  const appendix = envelope.Appendix;

  const nf = {
    kind: 'ConcreteReleaseAppendix0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,

    status: appendix.status,
    verdict: appendix.verdict,
    claimBoundary: appendix.claimBoundary,
    releaseAuditAttached: appendix.releaseAuditAttached,
    releaseAuditDigest: appendix.releaseAuditDigest,

    concreteRows: appendix.concreteRows,
    concreteLocalPackages: appendix.concreteLocalPackages,
    concreteGlobalFirewalls: appendix.concreteGlobalFirewalls,
    concreteGlobalProofDAG: appendix.concreteGlobalProofDAG,
    concreteKBundle: appendix.concreteKBundle,
    kBundleEnvelopeKind: appendix.kBundleEnvelopeKind,
    kBundleKernelRuleCoverageComplete: appendix.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: appendix.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: appendix.kBundleReflectionProofRefsResolve,
    kBundleCoverageDigest: appendix.kBundleCoverageDigest,

    concreteFinalIntegration: appendix.concreteFinalIntegration,
    finalIntegrationEnvelopeKind: appendix.finalIntegrationEnvelopeKind,
    finalIntegrationConcreteGlobalProofDAG: appendix.finalIntegrationConcreteGlobalProofDAG,
    finalIntegrationGPackFieldCoverageComplete: appendix.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: appendix.finalIntegrationRowFamGCoverageComplete,
    finalIntegrationUsesGPack: appendix.finalIntegrationUsesGPack,
    rowFamGUsesGPack: appendix.rowFamGUsesGPack,
    finalTheoremUsesFinalIntegration: appendix.finalTheoremUsesFinalIntegration,
    rowFamFinalUsesFinalTheorem: appendix.rowFamFinalUsesFinalTheorem,
    finalMatchUsesGPack: appendix.finalMatchUsesGPack,
    satDecisionUsesGPack: appendix.satDecisionUsesGPack,
    finalIntegrationLinksDigest: appendix.finalIntegrationLinksDigest,


    hardEnvelopeKind: appendix.hardEnvelopeKind,
    concreteHardCheck: appendix.concreteHardCheck,
    hardCheckerCoverageComplete: appendix.hardCheckerCoverageComplete,
    hardRowKeyCoverageComplete: appendix.hardRowKeyCoverageComplete,
    hardRoutePriorityComplete: appendix.hardRoutePriorityComplete,
    hardProofRefPolicyComplete: appendix.hardProofRefPolicyComplete,
    hardHashDisciplineComplete: appendix.hardHashDisciplineComplete,
    hardNoMinCoverageComplete: appendix.hardNoMinCoverageComplete,
    hardImportPolicyComplete: appendix.hardImportPolicyComplete,
    hardReflectionPolicyComplete: appendix.hardReflectionPolicyComplete,
    hardBoundsPolicyComplete: appendix.hardBoundsPolicyComplete,
    hardDiagnosticsPolicyComplete: appendix.hardDiagnosticsPolicyComplete,
    hardCoverageDigest: appendix.hardCoverageDigest,
    hardCheckDigest: appendix.hardCheckDigest,

    finalCertificateUsesConcreteAcceptRun: appendix.finalCertificateUsesConcreteAcceptRun,
    statusUsesConcreteFinalCertificate: appendix.statusUsesConcreteFinalCertificate,

    publicConclusionEmitted: appendix.publicConclusionEmitted,
    publicConclusion: appendix.publicConclusion,

    pccPackDigest: appendix.pccPackDigest,
    acceptRunDigest: appendix.acceptRunDigest,
    finalVerdictDigest: appendix.finalVerdictDigest,
    certificateDigest: appendix.certificateDigest,
    canonicalByteRoots: appendix.canonicalByteRoots,
    acceptanceTranscript: appendix.acceptanceTranscript,

    concreteReleaseGateEnvelopeDigest: digestCanonical0(envelope.ReleaseAuditConcreteFinalCertificateGateEnvelope),
    appendixDigest: digestCanonical0(appendix),
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

export async function writeConcreteReleaseAppendixFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteReleaseAppendixFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteReleaseAppendix0(options);
  const checked = await CheckConcreteReleaseAppendix0(envelope, options.checkConfig ?? {});
  const gateCheck = await CheckReleaseAuditConcreteFinalCertificateGate0(
    envelope.ReleaseAuditConcreteFinalCertificateGateEnvelope,
    options.gateCheckConfig ?? {},
  );

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteReleaseAppendix0.json');
  const appendixPath = path.join(outDir, 'ConcreteReleaseAppendixRecord0.json');
  const gatePath = path.join(outDir, 'ReleaseAuditConcreteFinalCertificateGate0.json');
  const publicStatusPath = path.join(outDir, 'FinalCertificatePublicStatusEmission0.json');
  const certificatePath = path.join(outDir, 'FinalCertificate0.json');
  const releaseAuditPath = path.join(outDir, 'ReleaseAudit0.json');
  const gateCheckPath = path.join(outDir, 'ReleaseAuditConcreteFinalCertificateGate0.check.json');
  const checkPath = path.join(outDir, 'ConcreteReleaseAppendix0.check.json');

  const gate = envelope.ReleaseAuditConcreteFinalCertificateGateEnvelope;

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(appendixPath, envelope.Appendix);
  await writeJsonFile0(gatePath, gate);
  await writeJsonFile0(publicStatusPath, gate.ConcreteFinalCertificatePublicStatusEnvelope.FinalCertificatePublicStatusEnvelope.PublicStatus);
  await writeJsonFile0(certificatePath, gate.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.Certificate);
  await writeJsonFile0(releaseAuditPath, gate.ReleaseAuditRecord);
  await writeJsonFile0(gateCheckPath, gateCheck);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    gateCheck,
    files: {
      envelopePath,
      appendixPath,
      gatePath,
      publicStatusPath,
      certificatePath,
      releaseAuditPath,
      gateCheckPath,
      checkPath,
    },
  };
}



function summarizeConcretePackageCoverageFromReleaseGate0(gateEnvelope) {
  const generatedAcceptRunEnvelope =
    gateEnvelope?.ConcreteFinalCertificatePublicStatusEnvelope
      ?.ConcreteFinalCertificateEnvelope
      ?.ConcreteGeneratedAcceptRunEnvelope
      ?.GeneratedAcceptRunEnvelope ?? null;

  const materializedPCCPack = generatedAcceptRunEnvelope?.MaterializedPCCPack ?? null;
  const kBundleEnvelope = materializedPCCPack?.KBundleEnvelope ?? null;
  const kBundleCoverage = kBundleEnvelope?.ProofInventory ?? null;
  const finalIntegrationEnvelope = materializedPCCPack?.FinalIntegrationEnvelope ?? null;
  const finalIntegrationLinks = finalIntegrationEnvelope?.ConcreteLinks ?? null;

  return {
    kind: 'ConcreteReleaseAppendixPackageCoverage0',
    version: CHECKER_VERSION,

    kBundleEnvelopeKind: kBundleEnvelope?.kind ?? null,
    concreteKBundle: kBundleEnvelope?.kind === 'ConcreteMaterializedKBundle0',
    kBundleKernelRuleCoverageComplete: kBundleCoverage?.kernelRuleCoverageComplete === true,
    kBundleSigmaProofRefsResolve: kBundleCoverage?.sigmaProofRefsResolve === true,
    kBundleReflectionProofRefsResolve: kBundleCoverage?.reflectionProofRefsResolve === true,
    kBundleCoverageDigest: isPlainObject(kBundleCoverage) ? digestCanonical0(kBundleCoverage) : null,

    finalIntegrationEnvelopeKind: finalIntegrationEnvelope?.kind ?? null,
    concreteFinalIntegration: finalIntegrationEnvelope?.kind === 'ConcreteMaterializedFinalIntegration0',
    finalIntegrationConcreteGlobalProofDAG: finalIntegrationLinks?.concreteGlobalProofDAG === true,
    finalIntegrationGPackFieldCoverageComplete: finalIntegrationLinks?.gpackFieldCoverageComplete === true,
    finalIntegrationRowFamGCoverageComplete: finalIntegrationLinks?.rowFamGCoverageComplete === true,
    finalIntegrationUsesGPack: finalIntegrationLinks?.finalIntegrationUsesGPack === true,
    rowFamGUsesGPack: finalIntegrationLinks?.rowFamGUsesGPack === true,
    finalTheoremUsesFinalIntegration: finalIntegrationLinks?.finalTheoremUsesFinalIntegration === true,
    rowFamFinalUsesFinalTheorem: finalIntegrationLinks?.rowFamFinalUsesFinalTheorem === true,
    finalMatchUsesGPack: finalIntegrationLinks?.finalMatchUsesGPack === true,
    satDecisionUsesGPack: finalIntegrationLinks?.satDecisionUsesGPack === true,
    finalIntegrationLinksDigest: isPlainObject(finalIntegrationLinks) ? digestCanonical0(finalIntegrationLinks) : null,
  };
}

function summarizeHardCoverageFromReleaseGate0(gateEnvelope) {
  const generatedAcceptRunEnvelope =
    gateEnvelope?.ConcreteFinalCertificatePublicStatusEnvelope
      ?.ConcreteFinalCertificateEnvelope
      ?.ConcreteGeneratedAcceptRunEnvelope
      ?.GeneratedAcceptRunEnvelope ?? null;

  const materializedPCCPack = generatedAcceptRunEnvelope?.MaterializedPCCPack ?? null;
  const hardEnvelope = materializedPCCPack?.HardEnvelope ?? null;
  const hardCoverage = hardEnvelope?.Coverage ?? null;
  const hardCheck =
    hardEnvelope?.HardCheck ??
    hardEnvelope?.MaterializedHardEnvelope?.HardCheck ??
    materializedPCCPack?.PCCPack?.HardCheck ??
    generatedAcceptRunEnvelope?.AcceptRun?.Pgen?.HardCheck ??
    null;

  return {
    kind: 'ConcreteReleaseAppendixHardCoverage0',
    version: CHECKER_VERSION,
    hardEnvelopeKind: hardEnvelope?.kind ?? null,
    concreteHardCheck: hardEnvelope?.kind === 'ConcreteMaterializedHardCheck0',
    hardCheckerCoverageComplete: hardCoverage?.checkerCoverageComplete === true,
    hardRowKeyCoverageComplete: hardCoverage?.rowKeyCoverageComplete === true,
    hardRoutePriorityComplete: hardCoverage?.routePriorityComplete === true,
    hardProofRefPolicyComplete: hardCoverage?.proofRefPolicyComplete === true,
    hardHashDisciplineComplete: hardCoverage?.hashDisciplineComplete === true,
    hardNoMinCoverageComplete: hardCoverage?.noMinCoverageComplete === true,
    hardImportPolicyComplete: hardCoverage?.importPolicyComplete === true,
    hardReflectionPolicyComplete: hardCoverage?.reflectionPolicyComplete === true,
    hardBoundsPolicyComplete: hardCoverage?.boundsPolicyComplete === true,
    hardDiagnosticsPolicyComplete: hardCoverage?.diagnosticsPolicyComplete === true,
    hardCoverageDigest: isPlainObject(hardCoverage) ? digestCanonical0(hardCoverage) : null,
    hardCheckDigest: isPlainObject(hardCheck) ? digestCanonical0(hardCheck) : null,
  };
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteReleaseAppendixConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteReleaseAppendixConfig0') {
    return validationReject0(['kind'], 'ConcreteReleaseAppendixConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteReleaseAppendixConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkConcreteReleaseGate',
    'checkAppendix',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteReleaseAppendixConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.concreteReleaseGateConfig)) {
    return validationReject0(['concreteReleaseGateConfig'], 'concreteReleaseGateConfig must be an object', {
      actual: typeof config.concreteReleaseGateConfig,
    });
  }

  return validationAccept0({
    kind: 'ConcreteReleaseAppendixConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteReleaseAppendix0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteReleaseAppendix0') {
    return validationReject0(['kind'], 'ConcreteReleaseAppendix0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteReleaseAppendix0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.ReleaseAuditConcreteFinalCertificateGateEnvelope)) {
    return validationReject0(['ReleaseAuditConcreteFinalCertificateGateEnvelope'], 'ConcreteReleaseAppendix0 must include ReleaseAuditConcreteFinalCertificateGateEnvelope', {
      actual: typeof envelope.ReleaseAuditConcreteFinalCertificateGateEnvelope,
    });
  }

  if (!isPlainObject(envelope.Appendix)) {
    return validationReject0(['Appendix'], 'ConcreteReleaseAppendix0 must include Appendix', {
      actual: typeof envelope.Appendix,
    });
  }

  return validationAccept0({
    kind: 'ConcreteReleaseAppendixShape0NF',
  });
}

function validateAppendixRecord0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['Appendix'], 'ConcreteReleaseAppendix record must match recomputed appendix summary', {
      expectedDigest: digestCanonical0(expected),
      actualDigest: digestCanonical0(actual),
    });
  }

  const requiredTrue = [
    'releaseAuditAttached',
    'concreteRows',
    'concreteLocalPackages',
    'concreteGlobalFirewalls',
    'concreteGlobalProofDAG',
    'concreteKBundle',
    'kBundleKernelRuleCoverageComplete',
    'kBundleSigmaProofRefsResolve',
    'kBundleReflectionProofRefsResolve',

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
    'finalCertificateUsesConcreteAcceptRun',
    'statusUsesConcreteFinalCertificate',
    'publicConclusionEmitted',
  ];

  for (const field of requiredTrue) {
    if (actual[field] !== true) {
      return validationReject0(['Appendix', field], `ConcreteReleaseAppendix must certify ${field}`, {
        actual: actual[field],
      });
    }
  }

  if (actual.status !== 'accepted' || actual.verdict !== 'accept') {
    return validationReject0(['Appendix', 'status'], 'ConcreteReleaseAppendix must record accepted verdict', {
      status: actual.status,
      verdict: actual.verdict,
    });
  }

  if (!samePublicConclusion0(actual.publicConclusion, {
    antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
    consequent: 'P = NP',
    conditional: true,
  })) {
    return validationReject0(['Appendix', 'publicConclusion'], 'ConcreteReleaseAppendix public conclusion mismatch', {
      actual: actual.publicConclusion,
    });
  }

  return validationAccept0({
    kind: 'ConcreteReleaseAppendixRecord0NF',
    appendixDigest: digestCanonical0(actual),
    pccPackDigest: actual.pccPackDigest,
    finalVerdictDigest: actual.finalVerdictDigest,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['ConcreteReleaseAppendix0'], 'ConcreteReleaseAppendix0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ConcreteReleaseAppendix0'], 'ConcreteReleaseAppendix0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteReleaseAppendixJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope) {
  const gate = envelope.ReleaseAuditConcreteFinalCertificateGateEnvelope;

  const expected = {
    concreteReleaseGateEnvelopeDigest: digestCanonical0(gate),
    releaseAuditDigest: gate.ReleaseAuditRecord.Digest ?? gate.ReleaseAuditRecord.digest,
    concretePublicStatusEnvelopeDigest: digestCanonical0(gate.ConcreteFinalCertificatePublicStatusEnvelope),
    publicStatusDigest: digestCanonical0(gate.ConcreteFinalCertificatePublicStatusEnvelope.FinalCertificatePublicStatusEnvelope.PublicStatus),
    concreteFinalCertificateDigest: digestCanonical0(gate.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope),
    certificateDigest: digestCanonical0(gate.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(gate.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest:
      gate.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict.Digest ??
      gate.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.FinalCertificateEnvelope.FinalVerdict.digest,
    acceptRunDigest: digestCanonical0(
      gate.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun,
    ),
    pccPackDigest: digestCanonical0(
      gate.ConcreteFinalCertificatePublicStatusEnvelope.ConcreteFinalCertificateEnvelope.ConcreteGeneratedAcceptRunEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen,
    ),
    appendixDigest: digestCanonical0(envelope.Appendix),
  };

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteReleaseAppendixLinkage0NF',
      present: false,
      ...expected,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteReleaseAppendix0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
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
    kind: 'ConcreteReleaseAppendixLinkage0NF',
    present: true,
    ...expected,
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ConcreteReleaseAppendixFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === CONCRETE_RELEASE_APPENDIX_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== CONCRETE_RELEASE_APPENDIX_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== CONCRETE_RELEASE_APPENDIX_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'concrete release appendix contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ConcreteReleaseAppendixNoForbiddenFixtureMarkers0NF',
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
      CONCRETE_RELEASE_APPENDIX_SYNTHETIC_MARKER0,
      ...CONCRETE_RELEASE_APPENDIX_FORBIDDEN_MARKERS0,
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

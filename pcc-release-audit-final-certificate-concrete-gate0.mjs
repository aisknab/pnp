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

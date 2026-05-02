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

const CHECKER_VERSION = 0;

export const FINAL_CERTIFICATE_PUBLIC_STATUS_PHASES0 = Object.freeze([
  'CheckFinalCertificatePublicStatusInput0',
  'CheckMaterializedFinalCertificate0',
  'CheckReleaseAuditAttachment0',
  'CheckFinalCertificatePublicStatusPolicy0',
  'CheckFinalCertificatePublicStatusEmission0',
  'CheckFinalCertificatePublicStatusLinkage0',
]);

export const FINAL_CERTIFICATE_PUBLIC_STATUS_POLICY0 = Object.freeze({
  kind: 'FinalCertificatePublicStatusPolicy0',
  version: CHECKER_VERSION,
  materializedPathOnly: true,
  separateFromSyntheticRunAll: true,
  publicConclusionOnlyAfterAcceptedCertificate: true,
  publicConclusionOnlyAfterAcceptedReplay: true,
  rejectEmitsNoPublicConclusion: true,
  certificateMustCarryCanonicalByteRoots: true,
  certificateMustCarryAcceptanceTranscriptDigest: true,
  certificateMustCarryFinalVerdictDigest: true,
  releaseAuditMayBeAttachedLater: true,
});

const FINAL_CERTIFICATE_PUBLIC_STATUS_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const FINAL_CERTIFICATE_PUBLIC_STATUS_SYNTHETIC_MARKER0 = 'synthetic';

export function makeFinalCertificatePublicStatusConfig0(overrides = {}) {
  return {
    kind: 'FinalCertificatePublicStatusConfig0',
    version: CHECKER_VERSION,
    checkFinalCertificate: true,
    checkReleaseAuditRecord: false,
    checkPublicStatus: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    finalCertificateConfig: {},
    ...overrides,
  };
}

export async function makeFinalCertificatePublicStatus0({
  FinalCertificateEnvelope = null,
  ReleaseAuditRecord = null,
  PublicStatus = null,
  overrides = {},
} = {}) {
  const finalCertificateEnvelope = FinalCertificateEnvelope ?? await makeMaterializedFinalCertificate0();
  const releaseAuditRecord = ReleaseAuditRecord ?? null;
  const publicStatus = PublicStatus ?? emitFinalCertificatePublicStatus0({
    finalCertificateEnvelope,
    releaseAuditRecord,
  });

  const linkage = {
    kind: 'FinalCertificatePublicStatusLinkage0',
    version: CHECKER_VERSION,
    finalCertificateEnvelopeDigest: digestCanonical0(finalCertificateEnvelope),
    certificateDigest: digestCanonical0(finalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(finalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest: finalCertificateEnvelope.FinalVerdict.Digest ?? finalCertificateEnvelope.FinalVerdict.digest ?? null,
    generatedAcceptRunEnvelopeDigest: digestCanonical0(finalCertificateEnvelope.GeneratedAcceptRunEnvelope),
    acceptRunDigest: digestCanonical0(finalCertificateEnvelope.GeneratedAcceptRunEnvelope.AcceptRun),
    pccPackDigest: digestCanonical0(finalCertificateEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen),
    publicStatusDigest: digestCanonical0(publicStatus),
    releaseAuditAttached: isPlainObject(releaseAuditRecord),
    releaseAuditDigest: isPlainObject(releaseAuditRecord)
      ? releaseAuditRecord.Digest ?? releaseAuditRecord.digest ?? digestCanonical0(releaseAuditRecord)
      : null,
  };

  return {
    kind: 'FinalCertificatePublicStatus0',
    version: CHECKER_VERSION,
    FinalCertificateEnvelope: finalCertificateEnvelope,
    ReleaseAuditRecord: releaseAuditRecord,
    StatusPolicy: {
      ...FINAL_CERTIFICATE_PUBLIC_STATUS_POLICY0,
    },
    PublicStatus: publicStatus,
    Linkage: linkage,
    PiFinalCertificatePublicStatus: {
      kind: 'PiFinalCertificatePublicStatus0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'FinalCertificate',
          digest: linkage.certificateDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'PublicStatus',
          digest: linkage.publicStatusDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function emitFinalCertificatePublicStatus0({
  finalCertificateEnvelope,
  releaseAuditRecord = null,
}) {
  const certificate = finalCertificateEnvelope.Certificate;
  const finalVerdict = finalCertificateEnvelope.FinalVerdict;
  const finalNF = finalVerdict.NF ?? finalVerdict.nf ?? {};
  const releaseAuditAttached = isPlainObject(releaseAuditRecord);

  return {
    kind: 'FinalCertificatePublicStatusEmission0',
    version: CHECKER_VERSION,
    status: 'accepted',
    verdict: 'accept',
    materializedPath: true,
    syntheticRunAll: false,
    acceptedCertificate: true,
    replayAccepted: true,
    publicConclusionEmitted: true,
    publicConclusion: certificate.publicTheorem,
    claimBoundary: 'conditional-on-accepted-final-certificate',
    noClaimBeforeAccept: true,

    checker: certificate.checker,
    generator: certificate.generator,
    runId: certificate.runId,

    certificateDigest: digestCanonical0(certificate),
    finalVerdictDigest: finalVerdict.Digest ?? finalVerdict.digest ?? digestCanonical0(finalVerdict),
    finalVerdictObjectDigest: digestCanonical0(finalVerdict),
    generatedAcceptRunEnvelopeDigest: digestCanonical0(finalCertificateEnvelope.GeneratedAcceptRunEnvelope),
    acceptRunDigest: certificate.artefactDigests.acceptRunDigest,
    pccPackDigest: certificate.artefactDigests.pccPackDigest,

    canonicalByteRoots: certificate.canonicalByteRoots,
    acceptanceTranscript: certificate.acceptanceTranscript,

    releaseAuditAttached,
    releaseAuditDigest: releaseAuditAttached
      ? releaseAuditRecord.Digest ?? releaseAuditRecord.digest ?? digestCanonical0(releaseAuditRecord)
      : certificate.releaseAuditDigest,
    releaseAuditStatus: releaseAuditAttached
      ? 'attached'
      : certificate.releaseAuditStatus,

    sourceFinalVerdictPublicConclusion: finalNF.publicConclusion ?? null,
  };
}

export async function CheckFinalCertificatePublicStatus0(
  input,
  config = makeFinalCertificatePublicStatusConfig0(),
) {
  const checker = 'CheckFinalCertificatePublicStatus0';
  const ledger = [];
  const cfg = makeFinalCertificatePublicStatusConfig0(config);
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
    phase: 'CheckFinalCertificatePublicStatusInput0',
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

  if (cfg.checkFinalCertificate === true) {
    const certRecord = await CheckMaterializedFinalCertificate0(
      envelope.FinalCertificateEnvelope,
      cfg.finalCertificateConfig ?? {},
    );
    const cert = recordToValidation0(certRecord, ['FinalCertificateEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedFinalCertificate0',
      status: cert.ok ? 'pass' : 'fail',
      digest: certRecord.Digest ?? certRecord.digest ?? digestCanonical0(certRecord),
    });

    if (!cert.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.FinalCertificate`,
        path: cert.path,
        witness: cert.witness,
        ledger,
      });
    }
  }

  if (cfg.checkReleaseAuditRecord === true) {
    const releaseAudit = validateReleaseAuditRecord0(envelope.ReleaseAuditRecord);

    ledger.push({
      phase: 'CheckReleaseAuditAttachment0',
      status: releaseAudit.ok ? 'pass' : 'fail',
      digest: digestCanonical0(releaseAudit.nf ?? releaseAudit.witness ?? null),
    });

    if (!releaseAudit.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ReleaseAudit`,
        path: releaseAudit.path,
        witness: releaseAudit.witness,
        ledger,
      });
    }
  } else {
    ledger.push({
      phase: 'CheckReleaseAuditAttachment0',
      status: 'pass',
      digest: digestCanonical0({
        skipped: true,
        attached: isPlainObject(envelope.ReleaseAuditRecord),
      }),
    });
  }

  const policy = validateStatusPolicy0(envelope.StatusPolicy);

  ledger.push({
    phase: 'CheckFinalCertificatePublicStatusPolicy0',
    status: policy.ok ? 'pass' : 'fail',
    digest: digestCanonical0(policy.nf ?? policy.witness ?? null),
  });

  if (!policy.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.StatusPolicy`,
      path: policy.path,
      witness: policy.witness,
      ledger,
    });
  }

  if (cfg.checkPublicStatus === true) {
    const publicStatus = validatePublicStatus0(envelope.PublicStatus, envelope);

    ledger.push({
      phase: 'CheckFinalCertificatePublicStatusEmission0',
      status: publicStatus.ok ? 'pass' : 'fail',
      digest: digestCanonical0(publicStatus.nf ?? publicStatus.witness ?? null),
    });

    if (!publicStatus.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.PublicStatus`,
        path: publicStatus.path,
        witness: publicStatus.witness,
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

  const markerInventory = collectFixtureMarkers0(envelope, ['FinalCertificatePublicStatus0']);

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
      phase: 'CheckFinalCertificatePublicStatusLinkage0',
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

  const publicStatus = envelope.PublicStatus;

  const nf = {
    kind: 'FinalCertificatePublicStatus0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: FINAL_CERTIFICATE_PUBLIC_STATUS_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,
    status: publicStatus.status,
    verdict: publicStatus.verdict,
    acceptedCertificate: publicStatus.acceptedCertificate,
    replayAccepted: publicStatus.replayAccepted,
    publicConclusionEmitted: publicStatus.publicConclusionEmitted,
    publicConclusion: publicStatus.publicConclusion,
    claimBoundary: publicStatus.claimBoundary,
    checkerTarget: publicStatus.checker,
    generator: publicStatus.generator,
    runId: publicStatus.runId,
    certificateDigest: publicStatus.certificateDigest,
    finalVerdictDigest: publicStatus.finalVerdictDigest,
    acceptRunDigest: publicStatus.acceptRunDigest,
    pccPackDigest: publicStatus.pccPackDigest,
    canonicalByteRoots: publicStatus.canonicalByteRoots,
    acceptanceTranscript: publicStatus.acceptanceTranscript,
    releaseAuditAttached: publicStatus.releaseAuditAttached,
    releaseAuditDigest: publicStatus.releaseAuditDigest,
    releaseAuditStatus: publicStatus.releaseAuditStatus,
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

export async function writeFinalCertificatePublicStatusFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeFinalCertificatePublicStatusFiles0 requires a non-empty output directory');
  }

  const envelope = await makeFinalCertificatePublicStatus0(options);
  const checked = await CheckFinalCertificatePublicStatus0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'FinalCertificatePublicStatus0.json');
  const publicStatusPath = path.join(outDir, 'FinalCertificatePublicStatusEmission0.json');
  const certificatePath = path.join(outDir, 'FinalCertificate0.json');
  const finalVerdictPath = path.join(outDir, 'EmitFinalVerdict0.json');
  const checkPath = path.join(outDir, 'FinalCertificatePublicStatus0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(publicStatusPath, envelope.PublicStatus);
  await writeJsonFile0(certificatePath, envelope.FinalCertificateEnvelope.Certificate);
  await writeJsonFile0(finalVerdictPath, envelope.FinalCertificateEnvelope.FinalVerdict);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      publicStatusPath,
      certificatePath,
      finalVerdictPath,
      checkPath,
    },
  };
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'FinalCertificatePublicStatusConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'FinalCertificatePublicStatusConfig0') {
    return validationReject0(['kind'], 'FinalCertificatePublicStatusConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalCertificatePublicStatusConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkFinalCertificate',
    'checkReleaseAuditRecord',
    'checkPublicStatus',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `FinalCertificatePublicStatusConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.finalCertificateConfig)) {
    return validationReject0(['finalCertificateConfig'], 'finalCertificateConfig must be an object', {
      actual: typeof config.finalCertificateConfig,
    });
  }

  return validationAccept0({
    kind: 'FinalCertificatePublicStatusConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'FinalCertificatePublicStatus0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'FinalCertificatePublicStatus0') {
    return validationReject0(['kind'], 'FinalCertificatePublicStatus0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalCertificatePublicStatus0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.FinalCertificateEnvelope)) {
    return validationReject0(['FinalCertificateEnvelope'], 'FinalCertificatePublicStatus0 must include FinalCertificateEnvelope', {
      actual: typeof envelope.FinalCertificateEnvelope,
    });
  }

  if (!isPlainObject(envelope.StatusPolicy)) {
    return validationReject0(['StatusPolicy'], 'FinalCertificatePublicStatus0 must include StatusPolicy', {
      actual: typeof envelope.StatusPolicy,
    });
  }

  if (!isPlainObject(envelope.PublicStatus)) {
    return validationReject0(['PublicStatus'], 'FinalCertificatePublicStatus0 must include PublicStatus', {
      actual: typeof envelope.PublicStatus,
    });
  }

  if (envelope.PublicStatus.kind !== 'FinalCertificatePublicStatusEmission0') {
    return validationReject0(['PublicStatus', 'kind'], 'PublicStatus kind must be FinalCertificatePublicStatusEmission0', {
      actual: envelope.PublicStatus.kind,
    });
  }

  return validationAccept0({
    kind: 'FinalCertificatePublicStatusShape0NF',
  });
}

function validateStatusPolicy0(policy) {
  if (!isPlainObject(policy)) {
    return validationReject0(['StatusPolicy'], 'StatusPolicy must be an object', {
      actual: typeof policy,
    });
  }

  if (policy.kind !== undefined && policy.kind !== 'FinalCertificatePublicStatusPolicy0') {
    return validationReject0(['StatusPolicy', 'kind'], 'StatusPolicy kind mismatch', {
      actual: policy.kind,
    });
  }

  for (const field of [
    'materializedPathOnly',
    'separateFromSyntheticRunAll',
    'publicConclusionOnlyAfterAcceptedCertificate',
    'publicConclusionOnlyAfterAcceptedReplay',
    'rejectEmitsNoPublicConclusion',
    'certificateMustCarryCanonicalByteRoots',
    'certificateMustCarryAcceptanceTranscriptDigest',
    'certificateMustCarryFinalVerdictDigest',
    'releaseAuditMayBeAttachedLater',
  ]) {
    if (policy[field] !== true) {
      return validationReject0(['StatusPolicy', field], `StatusPolicy must certify ${field}`, {
        actual: policy[field],
      });
    }
  }

  return validationAccept0({
    kind: 'FinalCertificatePublicStatusPolicy0NF',
  });
}

function validateReleaseAuditRecord0(record) {
  if (!isPlainObject(record)) {
    return validationReject0(['ReleaseAuditRecord'], 'ReleaseAuditRecord must be an accepted CheckReleaseAudit0 record when checking is enabled', {
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
    return validationReject0(['ReleaseAuditRecord', 'NF'], 'ReleaseAuditRecord must expose an NF object', {
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
    kind: 'ReleaseAuditAttachment0NF',
    releaseAuditDigest: record.Digest ?? record.digest,
  });
}

function validatePublicStatus0(publicStatus, envelope) {
  const certEnvelope = envelope.FinalCertificateEnvelope;
  const certificate = certEnvelope.Certificate;
  const finalVerdict = certEnvelope.FinalVerdict;
  const finalNF = finalVerdict.NF ?? finalVerdict.nf ?? {};

  if (publicStatus.status !== 'accepted') {
    return validationReject0(['PublicStatus', 'status'], 'Final certificate public status must be accepted', {
      actual: publicStatus.status,
    });
  }

  if (publicStatus.verdict !== 'accept') {
    return validationReject0(['PublicStatus', 'verdict'], 'Final certificate public status verdict must be accept', {
      actual: publicStatus.verdict,
    });
  }

  for (const field of [
    'materializedPath',
    'acceptedCertificate',
    'replayAccepted',
    'publicConclusionEmitted',
    'noClaimBeforeAccept',
  ]) {
    if (publicStatus[field] !== true) {
      return validationReject0(['PublicStatus', field], `PublicStatus must certify ${field}`, {
        actual: publicStatus[field],
      });
    }
  }

  if (publicStatus.syntheticRunAll !== false) {
    return validationReject0(['PublicStatus', 'syntheticRunAll'], 'PublicStatus must remain separate from synthetic RunAll0', {
      actual: publicStatus.syntheticRunAll,
    });
  }

  if (publicStatus.claimBoundary !== 'conditional-on-accepted-final-certificate') {
    return validationReject0(['PublicStatus', 'claimBoundary'], 'PublicStatus claim boundary mismatch', {
      actual: publicStatus.claimBoundary,
    });
  }

  if (!samePublicConclusion0(publicStatus.publicConclusion, certificate.publicTheorem)) {
    return validationReject0(['PublicStatus', 'publicConclusion'], 'PublicStatus public conclusion must match certificate public theorem', {
      expected: certificate.publicTheorem,
      actual: publicStatus.publicConclusion,
    });
  }

  if (!samePublicConclusion0(publicStatus.publicConclusion, finalNF.publicConclusion)) {
    return validationReject0(['PublicStatus', 'publicConclusion'], 'PublicStatus public conclusion must match final verdict public conclusion', {
      expected: finalNF.publicConclusion,
      actual: publicStatus.publicConclusion,
    });
  }

  const digestChecks = [
    ['certificateDigest', digestCanonical0(certificate)],
    ['finalVerdictDigest', finalVerdict.Digest ?? finalVerdict.digest],
    ['finalVerdictObjectDigest', digestCanonical0(finalVerdict)],
    ['generatedAcceptRunEnvelopeDigest', digestCanonical0(certEnvelope.GeneratedAcceptRunEnvelope)],
    ['acceptRunDigest', certificate.artefactDigests.acceptRunDigest],
    ['pccPackDigest', certificate.artefactDigests.pccPackDigest],
  ];

  for (const [field, expected] of digestChecks) {
    if (!sameDigestHex0(publicStatus[field], expected)) {
      return validationReject0(['PublicStatus', field], `PublicStatus ${field} mismatch`, {
        expected,
        actual: publicStatus[field],
      });
    }
  }

  if (!isPlainObject(publicStatus.canonicalByteRoots)) {
    return validationReject0(['PublicStatus', 'canonicalByteRoots'], 'PublicStatus must expose canonical byte roots', {
      actual: typeof publicStatus.canonicalByteRoots,
    });
  }

  if (stableStringify0(publicStatus.canonicalByteRoots) !== stableStringify0(certificate.canonicalByteRoots)) {
    return validationReject0(['PublicStatus', 'canonicalByteRoots'], 'PublicStatus canonicalByteRoots must match certificate', {
      expected: certificate.canonicalByteRoots,
      actual: publicStatus.canonicalByteRoots,
    });
  }

  if (!isPlainObject(publicStatus.acceptanceTranscript)) {
    return validationReject0(['PublicStatus', 'acceptanceTranscript'], 'PublicStatus must expose acceptance transcript digests', {
      actual: typeof publicStatus.acceptanceTranscript,
    });
  }

  if (stableStringify0(publicStatus.acceptanceTranscript) !== stableStringify0(certificate.acceptanceTranscript)) {
    return validationReject0(['PublicStatus', 'acceptanceTranscript'], 'PublicStatus acceptanceTranscript must match certificate', {
      expected: certificate.acceptanceTranscript,
      actual: publicStatus.acceptanceTranscript,
    });
  }

  if (isPlainObject(envelope.ReleaseAuditRecord)) {
    const releaseAuditDigest = envelope.ReleaseAuditRecord.Digest ?? envelope.ReleaseAuditRecord.digest;

    if (publicStatus.releaseAuditAttached !== true) {
      return validationReject0(['PublicStatus', 'releaseAuditAttached'], 'PublicStatus must mark attached release audit when ReleaseAuditRecord is present', {
        actual: publicStatus.releaseAuditAttached,
      });
    }

    if (!sameDigestHex0(publicStatus.releaseAuditDigest, releaseAuditDigest)) {
      return validationReject0(['PublicStatus', 'releaseAuditDigest'], 'PublicStatus releaseAuditDigest mismatch', {
        expected: releaseAuditDigest,
        actual: publicStatus.releaseAuditDigest,
      });
    }

    if (publicStatus.releaseAuditStatus !== 'attached') {
      return validationReject0(['PublicStatus', 'releaseAuditStatus'], 'PublicStatus releaseAuditStatus must be attached when ReleaseAuditRecord is present', {
        actual: publicStatus.releaseAuditStatus,
      });
    }
  }

  return validationAccept0({
    kind: 'FinalCertificatePublicStatusEmission0NF',
    certificateDigest: publicStatus.certificateDigest,
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
    return validationReject0(['FinalCertificatePublicStatus0'], 'FinalCertificatePublicStatus0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['FinalCertificatePublicStatus0'], 'FinalCertificatePublicStatus0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'FinalCertificatePublicStatusJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'FinalCertificatePublicStatusFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === FINAL_CERTIFICATE_PUBLIC_STATUS_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== FINAL_CERTIFICATE_PUBLIC_STATUS_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== FINAL_CERTIFICATE_PUBLIC_STATUS_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'final certificate public status contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'FinalCertificatePublicStatusNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function validateLinkage0(envelope) {
  const expected = {
    finalCertificateEnvelopeDigest: digestCanonical0(envelope.FinalCertificateEnvelope),
    certificateDigest: digestCanonical0(envelope.FinalCertificateEnvelope.Certificate),
    finalVerdictDigest: digestCanonical0(envelope.FinalCertificateEnvelope.FinalVerdict),
    finalVerdictRecordDigest: envelope.FinalCertificateEnvelope.FinalVerdict.Digest ?? envelope.FinalCertificateEnvelope.FinalVerdict.digest,
    generatedAcceptRunEnvelopeDigest: digestCanonical0(envelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope),
    acceptRunDigest: digestCanonical0(envelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope.AcceptRun),
    pccPackDigest: digestCanonical0(envelope.FinalCertificateEnvelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen),
    publicStatusDigest: digestCanonical0(envelope.PublicStatus),
    releaseAuditDigest: isPlainObject(envelope.ReleaseAuditRecord)
      ? envelope.ReleaseAuditRecord.Digest ?? envelope.ReleaseAuditRecord.digest ?? digestCanonical0(envelope.ReleaseAuditRecord)
      : null,
  };

  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'FinalCertificatePublicStatusLinkage0NF',
      present: false,
      ...expected,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'FinalCertificatePublicStatus0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (expectedDigest === null) {
      if (envelope.Linkage[field] !== null) {
        return validationReject0(['Linkage', field], `Linkage ${field} must be null`, {
          expected: null,
          actual: envelope.Linkage[field],
        });
      }

      continue;
    }

    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  if (envelope.Linkage.releaseAuditAttached !== isPlainObject(envelope.ReleaseAuditRecord)) {
    return validationReject0(['Linkage', 'releaseAuditAttached'], 'Linkage releaseAuditAttached mismatch', {
      expected: isPlainObject(envelope.ReleaseAuditRecord),
      actual: envelope.Linkage.releaseAuditAttached,
    });
  }

  return validationAccept0({
    kind: 'FinalCertificatePublicStatusLinkage0NF',
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
      FINAL_CERTIFICATE_PUBLIC_STATUS_SYNTHETIC_MARKER0,
      ...FINAL_CERTIFICATE_PUBLIC_STATUS_FORBIDDEN_MARKERS0,
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

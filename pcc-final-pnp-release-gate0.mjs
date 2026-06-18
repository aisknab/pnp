import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckFinalPNPCertificate0,
  makeFinalPNPCertificate0,
} from './pcc-final-pnp-certificate0.mjs';

const CHECKER_VERSION = 0;

export const FINAL_PNP_RELEASE_GATE_PHASES0 = Object.freeze([
  'CheckFinalPNPReleaseGateInput0',
  'CheckReleaseAuditRecord0',
  'CheckFinalPNPCertificate0',
  'CheckFinalPNPReleaseGateContract0',
  'CheckFinalPNPReleaseGateJson0',
  'CheckFinalPNPReleaseGateLinkage0',
  'EmitFinalPNPReleaseGate0',
]);

export function makeFinalPNPReleaseGateConfig0(overrides = {}) {
  return {
    kind: 'FinalPNPReleaseGateConfig0',
    version: CHECKER_VERSION,
    checkReleaseAuditRecord: true,
    checkFinalPNPCertificate: true,
    checkContract: true,
    checkJsonMaterialized: true,
    checkLinkage: true,
    finalPNPCertificateConfig: {},
    ...overrides,
  };
}

export async function makeFinalPNPReleaseGate0({
  FinalPNPCertificateEnvelope = null,
  overrides = {},
} = {}) {
  const finalPNPCertificateEnvelope =
    FinalPNPCertificateEnvelope ?? await makeFinalPNPCertificate0();

  const checkFinalPNPCertificateRecord =
    await CheckFinalPNPCertificate0(finalPNPCertificateEnvelope);

  const releaseAuditRecord = resolveReleaseAuditRecord0(finalPNPCertificateEnvelope);

  const linkage = makeLinkage0({
    finalPNPCertificateEnvelope,
    checkFinalPNPCertificateRecord,
    releaseAuditRecord,
  });

  return {
    kind: 'FinalPNPReleaseGate0',
    version: CHECKER_VERSION,
    FinalPNPCertificateEnvelope: finalPNPCertificateEnvelope,
    CheckFinalPNPCertificateRecord: checkFinalPNPCertificateRecord,
    ReleaseAuditRecord: releaseAuditRecord,
    Linkage: linkage,
    PiFinalPNPReleaseGate: {
      kind: 'PiFinalPNPReleaseGate0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'FinalPNPCertificateEnvelope',
          digest: linkage.finalPNPCertificateEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'CheckFinalPNPCertificateRecord',
          digest: linkage.checkFinalPNPCertificateRecordDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ReleaseAuditRecord',
          digest: linkage.releaseAuditRecordDigest,
        },
      ],
    },
    ...overrides,
  };
}

export async function CheckFinalPNPReleaseGate0(
  input,
  config = makeFinalPNPReleaseGateConfig0(),
) {
  const checker = 'CheckFinalPNPReleaseGate0';
  const ledger = [];
  const cfg = makeFinalPNPReleaseGateConfig0(config);
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
    phase: 'CheckFinalPNPReleaseGateInput0',
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

  let finalPNPCertificateRecord = envelope.CheckFinalPNPCertificateRecord;

  if (cfg.checkFinalPNPCertificate === true) {
    const fresh = await CheckFinalPNPCertificate0(
      envelope.FinalPNPCertificateEnvelope,
      cfg.finalPNPCertificateConfig ?? {},
    );

    const result = recordToValidation0(fresh, ['FinalPNPCertificateEnvelope']);

    ledger.push({
      phase: 'CheckFinalPNPCertificate0',
      status: result.ok ? 'pass' : 'fail',
      digest: fresh.Digest ?? fresh.digest ?? digestCanonical0(fresh),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.FinalPNPCertificate`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    const materialized = validateMaterializedRecord0(
      envelope.CheckFinalPNPCertificateRecord,
      fresh,
      ['CheckFinalPNPCertificateRecord'],
      'CheckFinalPNPCertificateRecord',
    );

    ledger.push({
      phase: 'CheckFinalPNPCertificateRecord',
      status: materialized.ok ? 'pass' : 'fail',
      digest: digestCanonical0(materialized.nf ?? materialized.witness ?? null),
    });

    if (!materialized.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckFinalPNPCertificateRecord`,
        path: materialized.path,
        witness: materialized.witness,
        ledger,
      });
    }

    finalPNPCertificateRecord = envelope.CheckFinalPNPCertificateRecord;
  }

  const contract = validateFinalPNPReleaseGateContract0({
    envelope,
    finalPNPCertificateRecord,
  });

  if (cfg.checkContract === true) {
    ledger.push({
      phase: 'CheckFinalPNPReleaseGateContract0',
      status: contract.ok ? 'pass' : 'fail',
      digest: digestCanonical0(contract.nf ?? contract.witness ?? null),
    });

    if (!contract.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.contract`,
        path: contract.path,
        witness: contract.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope);

    ledger.push({
      phase: 'CheckFinalPNPReleaseGateJson0',
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

  if (cfg.checkLinkage === true) {
    const linkage = validateLinkage0(envelope, finalPNPCertificateRecord);

    ledger.push({
      phase: 'CheckFinalPNPReleaseGateLinkage0',
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

  const cert = envelope.FinalPNPCertificateEnvelope.Certificate;
  const contractNF = contract.nf ?? {};

  const nf = {
    kind: 'FinalPNPReleaseGate0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: FINAL_PNP_RELEASE_GATE_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,

    finalPNPReleaseGateAccepted: true,
    finalPNPCertificateAccepted: contractNF.finalPNPCertificateAccepted === true,
    releaseAuditAccepted: contractNF.releaseAuditAccepted === true,
    finalAcceptanceReplayClosed: cert.finalAcceptanceReplayClosed === true,

    status: cert.status,
    verdict: cert.verdict,
    theorem: cert.theorem,
    claimBoundary: cert.claimBoundary,
    noClaimBeforeAccept: cert.noClaimBeforeAccept === true,

    generator: cert.generator,
    checkerName: cert.checker,
    generatorIsGeneratePCCPack: cert.generatorIsGeneratePCCPack === true,
    checkPCCPackexpAccepted: cert.checkPCCPackexpAccepted === true,
    checkAcceptRunAccepted: cert.checkAcceptRunAccepted === true,
    replayAccepted: cert.replayAccepted === true,
    finalVerdictAccepted: cert.finalVerdictAccepted === true,

    publicConclusionEmitted: cert.publicConclusionEmitted === true,
    publicConclusionAntecedent: cert.publicConclusionAntecedent,
    publicConclusionConsequent: cert.publicConclusionConsequent,
    publicConclusionConditional: cert.publicConclusionConditional === true,

    checkPCCPackexpGeneratedPackageImplication:
      cert.checkPCCPackexpGeneratedPackageImplication === true,
    checkPCCPackexpConcreteCoverageComplete:
      cert.checkPCCPackexpConcreteCoverageComplete === true,
    checkPCCPackexpPCCPackLinkageComplete:
      cert.checkPCCPackexpPCCPackLinkageComplete === true,

    releaseAuditDigest: cert.releaseAuditDigest,
    finalPNPCertificateEnvelopeDigest:
      digestCanonical0(envelope.FinalPNPCertificateEnvelope),
    checkFinalPNPCertificateRecordDigest:
      digestFromRecord0(finalPNPCertificateRecord),
    certificateDigest: digestCanonical0(cert),
    acceptRunDigest: cert.acceptRunDigest,
    pccPackDigest: cert.pccPackDigest,
    acceptanceTranscriptDigest: cert.acceptanceTranscriptDigest,
    finalVerdictRecordDigest: cert.finalVerdictRecordDigest,
    checkPCCPackexpRecordDigest: cert.checkPCCPackexpRecordDigest,
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeFinalPNPReleaseGateFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeFinalPNPReleaseGateFiles0 requires a non-empty output directory');
  }

  const envelope = await makeFinalPNPReleaseGate0(options);
  const checked = await CheckFinalPNPReleaseGate0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'FinalPNPReleaseGate0.json');
  const certificateEnvelopePath = path.join(outDir, 'FinalPNPCertificate0.json');
  const certificateRecordPath = path.join(outDir, 'FinalPNPCertificate0.check.json');
  const releaseAuditPath = path.join(outDir, 'ReleaseAudit0.json');
  const certificatePath = path.join(outDir, 'FinalPNPCertificateRecord0.json');
  const checkPath = path.join(outDir, 'FinalPNPReleaseGate0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(certificateEnvelopePath, envelope.FinalPNPCertificateEnvelope);
  await writeJsonFile0(certificateRecordPath, envelope.CheckFinalPNPCertificateRecord);
  await writeJsonFile0(releaseAuditPath, envelope.ReleaseAuditRecord);
  await writeJsonFile0(certificatePath, envelope.FinalPNPCertificateEnvelope.Certificate);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      certificateEnvelopePath,
      certificateRecordPath,
      releaseAuditPath,
      certificatePath,
      checkPath,
    },
  };
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'FinalPNPReleaseGateConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'FinalPNPReleaseGateConfig0') {
    return validationReject0(['kind'], 'FinalPNPReleaseGateConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalPNPReleaseGateConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkReleaseAuditRecord',
    'checkFinalPNPCertificate',
    'checkContract',
    'checkJsonMaterialized',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `FinalPNPReleaseGateConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.finalPNPCertificateConfig)) {
    return validationReject0(['finalPNPCertificateConfig'], 'finalPNPCertificateConfig must be an object', {
      actual: typeof config.finalPNPCertificateConfig,
    });
  }

  return validationAccept0({
    kind: 'FinalPNPReleaseGateConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'FinalPNPReleaseGate0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'FinalPNPReleaseGate0') {
    return validationReject0(['kind'], 'FinalPNPReleaseGate0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalPNPReleaseGate0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.FinalPNPCertificateEnvelope)) {
    return validationReject0(['FinalPNPCertificateEnvelope'], 'FinalPNPReleaseGate0 must include FinalPNPCertificateEnvelope', {
      actual: typeof envelope.FinalPNPCertificateEnvelope,
    });
  }

  if (!isPlainObject(envelope.CheckFinalPNPCertificateRecord)) {
    return validationReject0(['CheckFinalPNPCertificateRecord'], 'FinalPNPReleaseGate0 must include CheckFinalPNPCertificateRecord', {
      actual: typeof envelope.CheckFinalPNPCertificateRecord,
    });
  }

  if (!isPlainObject(envelope.ReleaseAuditRecord)) {
    return validationReject0(['ReleaseAuditRecord'], 'FinalPNPReleaseGate0 must include ReleaseAuditRecord', {
      actual: typeof envelope.ReleaseAuditRecord,
    });
  }

  return validationAccept0({
    kind: 'FinalPNPReleaseGateShape0NF',
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

  const nf = recordNF0(record);

  if (!isPlainObject(nf.publicConclusion)) {
    return validationReject0(['ReleaseAuditRecord', 'NF', 'publicConclusion'], 'ReleaseAuditRecord must expose public conclusion boundary', {
      actual: typeof nf.publicConclusion,
    });
  }

  if (
    nf.publicConclusion.antecedent !== 'CheckPCCPackexp(GeneratePCCPack())=accept' ||
    nf.publicConclusion.consequent !== 'P = NP'
  ) {
    return validationReject0(['ReleaseAuditRecord', 'NF', 'publicConclusion'], 'ReleaseAuditRecord public conclusion boundary mismatch', {
      actual: nf.publicConclusion,
    });
  }

  return validationAccept0({
    kind: 'FinalPNPReleaseGateReleaseAuditRecord0NF',
    releaseAuditDigest: digestFromRecord0(record),
  });
}

function validateMaterializedRecord0(actual, expected, path, label) {
  if (!isPlainObject(actual)) {
    return validationReject0(path, `${label} must be materialized`, {
      actual: typeof actual,
    });
  }

  if (!sameDigestHex0(digestFromRecord0(actual), digestFromRecord0(expected))) {
    return validationReject0(path, `${label} digest must match freshly recomputed record`, {
      expected: digestFromRecord0(expected),
      actual: digestFromRecord0(actual),
    });
  }

  return validationAccept0({
    kind: `${label}MaterializedRecord0NF`,
    digest: digestFromRecord0(actual),
  });
}

function validateFinalPNPReleaseGateContract0({
  envelope,
  finalPNPCertificateRecord,
}) {
  const cert = envelope.FinalPNPCertificateEnvelope.Certificate;
  const releaseAuditRecord = envelope.ReleaseAuditRecord;
  const certNF = recordNF0(finalPNPCertificateRecord);

  if (!isPlainObject(cert)) {
    return validationReject0(['FinalPNPCertificateEnvelope', 'Certificate'], 'FinalPNPCertificate certificate must be materialized', {
      actual: typeof cert,
    });
  }

  if (finalPNPCertificateRecord.tag !== 'accept') {
    return validationReject0(['CheckFinalPNPCertificateRecord', 'tag'], 'CheckFinalPNPCertificateRecord must be accepted', {
      actual: finalPNPCertificateRecord.tag,
    });
  }

  const requiredTrue = [
    'finalPNPCertificateAccepted',
    'finalAcceptanceReplayClosed',
    'generatorIsGeneratePCCPack',
    'checkAcceptRunAccepted',
    'replayAccepted',
    'finalVerdictAccepted',
    'checkPCCPackexpAccepted',
    'publicConclusionEmitted',
    'publicConclusionConditional',
    'checkPCCPackexpGeneratedPackageImplication',
    'checkPCCPackexpConcreteCoverageComplete',
    'checkPCCPackexpPCCPackLinkageComplete',
  ];

  for (const field of requiredTrue) {
    if (certNF[field] !== true) {
      return validationReject0(['CheckFinalPNPCertificateRecord', 'NF', field], `FinalPNPReleaseGate requires ${field}`, {
        actual: certNF[field],
      });
    }
  }

  if (cert.status !== 'accepted' || cert.verdict !== 'accept') {
    return validationReject0(['FinalPNPCertificateEnvelope', 'Certificate', 'status'], 'FinalPNPCertificate must record accepted status', {
      status: cert.status,
      verdict: cert.verdict,
    });
  }

  if (cert.checker !== 'CheckPCCPackexp0' || cert.generator !== 'GeneratePCCPack') {
    return validationReject0(['FinalPNPCertificateEnvelope', 'Certificate'], 'FinalPNPCertificate must bind CheckPCCPackexp0 and GeneratePCCPack', {
      checker: cert.checker,
      generator: cert.generator,
    });
  }

  if (!samePublicTheorem0(cert.theorem)) {
    return validationReject0(['FinalPNPCertificateEnvelope', 'Certificate', 'theorem'], 'FinalPNPReleaseGate theorem mismatch', {
      actual: cert.theorem,
    });
  }

  if (
    cert.publicConclusionAntecedent !== 'CheckPCCPackexp(GeneratePCCPack())=accept' ||
    cert.publicConclusionConsequent !== 'P = NP' ||
    cert.publicConclusionConditional !== true
  ) {
    return validationReject0(['FinalPNPCertificateEnvelope', 'Certificate', 'publicConclusion'], 'FinalPNPReleaseGate public conclusion mismatch', {
      antecedent: cert.publicConclusionAntecedent,
      consequent: cert.publicConclusionConsequent,
      conditional: cert.publicConclusionConditional,
    });
  }

  if (!sameDigestHex0(cert.releaseAuditDigest, digestFromRecord0(releaseAuditRecord))) {
    return validationReject0(['FinalPNPCertificateEnvelope', 'Certificate', 'releaseAuditDigest'], 'FinalPNPCertificate release-audit digest must match materialized ReleaseAuditRecord', {
      expected: digestFromRecord0(releaseAuditRecord),
      actual: cert.releaseAuditDigest,
    });
  }

  if (!sameDigestHex0(certNF.certificateDigest, digestCanonical0(cert))) {
    return validationReject0(['CheckFinalPNPCertificateRecord', 'NF', 'certificateDigest'], 'CheckFinalPNPCertificate0 certificate digest must match certificate bytes', {
      expected: digestCanonical0(cert),
      actual: certNF.certificateDigest,
    });
  }

  return validationAccept0({
    kind: 'FinalPNPReleaseGateContract0NF',
    finalPNPCertificateAccepted: true,
    releaseAuditAccepted: releaseAuditRecord.tag === 'accept',
    theorem: cert.theorem,
    releaseAuditDigest: cert.releaseAuditDigest,
    certificateDigest: digestCanonical0(cert),
  });
}

function makeLinkage0({
  finalPNPCertificateEnvelope,
  checkFinalPNPCertificateRecord,
  releaseAuditRecord,
}) {
  const cert = finalPNPCertificateEnvelope?.Certificate ?? {};

  return {
    kind: 'FinalPNPReleaseGateLinkage0',
    version: CHECKER_VERSION,
    finalPNPCertificateEnvelopeDigest: digestCanonical0(finalPNPCertificateEnvelope),
    checkFinalPNPCertificateRecordDigest: digestFromRecord0(checkFinalPNPCertificateRecord),
    releaseAuditRecordDigest: digestFromRecord0(releaseAuditRecord),
    certificateDigest: digestCanonical0(cert),
    acceptRunDigest: cert.acceptRunDigest ?? null,
    pccPackDigest: cert.pccPackDigest ?? null,
    finalVerdictRecordDigest: cert.finalVerdictRecordDigest ?? null,
    checkPCCPackexpRecordDigest: cert.checkPCCPackexpRecordDigest ?? null,
  };
}

function validateLinkage0(envelope, finalPNPCertificateRecord) {
  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'FinalPNPReleaseGate0 Linkage must be an object', {
      actual: typeof envelope.Linkage,
    });
  }

  const expected = makeLinkage0({
    finalPNPCertificateEnvelope: envelope.FinalPNPCertificateEnvelope,
    checkFinalPNPCertificateRecord: finalPNPCertificateRecord,
    releaseAuditRecord: envelope.ReleaseAuditRecord,
  });

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (field === 'kind' || field === 'version') {
      continue;
    }

    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `FinalPNPReleaseGate0 linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'FinalPNPReleaseGateLinkage0NF',
    ...expected,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['FinalPNPReleaseGate0'], 'FinalPNPReleaseGate0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['FinalPNPReleaseGate0'], 'FinalPNPReleaseGate0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'FinalPNPReleaseGateJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function resolveReleaseAuditRecord0(finalPNPCertificateEnvelope) {
  return finalPNPCertificateEnvelope
    ?.ConcreteFinalAcceptanceReplayEnvelope
    ?.ConcreteReleaseAppendixEnvelope
    ?.ReleaseAuditConcreteFinalCertificateGateEnvelope
    ?.ReleaseAuditRecord ?? null;
}

function samePublicTheorem0(value) {
  return (
    isPlainObject(value) &&
    value.statement === 'P = NP' &&
    value.antecedent === 'CheckPCCPackexp(GeneratePCCPack())=accept' &&
    value.consequent === 'P = NP' &&
    value.conditional === true
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

function recordNF0(record) {
  return isPlainObject(record)
    ? record.NF ?? record.nf ?? {}
    : {};
}

function digestFromRecord0(record) {
  if (!isPlainObject(record)) {
    return null;
  }

  return record.Digest ?? record.digest ?? (
    isPlainObject(record.NF ?? record.nf)
      ? digestCanonical0(record.NF ?? record.nf)
      : digestCanonical0(record)
  );
}

function compactReject0(record) {
  if (!isRejectRecord0(record)) {
    return null;
  }

  return {
    checker: record.checker,
    coord: record.Coord ?? record.coord,
    path: record.Path ?? record.path,
    witness: record.Witness ?? record.witness,
    digest: record.Digest ?? record.digest,
  };
}

function isRejectRecord0(value) {
  return classifyRecord0(value) === 'reject';
}

function classifyRecord0(value) {
  if (!isPlainObject(value)) {
    return 'unknown';
  }

  if (value.tag === 'reject' || value.kind === 'reject') {
    return 'reject';
  }

  if (value.tag === 'accept' || value.kind === 'accept') {
    return 'accept';
  }

  return 'unknown';
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

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}

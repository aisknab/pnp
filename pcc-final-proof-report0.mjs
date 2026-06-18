import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckFinalPNPReleaseGate0,
  makeFinalPNPReleaseGate0,
} from './pcc-final-pnp-release-gate0.mjs';

const CHECKER_VERSION = 0;

export const FINAL_PNP_PROOF_REPORT_PHASES0 = Object.freeze([
  'CheckFinalPNPProofReportInput0',
  'CheckFinalPNPReleaseGate0',
  'CheckFinalPNPProofReportRecord0',
  'CheckFinalPNPProofReportContract0',
  'CheckFinalPNPProofReportJson0',
  'CheckFinalPNPProofReportLinkage0',
  'EmitFinalPNPProofReport0',
]);

export function makeFinalPNPProofReportConfig0(overrides = {}) {
  return {
    kind: 'FinalPNPProofReportConfig0',
    version: CHECKER_VERSION,
    checkFinalPNPReleaseGate: true,
    checkReport: true,
    checkContract: true,
    checkJsonMaterialized: true,
    checkLinkage: true,
    finalPNPReleaseGateConfig: {},
    ...overrides,
  };
}

export async function makeFinalPNPProofReport0({
  FinalPNPReleaseGateEnvelope = null,
  Report = null,
  overrides = {},
} = {}) {
  const finalPNPReleaseGateEnvelope =
    FinalPNPReleaseGateEnvelope ?? await makeFinalPNPReleaseGate0();

  const releaseGateRecord =
    await CheckFinalPNPReleaseGate0(finalPNPReleaseGateEnvelope);

  const report = Report ?? makeFinalPNPProofReportRecord0({
    finalPNPReleaseGateEnvelope,
    finalPNPReleaseGateRecord: releaseGateRecord,
  });

  const linkage = makeLinkage0({
    finalPNPReleaseGateEnvelope,
    finalPNPReleaseGateRecord: releaseGateRecord,
    report,
  });

  return {
    kind: 'FinalPNPProofReport0',
    version: CHECKER_VERSION,
    FinalPNPReleaseGateEnvelope: finalPNPReleaseGateEnvelope,
    CheckFinalPNPReleaseGateRecord: releaseGateRecord,
    Report: report,
    Linkage: linkage,
    PiFinalPNPProofReport: {
      kind: 'PiFinalPNPProofReport0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'FinalPNPReleaseGateEnvelope',
          digest: linkage.finalPNPReleaseGateEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'CheckFinalPNPReleaseGateRecord',
          digest: linkage.finalPNPReleaseGateRecordDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'FinalPNPProofReportRecord',
          digest: linkage.reportDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function makeFinalPNPProofReportRecord0({
  finalPNPReleaseGateEnvelope,
  finalPNPReleaseGateRecord,
}) {
  const gateNF = recordNF0(finalPNPReleaseGateRecord);
  const certificate =
    finalPNPReleaseGateEnvelope?.FinalPNPCertificateEnvelope?.Certificate ?? null;

  return {
    kind: 'FinalPNPProofReportRecord0',
    version: CHECKER_VERSION,

    status: 'accepted',
    theorem: {
      statement: 'P = NP',
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
      conditional: true,
    },
    claimBoundary: 'accepted-final-pnp-release-gate',
    noClaimBeforeAccept: true,

    finalPNPReleaseGateAccepted: gateNF.finalPNPReleaseGateAccepted === true,
    finalPNPCertificateAccepted: gateNF.finalPNPCertificateAccepted === true,
    releaseAuditAccepted: gateNF.releaseAuditAccepted === true,
    finalAcceptanceReplayClosed: gateNF.finalAcceptanceReplayClosed === true,

    statusFromGate: gateNF.status ?? null,
    verdict: gateNF.verdict ?? null,
    generator: gateNF.generator ?? null,
    checkerName: gateNF.checkerName ?? null,
    generatorIsGeneratePCCPack: gateNF.generatorIsGeneratePCCPack === true,
    checkPCCPackexpAccepted: gateNF.checkPCCPackexpAccepted === true,
    checkAcceptRunAccepted: gateNF.checkAcceptRunAccepted === true,
    replayAccepted: gateNF.replayAccepted === true,
    finalVerdictAccepted: gateNF.finalVerdictAccepted === true,

    publicConclusionEmitted: gateNF.publicConclusionEmitted === true,
    publicConclusionAntecedent: gateNF.publicConclusionAntecedent ?? null,
    publicConclusionConsequent: gateNF.publicConclusionConsequent ?? null,
    publicConclusionConditional: gateNF.publicConclusionConditional === true,

    checkPCCPackexpGeneratedPackageImplication:
      gateNF.checkPCCPackexpGeneratedPackageImplication === true,
    checkPCCPackexpConcreteCoverageComplete:
      gateNF.checkPCCPackexpConcreteCoverageComplete === true,
    checkPCCPackexpPCCPackLinkageComplete:
      gateNF.checkPCCPackexpPCCPackLinkageComplete === true,

    finalPNPReleaseGateEnvelopeDigest:
      digestCanonical0(finalPNPReleaseGateEnvelope),
    finalPNPReleaseGateRecordDigest:
      digestFromRecord0(finalPNPReleaseGateRecord),

    releaseAuditDigest:
      gateNF.releaseAuditDigest ?? certificate?.releaseAuditDigest ?? null,
    certificateDigest:
      gateNF.certificateDigest ?? digestCanonical0(certificate),
    finalPNPCertificateEnvelopeDigest:
      gateNF.finalPNPCertificateEnvelopeDigest ??
      digestCanonical0(finalPNPReleaseGateEnvelope?.FinalPNPCertificateEnvelope ?? null),
    checkFinalPNPCertificateRecordDigest:
      gateNF.checkFinalPNPCertificateRecordDigest ??
      digestFromRecord0(finalPNPReleaseGateEnvelope?.CheckFinalPNPCertificateRecord),

    acceptRunDigest: gateNF.acceptRunDigest ?? certificate?.acceptRunDigest ?? null,
    pccPackDigest: gateNF.pccPackDigest ?? certificate?.pccPackDigest ?? null,
    acceptanceTranscriptDigest:
      gateNF.acceptanceTranscriptDigest ?? certificate?.acceptanceTranscriptDigest ?? null,
    finalVerdictRecordDigest:
      gateNF.finalVerdictRecordDigest ?? certificate?.finalVerdictRecordDigest ?? null,
    checkPCCPackexpRecordDigest:
      gateNF.checkPCCPackexpRecordDigest ?? certificate?.checkPCCPackexpRecordDigest ?? null,

    publicTheoremStatement: 'P = NP',
    publicConclusionStatement:
      'CheckPCCPackexp(GeneratePCCPack())=accept => P = NP',
  };
}

export async function CheckFinalPNPProofReport0(
  input,
  config = makeFinalPNPProofReportConfig0(),
) {
  const checker = 'CheckFinalPNPProofReport0';
  const ledger = [];
  const cfg = makeFinalPNPProofReportConfig0(config);
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
    phase: 'CheckFinalPNPProofReportInput0',
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

  let releaseGateRecord = envelope.CheckFinalPNPReleaseGateRecord;

  if (cfg.checkFinalPNPReleaseGate === true) {
    const fresh = await CheckFinalPNPReleaseGate0(
      envelope.FinalPNPReleaseGateEnvelope,
      cfg.finalPNPReleaseGateConfig ?? {},
    );

    const result = recordToValidation0(fresh, ['FinalPNPReleaseGateEnvelope']);

    ledger.push({
      phase: 'CheckFinalPNPReleaseGate0',
      status: result.ok ? 'pass' : 'fail',
      digest: fresh.Digest ?? fresh.digest ?? digestCanonical0(fresh),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.FinalPNPReleaseGate`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    const materialized = validateMaterializedRecord0(
      envelope.CheckFinalPNPReleaseGateRecord,
      fresh,
      ['CheckFinalPNPReleaseGateRecord'],
      'CheckFinalPNPReleaseGateRecord',
    );

    ledger.push({
      phase: 'CheckFinalPNPReleaseGateRecord',
      status: materialized.ok ? 'pass' : 'fail',
      digest: digestCanonical0(materialized.nf ?? materialized.witness ?? null),
    });

    if (!materialized.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckFinalPNPReleaseGateRecord`,
        path: materialized.path,
        witness: materialized.witness,
        ledger,
      });
    }

    releaseGateRecord = envelope.CheckFinalPNPReleaseGateRecord;
  }

  if (cfg.checkReport === true) {
    const expected = makeFinalPNPProofReportRecord0({
      finalPNPReleaseGateEnvelope: envelope.FinalPNPReleaseGateEnvelope,
      finalPNPReleaseGateRecord: releaseGateRecord,
    });

    const report = validateReportRecord0(envelope.Report, expected);

    ledger.push({
      phase: 'CheckFinalPNPProofReportRecord0',
      status: report.ok ? 'pass' : 'fail',
      digest: digestCanonical0(report.nf ?? report.witness ?? null),
    });

    if (!report.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.report`,
        path: report.path,
        witness: report.witness,
        ledger,
      });
    }
  }

  const contract = validateFinalPNPProofReportContract0(envelope.Report, releaseGateRecord);

  if (cfg.checkContract === true) {
    ledger.push({
      phase: 'CheckFinalPNPProofReportContract0',
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
      phase: 'CheckFinalPNPProofReportJson0',
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
    const linkage = validateLinkage0(envelope, releaseGateRecord);

    ledger.push({
      phase: 'CheckFinalPNPProofReportLinkage0',
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

  const report = envelope.Report;

  const nf = {
    kind: 'FinalPNPProofReport0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: FINAL_PNP_PROOF_REPORT_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,

    finalPNPProofReportAccepted: true,
    status: report.status,
    theorem: report.theorem,
    claimBoundary: report.claimBoundary,
    noClaimBeforeAccept: report.noClaimBeforeAccept,

    finalPNPReleaseGateAccepted: report.finalPNPReleaseGateAccepted,
    finalPNPCertificateAccepted: report.finalPNPCertificateAccepted,
    releaseAuditAccepted: report.releaseAuditAccepted,
    finalAcceptanceReplayClosed: report.finalAcceptanceReplayClosed,

    verdict: report.verdict,
    generator: report.generator,
    checkerName: report.checkerName,
    generatorIsGeneratePCCPack: report.generatorIsGeneratePCCPack,
    checkPCCPackexpAccepted: report.checkPCCPackexpAccepted,
    checkAcceptRunAccepted: report.checkAcceptRunAccepted,
    replayAccepted: report.replayAccepted,
    finalVerdictAccepted: report.finalVerdictAccepted,

    publicConclusionEmitted: report.publicConclusionEmitted,
    publicConclusionAntecedent: report.publicConclusionAntecedent,
    publicConclusionConsequent: report.publicConclusionConsequent,
    publicConclusionConditional: report.publicConclusionConditional,

    checkPCCPackexpGeneratedPackageImplication:
      report.checkPCCPackexpGeneratedPackageImplication,
    checkPCCPackexpConcreteCoverageComplete:
      report.checkPCCPackexpConcreteCoverageComplete,
    checkPCCPackexpPCCPackLinkageComplete:
      report.checkPCCPackexpPCCPackLinkageComplete,

    finalPNPReleaseGateEnvelopeDigest:
      report.finalPNPReleaseGateEnvelopeDigest,
    finalPNPReleaseGateRecordDigest:
      report.finalPNPReleaseGateRecordDigest,
    releaseAuditDigest: report.releaseAuditDigest,
    certificateDigest: report.certificateDigest,
    acceptRunDigest: report.acceptRunDigest,
    pccPackDigest: report.pccPackDigest,
    acceptanceTranscriptDigest: report.acceptanceTranscriptDigest,
    finalVerdictRecordDigest: report.finalVerdictRecordDigest,
    checkPCCPackexpRecordDigest: report.checkPCCPackexpRecordDigest,

    publicTheoremStatement: report.publicTheoremStatement,
    publicConclusionStatement: report.publicConclusionStatement,
    reportDigest: digestCanonical0(report),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeFinalPNPProofReportFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeFinalPNPProofReportFiles0 requires a non-empty output directory');
  }

  const envelope = await makeFinalPNPProofReport0(options);
  const checked = await CheckFinalPNPProofReport0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'FinalPNPProofReport0.json');
  const reportPath = path.join(outDir, 'FinalPNPProofReportRecord0.json');
  const releaseGatePath = path.join(outDir, 'FinalPNPReleaseGate0.json');
  const releaseGateCheckPath = path.join(outDir, 'FinalPNPReleaseGate0.check.json');
  const certificatePath = path.join(outDir, 'FinalPNPCertificateRecord0.json');
  const checkPath = path.join(outDir, 'FinalPNPProofReport0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(reportPath, envelope.Report);
  await writeJsonFile0(releaseGatePath, envelope.FinalPNPReleaseGateEnvelope);
  await writeJsonFile0(releaseGateCheckPath, envelope.CheckFinalPNPReleaseGateRecord);
  await writeJsonFile0(certificatePath, envelope.FinalPNPReleaseGateEnvelope.FinalPNPCertificateEnvelope.Certificate);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      reportPath,
      releaseGatePath,
      releaseGateCheckPath,
      certificatePath,
      checkPath,
    },
  };
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'FinalPNPProofReportConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'FinalPNPProofReportConfig0') {
    return validationReject0(['kind'], 'FinalPNPProofReportConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalPNPProofReportConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkFinalPNPReleaseGate',
    'checkReport',
    'checkContract',
    'checkJsonMaterialized',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `FinalPNPProofReportConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.finalPNPReleaseGateConfig)) {
    return validationReject0(['finalPNPReleaseGateConfig'], 'finalPNPReleaseGateConfig must be an object', {
      actual: typeof config.finalPNPReleaseGateConfig,
    });
  }

  return validationAccept0({
    kind: 'FinalPNPProofReportConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'FinalPNPProofReport0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'FinalPNPProofReport0') {
    return validationReject0(['kind'], 'FinalPNPProofReport0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalPNPProofReport0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.FinalPNPReleaseGateEnvelope)) {
    return validationReject0(['FinalPNPReleaseGateEnvelope'], 'FinalPNPProofReport0 must include FinalPNPReleaseGateEnvelope', {
      actual: typeof envelope.FinalPNPReleaseGateEnvelope,
    });
  }

  if (!isPlainObject(envelope.CheckFinalPNPReleaseGateRecord)) {
    return validationReject0(['CheckFinalPNPReleaseGateRecord'], 'FinalPNPProofReport0 must include CheckFinalPNPReleaseGateRecord', {
      actual: typeof envelope.CheckFinalPNPReleaseGateRecord,
    });
  }

  if (!isPlainObject(envelope.Report)) {
    return validationReject0(['Report'], 'FinalPNPProofReport0 must include Report', {
      actual: typeof envelope.Report,
    });
  }

  return validationAccept0({
    kind: 'FinalPNPProofReportShape0NF',
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

function validateReportRecord0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['Report'], 'FinalPNPProofReport record must match recomputed report summary', {
      expectedDigest: digestCanonical0(expected),
      actualDigest: digestCanonical0(actual),
    });
  }

  return validationAccept0({
    kind: 'FinalPNPProofReportRecord0NF',
    reportDigest: digestCanonical0(actual),
  });
}

function validateFinalPNPProofReportContract0(report, releaseGateRecord) {
  if (!isPlainObject(report)) {
    return validationReject0(['Report'], 'FinalPNPProofReport record must be an object', {
      actual: typeof report,
    });
  }

  const gateNF = recordNF0(releaseGateRecord);

  const requiredTrue = [
    'noClaimBeforeAccept',
    'finalPNPReleaseGateAccepted',
    'finalPNPCertificateAccepted',
    'releaseAuditAccepted',
    'finalAcceptanceReplayClosed',
    'generatorIsGeneratePCCPack',
    'checkPCCPackexpAccepted',
    'checkAcceptRunAccepted',
    'replayAccepted',
    'finalVerdictAccepted',
    'publicConclusionEmitted',
    'publicConclusionConditional',
    'checkPCCPackexpGeneratedPackageImplication',
    'checkPCCPackexpConcreteCoverageComplete',
    'checkPCCPackexpPCCPackLinkageComplete',
  ];

  for (const field of requiredTrue) {
    if (report[field] !== true) {
      return validationReject0(['Report', field], `FinalPNPProofReport must certify ${field}`, {
        actual: report[field],
      });
    }
  }

  if (releaseGateRecord.tag !== 'accept') {
    return validationReject0(['CheckFinalPNPReleaseGateRecord', 'tag'], 'FinalPNPProofReport requires accepted release gate', {
      actual: releaseGateRecord.tag,
    });
  }

  if (report.status !== 'accepted' || report.verdict !== 'accept') {
    return validationReject0(['Report', 'status'], 'FinalPNPProofReport must record accepted status and verdict', {
      status: report.status,
      verdict: report.verdict,
    });
  }

  if (report.generator !== 'GeneratePCCPack' || report.checkerName !== 'CheckPCCPackexp0') {
    return validationReject0(['Report'], 'FinalPNPProofReport must bind GeneratePCCPack and CheckPCCPackexp0', {
      generator: report.generator,
      checkerName: report.checkerName,
    });
  }

  if (!samePublicTheorem0(report.theorem)) {
    return validationReject0(['Report', 'theorem'], 'FinalPNPProofReport theorem mismatch', {
      actual: report.theorem,
    });
  }

  if (
    report.publicConclusionAntecedent !== 'CheckPCCPackexp(GeneratePCCPack())=accept' ||
    report.publicConclusionConsequent !== 'P = NP' ||
    report.publicConclusionStatement !== 'CheckPCCPackexp(GeneratePCCPack())=accept => P = NP'
  ) {
    return validationReject0(['Report', 'publicConclusion'], 'FinalPNPProofReport public conclusion mismatch', {
      antecedent: report.publicConclusionAntecedent,
      consequent: report.publicConclusionConsequent,
      statement: report.publicConclusionStatement,
    });
  }

  if (!sameDigestHex0(report.finalPNPReleaseGateRecordDigest, digestFromRecord0(releaseGateRecord))) {
    return validationReject0(['Report', 'finalPNPReleaseGateRecordDigest'], 'FinalPNPProofReport release-gate record digest mismatch', {
      expected: digestFromRecord0(releaseGateRecord),
      actual: report.finalPNPReleaseGateRecordDigest,
    });
  }

  if (!sameDigestHex0(report.certificateDigest, gateNF.certificateDigest)) {
    return validationReject0(['Report', 'certificateDigest'], 'FinalPNPProofReport certificate digest must match release-gate NF', {
      expected: gateNF.certificateDigest,
      actual: report.certificateDigest,
    });
  }

  return validationAccept0({
    kind: 'FinalPNPProofReportContract0NF',
    finalPNPProofReportAccepted: true,
    reportDigest: digestCanonical0(report),
  });
}

function makeLinkage0({
  finalPNPReleaseGateEnvelope,
  finalPNPReleaseGateRecord,
  report,
}) {
  return {
    kind: 'FinalPNPProofReportLinkage0',
    version: CHECKER_VERSION,
    finalPNPReleaseGateEnvelopeDigest:
      digestCanonical0(finalPNPReleaseGateEnvelope),
    finalPNPReleaseGateRecordDigest:
      digestFromRecord0(finalPNPReleaseGateRecord),
    reportDigest:
      digestCanonical0(report),
    releaseAuditDigest:
      report.releaseAuditDigest ?? null,
    certificateDigest:
      report.certificateDigest ?? null,
    acceptRunDigest:
      report.acceptRunDigest ?? null,
    pccPackDigest:
      report.pccPackDigest ?? null,
    finalVerdictRecordDigest:
      report.finalVerdictRecordDigest ?? null,
    checkPCCPackexpRecordDigest:
      report.checkPCCPackexpRecordDigest ?? null,
  };
}

function validateLinkage0(envelope, releaseGateRecord) {
  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'FinalPNPProofReport0 Linkage must be an object', {
      actual: typeof envelope.Linkage,
    });
  }

  const expected = makeLinkage0({
    finalPNPReleaseGateEnvelope: envelope.FinalPNPReleaseGateEnvelope,
    finalPNPReleaseGateRecord: releaseGateRecord,
    report: envelope.Report,
  });

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (field === 'kind' || field === 'version') {
      continue;
    }

    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `FinalPNPProofReport0 linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'FinalPNPProofReportLinkage0NF',
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
    return validationReject0(['FinalPNPProofReport0'], 'FinalPNPProofReport0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['FinalPNPProofReport0'], 'FinalPNPProofReport0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'FinalPNPProofReportJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
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

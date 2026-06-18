
import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckConcreteMaterializedPCCPack0,
  summarizeConcretePCCPackCoverage0,
} from './pcc-pack-concrete-materialized0.mjs';

const CHECKER_VERSION = 0;

export const CHECK_PCC_PACK_EXP_REQUIRED_COVERAGE_FIELDS0 = Object.freeze([
  'publicConclusionOnlyAfterAcceptRun',

  'concreteKBundle',
  'kBundleKernelRuleCoverageComplete',
  'kBundleSigmaProofRefsResolve',
  'kBundleReflectionProofRefsResolve',
  'kBundleNoOpaqueProofRefs',
  'kBundleNoExecutableMinSymbols',

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

  'concreteRows',
  'concreteLocalPackages',
  'concreteGlobalFirewalls',
  'concreteGlobalProofDAG',

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
  'globalProofDAGHasGThresholdProofNode',
  'globalProofDAGPackageGDependsOnGThresholdProof',
  'globalProofDAGFinalSATinPDependsOnPackageG',
  'finalIntegrationGlobalGLinkageComplete',
  'finalTheoremGLinkageComplete',
  'finalTheoremUsesGlobalGThreshold',
  'finalTheoremUsesGThresholdProofRef',
  'finalTheoremUsesFinalIntegrationGlobalGLinkage',

  'pccPackLinkedToKBundle',
  'pccPackLinkedToHardCheck',
  'pccPackLinkedToRows',
  'pccPackLinkedToLocalPackages',
  'pccPackLinkedToGlobalFirewalls',
  'pccPackLinkedToGlobalProofDAG',
  'pccPackLinkedToGPack',
  'pccPackLinkedToFinalIntegration',
  'pccPackLinkedToFinalTheorem',
]);

export function makeCheckPCCPackexpConfig0(overrides = {}) {
  return {
    kind: 'CheckPCCPackexpConfig0',
    version: CHECKER_VERSION,
    checkConcreteMaterializedPCCPack: true,
    checkConcreteCoverage: true,
    checkPublicClaimBoundary: true,
    checkJsonMaterialized: true,
    checkRecordAlignment: true,
    concretePCCPackConfig: {},
    ...overrides,
  };
}

export async function CheckPCCPackexp0(
  input,
  config = makeCheckPCCPackexpConfig0(),
) {
  const checker = 'CheckPCCPackexp0';
  const ledger = [];
  const cfg = makeCheckPCCPackexpConfig0(config);
  let concreteRecord = null;

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

  const shape = validateShape0(input);

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

  if (cfg.checkConcreteMaterializedPCCPack === true) {
    concreteRecord = await CheckConcreteMaterializedPCCPack0(
      input,
      cfg.concretePCCPackConfig ?? {},
    );

    const result = recordToValidation0(concreteRecord, ['PCCPack']);

    ledger.push({
      phase: 'CheckConcreteMaterializedPCCPack0',
      status: result.ok ? 'pass' : 'fail',
      digest: concreteRecord.Digest ?? concreteRecord.digest ?? digestCanonical0(concreteRecord),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcretePCCPack`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const materializedPCCPack = resolveMaterializedPCCPack0(input);
  const pccPack = resolvePCCPack0(materializedPCCPack);
  const coverage = summarizeConcretePCCPackCoverage0(materializedPCCPack);

  if (cfg.checkConcreteCoverage === true) {
    const coverageCheck = validateConcreteCoverage0(coverage);

    ledger.push({
      phase: 'concreteCoverage',
      status: coverageCheck.ok ? 'pass' : 'fail',
      digest: digestCanonical0(coverageCheck.nf ?? coverageCheck.witness ?? null),
    });

    if (!coverageCheck.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.concreteCoverage`,
        path: coverageCheck.path,
        witness: coverageCheck.witness,
        ledger,
      });
    }
  }

  if (cfg.checkPublicClaimBoundary === true) {
    const claim = validatePublicClaimBoundary0(coverage, pccPack);

    ledger.push({
      phase: 'publicClaimBoundary',
      status: claim.ok ? 'pass' : 'fail',
      digest: digestCanonical0(claim.nf ?? claim.witness ?? null),
    });

    if (!claim.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.publicClaimBoundary`,
        path: claim.path,
        witness: claim.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(input);

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

  if (cfg.checkRecordAlignment === true && concreteRecord !== null) {
    const alignment = validateConcreteRecordAlignment0({
      concreteRecord,
      materializedPCCPack,
      pccPack,
      coverage,
    });

    ledger.push({
      phase: 'recordAlignment',
      status: alignment.ok ? 'pass' : 'fail',
      digest: digestCanonical0(alignment.nf ?? alignment.witness ?? null),
    });

    if (!alignment.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.recordAlignment`,
        path: alignment.path,
        witness: alignment.witness,
        ledger,
      });
    }
  }

  const concreteRecordNF = concreteRecord?.NF ?? concreteRecord?.nf ?? null;
  const claimBoundary = makeClaimBoundary0();

  const nf = {
    kind: 'CheckPCCPackexp0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,

    checkPCCPackexp: true,
    packageKind: coverage.pccPackKind,
    materializedPCCPackKind: materializedPCCPack.kind ?? null,

    pccPackDigest: digestCanonical0(pccPack),
    materializedPCCPackDigest: digestCanonical0(materializedPCCPack),
    concretePCCPackRecordDigest: concreteRecord?.Digest ?? concreteRecord?.digest ?? null,
    concreteCoverageDigest: digestCanonical0(coverage),

    publicConclusionOnlyAfterAcceptRun: coverage.publicConclusionOnlyAfterAcceptRun === true,
    publicConclusionEmitted: false,
    claimBoundary,
    publicConclusion: claimBoundary,

    concretePCCPack: true,
    concreteKBundle: coverage.concreteKBundle,
    kBundleKernelRuleCoverageComplete: coverage.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: coverage.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: coverage.kBundleReflectionProofRefsResolve,
    kBundleNoOpaqueProofRefs: coverage.kBundleNoOpaqueProofRefs,
    kBundleNoExecutableMinSymbols: coverage.kBundleNoExecutableMinSymbols,

    concreteHardCheck: coverage.concreteHardCheck,
    hardCheckerCoverageComplete: coverage.hardCheckerCoverageComplete,
    hardRowKeyCoverageComplete: coverage.hardRowKeyCoverageComplete,
    hardRoutePriorityComplete: coverage.hardRoutePriorityComplete,
    hardProofRefPolicyComplete: coverage.hardProofRefPolicyComplete,
    hardHashDisciplineComplete: coverage.hardHashDisciplineComplete,
    hardNoMinCoverageComplete: coverage.hardNoMinCoverageComplete,
    hardImportPolicyComplete: coverage.hardImportPolicyComplete,
    hardReflectionPolicyComplete: coverage.hardReflectionPolicyComplete,
    hardBoundsPolicyComplete: coverage.hardBoundsPolicyComplete,
    hardDiagnosticsPolicyComplete: coverage.hardDiagnosticsPolicyComplete,

    concreteRows: coverage.concreteRows,
    concreteLocalPackages: coverage.concreteLocalPackages,
    concreteGlobalFirewalls: coverage.concreteGlobalFirewalls,
    concreteGlobalProofDAG: coverage.concreteGlobalProofDAG,

    concreteFinalIntegration: coverage.concreteFinalIntegration,
    finalIntegrationConcreteGlobalProofDAG: coverage.finalIntegrationConcreteGlobalProofDAG,
    finalIntegrationGPackFieldCoverageComplete: coverage.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: coverage.finalIntegrationRowFamGCoverageComplete,
    finalIntegrationUsesGPack: coverage.finalIntegrationUsesGPack,
    rowFamGUsesGPack: coverage.rowFamGUsesGPack,
    finalTheoremUsesFinalIntegration: coverage.finalTheoremUsesFinalIntegration,
    rowFamFinalUsesFinalTheorem: coverage.rowFamFinalUsesFinalTheorem,
    finalMatchUsesGPack: coverage.finalMatchUsesGPack,
    satDecisionUsesGPack: coverage.satDecisionUsesGPack,
    globalProofDAGHasGThresholdProofNode: coverage.globalProofDAGHasGThresholdProofNode,
    globalProofDAGPackageGDependsOnGThresholdProof: coverage.globalProofDAGPackageGDependsOnGThresholdProof,
    globalProofDAGFinalSATinPDependsOnPackageG: coverage.globalProofDAGFinalSATinPDependsOnPackageG,
    finalIntegrationGlobalGLinkageComplete: coverage.finalIntegrationGlobalGLinkageComplete,
    finalTheoremGLinkageComplete: coverage.finalTheoremGLinkageComplete,
    finalTheoremUsesGlobalGThreshold: coverage.finalTheoremUsesGlobalGThreshold,
    finalTheoremUsesGThresholdProofRef: coverage.finalTheoremUsesGThresholdProofRef,
    finalTheoremUsesFinalIntegrationGlobalGLinkage: coverage.finalTheoremUsesFinalIntegrationGlobalGLinkage,

    pccPackLinkedToKBundle: coverage.pccPackLinkedToKBundle,
    pccPackLinkedToHardCheck: coverage.pccPackLinkedToHardCheck,
    pccPackLinkedToRows: coverage.pccPackLinkedToRows,
    pccPackLinkedToLocalPackages: coverage.pccPackLinkedToLocalPackages,
    pccPackLinkedToGlobalFirewalls: coverage.pccPackLinkedToGlobalFirewalls,
    pccPackLinkedToGlobalProofDAG: coverage.pccPackLinkedToGlobalProofDAG,
    pccPackLinkedToGPack: coverage.pccPackLinkedToGPack,
    pccPackLinkedToFinalIntegration: coverage.pccPackLinkedToFinalIntegration,
    pccPackLinkedToFinalTheorem: coverage.pccPackLinkedToFinalTheorem,

    concretePCCPackRecordKind: concreteRecordNF?.kind ?? null,
    concretePCCPackRecordAccepted: concreteRecord === null ? null : concreteRecord.tag === 'accept',
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'CheckPCCPackexpConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'CheckPCCPackexpConfig0') {
    return validationReject0(['kind'], 'CheckPCCPackexpConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `CheckPCCPackexpConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkConcreteMaterializedPCCPack',
    'checkConcreteCoverage',
    'checkPublicClaimBoundary',
    'checkJsonMaterialized',
    'checkRecordAlignment',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `CheckPCCPackexpConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.concretePCCPackConfig)) {
    return validationReject0(['concretePCCPackConfig'], 'concretePCCPackConfig must be an object', {
      actual: typeof config.concretePCCPackConfig,
    });
  }

  return validationAccept0({
    kind: 'CheckPCCPackexpConfig0NF',
  });
}

function validateShape0(input) {
  if (!isPlainObject(input)) {
    return validationReject0([], 'CheckPCCPackexp0 input must be an object', {
      actual: typeof input,
    });
  }

  const materializedPCCPack = resolveMaterializedPCCPack0(input);

  if (!isPlainObject(materializedPCCPack)) {
    return validationReject0(['MaterializedPCCPackEnvelope'], 'CheckPCCPackexp0 input must expose a materialized PCC pack', {
      actual: typeof materializedPCCPack,
    });
  }

  const pccPack = resolvePCCPack0(materializedPCCPack);

  if (!isPlainObject(pccPack)) {
    return validationReject0(['PCCPack'], 'CheckPCCPackexp0 input must expose PCCPack0', {
      actual: typeof pccPack,
    });
  }

  if (pccPack.kind !== 'PCCPack0') {
    return validationReject0(['PCCPack', 'kind'], 'CheckPCCPackexp0 requires PCCPack0', {
      actual: pccPack.kind,
    });
  }

  return validationAccept0({
    kind: 'CheckPCCPackexpShape0NF',
    materializedPCCPackKind: materializedPCCPack.kind ?? null,
    pccPackKind: pccPack.kind,
  });
}

function validateConcreteCoverage0(coverage) {
  if (!isPlainObject(coverage)) {
    return validationReject0(['ConcreteCoverage'], 'concrete PCCPack coverage must be an object', {
      actual: typeof coverage,
    });
  }

  if (coverage.pccPackKind !== 'PCCPack0') {
    return validationReject0(['ConcreteCoverage', 'pccPackKind'], 'concrete coverage must target PCCPack0', {
      actual: coverage.pccPackKind,
    });
  }

  for (const field of CHECK_PCC_PACK_EXP_REQUIRED_COVERAGE_FIELDS0) {
    if (coverage[field] !== true) {
      return validationReject0(['ConcreteCoverage', field], `CheckPCCPackexp0 requires concrete coverage field ${field}`, {
        actual: coverage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'CheckPCCPackexpConcreteCoverage0NF',
    concreteCoverageDigest: digestCanonical0(coverage),
  });
}

function validatePublicClaimBoundary0(coverage, pccPack) {
  if (coverage.publicConclusionOnlyAfterAcceptRun !== true) {
    return validationReject0(['ConcreteCoverage', 'publicConclusionOnlyAfterAcceptRun'], 'PCCPack public conclusion must be gated by accepted replay', {
      actual: coverage.publicConclusionOnlyAfterAcceptRun,
    });
  }

  if (pccPack?.Manifest?.publicConclusionOnlyAfterAcceptRun !== true) {
    return validationReject0(['PCCPack', 'Manifest', 'publicConclusionOnlyAfterAcceptRun'], 'PCCPack manifest must gate public conclusion by accepted replay', {
      actual: pccPack?.Manifest?.publicConclusionOnlyAfterAcceptRun,
    });
  }

  return validationAccept0({
    kind: 'CheckPCCPackexpPublicClaimBoundary0NF',
    claimBoundary: makeClaimBoundary0(),
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['CheckPCCPackexp0'], 'CheckPCCPackexp0 input must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['CheckPCCPackexp0'], 'CheckPCCPackexp0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'CheckPCCPackexpJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateConcreteRecordAlignment0({
  concreteRecord,
  materializedPCCPack,
  pccPack,
  coverage,
}) {
  const nf = concreteRecord.NF ?? concreteRecord.nf;

  if (!isPlainObject(nf)) {
    return validationReject0(['ConcretePCCPackRecord', 'NF'], 'accepted concrete PCCPack record must expose NF', {
      actual: typeof nf,
    });
  }

  const expected = {
    pccPackDigest: digestCanonical0(pccPack),
    materializedPCCPackDigest: digestCanonical0(materializedPCCPack),
    concreteCoverageDigest: digestCanonical0(coverage),
  };

  for (const [field, digest] of Object.entries(expected)) {
    if (!sameDigestHex0(nf[field], digest)) {
      return validationReject0(['ConcretePCCPackRecord', 'NF', field], `concrete PCCPack record ${field} mismatch`, {
        expected: digest,
        actual: nf[field],
      });
    }
  }

  return validationAccept0({
    kind: 'CheckPCCPackexpConcreteRecordAlignment0NF',
    ...expected,
  });
}

function resolveMaterializedPCCPack0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  if (value.kind === 'MaterializedPCCPack0') {
    return value;
  }

  return (
    value.MaterializedPCCPackEnvelope ??
    value.MaterializedPCCPack ??
    value.materializedPCCPack ??
    null
  );
}

function resolvePCCPack0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  if (value.kind === 'PCCPack0') {
    return value;
  }

  return value.PCCPack ?? value.pccPack ?? value.Pgen ?? null;
}

function makeClaimBoundary0() {
  return {
    antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
    consequent: 'P = NP',
    conditional: true,
  };
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

import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckIntegratedPipeline0,
  INTEGRATED_PIPELINE_PHASES0,
  makeSyntheticIntegratedPipeline0,
} from './pcc-integrated-pipeline0.mjs';

const CHECKER_VERSION = 0;

export const RUNALL_PUBLIC_CONCLUSION0 = Object.freeze({
  antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
  consequent: 'P = NP',
  conditional: true,
});

export const RUNALL_CHECKER_COVERAGE0 = Object.freeze([
  'CheckVerifierFrag0',
  'CheckBoot0',
  'CheckBootBatch0',
  'CheckBootAudit0',
  'CheckKImpl0',
  'CheckConformance0',
  'CheckSigmaRegistry0',
  'CheckReflectionRegistry0',
  'CheckKBundle0',
  'CheckHard0',
  'CheckRows0',
  'CheckBatchDeps0',
  'CheckRowFamilies0',
  'CheckGlobalProofDAG0',
  'CheckLocalPackageFamily0',
  'CheckLocalPackages0',
  'CheckImportGraph0',
  'CheckNoHiddenMin0',
  'CheckBounds0',
  'CheckGlobalFirewalls0',
  'CheckGPack0',
  'CheckRowFamG0',
  'CheckFinalFrameworkMatch0',
  'CheckSATDecision0',
  'CheckSATBounds0',
  'CheckFinalIntegration0',
  'CheckFinal0',
  'CheckRowFamFinal0',
  'CheckPackSufficiency0',
  'ReplayAcceptRun0',
  'CheckAcceptRun0',
  'EmitFinalVerdict0',
  'CheckIntegratedPipeline0',
  'RunAll0',
]);

export function makeSyntheticRunAllInput0(overrides = {}) {
  return {
    kind: 'RunAllInput0',
    version: CHECKER_VERSION,
    Pipeline: makeSyntheticIntegratedPipeline0(),
    RequiredPhaseOrder: INTEGRATED_PIPELINE_PHASES0,
    RequiredCheckers: RUNALL_CHECKER_COVERAGE0,
    RequiredPublicConclusion: RUNALL_PUBLIC_CONCLUSION0,
    ...overrides,
  };
}

export async function RunAll0(input = makeSyntheticRunAllInput0()) {
  return CheckRunAll0(input);
}

export async function CheckRunAll0(input = makeSyntheticRunAllInput0()) {
  const checker = 'RunAll0';
  const ledger = [];
  const normalized = normalizeRunAllInput0(input);

  const shape = validateRunAllInput0(normalized);

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

  const integratedRecord = await CheckIntegratedPipeline0(normalized.Pipeline);
  const integrated = recordToValidation0(integratedRecord, ['Pipeline']);

  ledger.push({
    phase: 'CheckIntegratedPipeline0',
    status: integrated.ok ? 'pass' : 'fail',
    digest: integratedRecord.Digest ?? integratedRecord.digest ?? digestCanonical0(integratedRecord),
  });

  if (!integrated.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.integrated`,
      path: integrated.path,
      witness: integrated.witness,
      ledger,
    });
  }

  const integratedNF = integratedRecord.NF ?? integratedRecord.nf;
  const status = validateIntegratedStatus0(integratedNF, normalized);

  ledger.push({
    phase: 'publicStatus',
    status: status.ok ? 'pass' : 'fail',
    digest: digestCanonical0(status.nf ?? status.witness ?? null),
  });

  if (!status.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.status`,
      path: status.path,
      witness: status.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'RunAll0StatusNF',
    checker,
    version: CHECKER_VERSION,
    status: 'complete',
    claimBoundary: 'conditional-on-accepted-generated-package',
    phaseOrder: INTEGRATED_PIPELINE_PHASES0,
    phaseCount: INTEGRATED_PIPELINE_PHASES0.length,
    checkerCoverage: RUNALL_CHECKER_COVERAGE0,
    checkerCount: RUNALL_CHECKER_COVERAGE0.length,
    finalVerdict: integratedNF.finalVerdict,
    publicConclusionEmitted: integratedNF.publicConclusionEmitted,
    publicConclusion: RUNALL_PUBLIC_CONCLUSION0,
    integratedDigest: integratedRecord.Digest ?? integratedRecord.digest,
    packDigest: integratedNF.packDigest,
    acceptRunDigest: integratedNF.acceptRunDigest,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function normalizeRunAllInput0(input) {
  if (input === undefined || input === null) {
    return makeSyntheticRunAllInput0();
  }

  if (isPlainObject(input) && input.kind === 'IntegratedPipeline0') {
    return makeSyntheticRunAllInput0({
      Pipeline: input,
    });
  }

  if (isPlainObject(input) && input.Pipeline !== undefined) {
    return {
      kind: input.kind ?? 'RunAllInput0',
      version: input.version ?? CHECKER_VERSION,
      Pipeline: input.Pipeline,
      RequiredPhaseOrder: input.RequiredPhaseOrder ?? INTEGRATED_PIPELINE_PHASES0,
      RequiredCheckers: input.RequiredCheckers ?? RUNALL_CHECKER_COVERAGE0,
      RequiredPublicConclusion: input.RequiredPublicConclusion ?? RUNALL_PUBLIC_CONCLUSION0,
    };
  }

  if (isPlainObject(input) && input.pipeline !== undefined) {
    return {
      kind: input.kind ?? 'RunAllInput0',
      version: input.version ?? CHECKER_VERSION,
      Pipeline: input.pipeline,
      RequiredPhaseOrder: input.RequiredPhaseOrder ?? INTEGRATED_PIPELINE_PHASES0,
      RequiredCheckers: input.RequiredCheckers ?? RUNALL_CHECKER_COVERAGE0,
      RequiredPublicConclusion: input.RequiredPublicConclusion ?? RUNALL_PUBLIC_CONCLUSION0,
    };
  }

  return input;
}

function validateRunAllInput0(input) {
  if (!isPlainObject(input)) {
    return validationReject0([], 'RunAllInput0 must be an object', {
      actual: typeof input,
    });
  }

  if (input.kind !== undefined && input.kind !== 'RunAllInput0') {
    return validationReject0(['kind'], 'RunAllInput0 kind must be RunAllInput0 when present', {
      actual: input.kind,
    });
  }

  if (input.version !== undefined && input.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `RunAllInput0 version must be ${CHECKER_VERSION} when present`, {
      actual: input.version,
    });
  }

  if (!isPlainObject(input.Pipeline)) {
    return validationReject0(['Pipeline'], 'RunAllInput0 Pipeline must be an object', {
      actual: typeof input.Pipeline,
    });
  }

  if (!Array.isArray(input.RequiredPhaseOrder)) {
    return validationReject0(['RequiredPhaseOrder'], 'RunAllInput0 RequiredPhaseOrder must be an array', {
      actual: typeof input.RequiredPhaseOrder,
    });
  }

  for (let index = 0; index < INTEGRATED_PIPELINE_PHASES0.length; index += 1) {
    if (input.RequiredPhaseOrder[index] !== INTEGRATED_PIPELINE_PHASES0[index]) {
      return validationReject0(['RequiredPhaseOrder', index], 'RunAllInput0 required phase order mismatch', {
        expected: INTEGRATED_PIPELINE_PHASES0[index],
        actual: input.RequiredPhaseOrder[index],
      });
    }
  }

  if (!Array.isArray(input.RequiredCheckers)) {
    return validationReject0(['RequiredCheckers'], 'RunAllInput0 RequiredCheckers must be an array', {
      actual: typeof input.RequiredCheckers,
    });
  }

  if (!arrayContainsAll0(input.RequiredCheckers, RUNALL_CHECKER_COVERAGE0)) {
    return validationReject0(['RequiredCheckers'], 'RunAllInput0 RequiredCheckers is missing required checker names', {
      expected: RUNALL_CHECKER_COVERAGE0,
      actual: input.RequiredCheckers,
    });
  }

  if (!isPlainObject(input.RequiredPublicConclusion)) {
    return validationReject0(['RequiredPublicConclusion'], 'RunAllInput0 RequiredPublicConclusion must be an object', {
      actual: typeof input.RequiredPublicConclusion,
    });
  }

  if (input.RequiredPublicConclusion.antecedent !== RUNALL_PUBLIC_CONCLUSION0.antecedent) {
    return validationReject0(['RequiredPublicConclusion', 'antecedent'], 'RunAll0 public conclusion antecedent mismatch', {
      expected: RUNALL_PUBLIC_CONCLUSION0.antecedent,
      actual: input.RequiredPublicConclusion.antecedent,
    });
  }

  if (input.RequiredPublicConclusion.consequent !== RUNALL_PUBLIC_CONCLUSION0.consequent) {
    return validationReject0(['RequiredPublicConclusion', 'consequent'], 'RunAll0 public conclusion consequent mismatch', {
      expected: RUNALL_PUBLIC_CONCLUSION0.consequent,
      actual: input.RequiredPublicConclusion.consequent,
    });
  }

  return validationAccept0({
    kind: 'RunAllInput0NF',
  });
}

function validateIntegratedStatus0(integratedNF, input) {
  if (!isPlainObject(integratedNF)) {
    return validationReject0(['IntegratedPipeline', 'NF'], 'integrated pipeline must return a normal form object', {
      actual: typeof integratedNF,
    });
  }

  if (!Array.isArray(integratedNF.phaseOrder)) {
    return validationReject0(['IntegratedPipeline', 'NF', 'phaseOrder'], 'integrated pipeline phaseOrder must be an array', {
      actual: typeof integratedNF.phaseOrder,
    });
  }

  for (let index = 0; index < INTEGRATED_PIPELINE_PHASES0.length; index += 1) {
    if (integratedNF.phaseOrder[index] !== INTEGRATED_PIPELINE_PHASES0[index]) {
      return validationReject0(['IntegratedPipeline', 'NF', 'phaseOrder', index], 'integrated pipeline phase order mismatch', {
        expected: INTEGRATED_PIPELINE_PHASES0[index],
        actual: integratedNF.phaseOrder[index],
      });
    }
  }

  if (!Array.isArray(integratedNF.phaseDigests)) {
    return validationReject0(['IntegratedPipeline', 'NF', 'phaseDigests'], 'integrated pipeline phaseDigests must be an array', {
      actual: typeof integratedNF.phaseDigests,
    });
  }

  const phaseDigestNames = new Set(integratedNF.phaseDigests.map((entry) => entry.phase));

  for (const phase of INTEGRATED_PIPELINE_PHASES0) {
    if (!phaseDigestNames.has(phase)) {
      return validationReject0(['IntegratedPipeline', 'NF', 'phaseDigests'], 'integrated pipeline digest transcript is missing a phase', {
        phase,
      });
    }
  }

  if (integratedNF.finalVerdict !== 'accept') {
    return validationReject0(['IntegratedPipeline', 'NF', 'finalVerdict'], 'RunAll0 requires an accepted final integrated verdict', {
      actual: integratedNF.finalVerdict,
    });
  }

  if (integratedNF.publicConclusionEmitted !== true) {
    return validationReject0(['IntegratedPipeline', 'NF', 'publicConclusionEmitted'], 'RunAll0 requires public conclusion emission after acceptance', {
      actual: integratedNF.publicConclusionEmitted,
    });
  }

  if (!isPlainObject(integratedNF.publicConclusion)) {
    return validationReject0(['IntegratedPipeline', 'NF', 'publicConclusion'], 'integrated pipeline publicConclusion must be an object', {
      actual: typeof integratedNF.publicConclusion,
    });
  }

  if (integratedNF.publicConclusion.antecedent !== input.RequiredPublicConclusion.antecedent) {
    return validationReject0(['IntegratedPipeline', 'NF', 'publicConclusion', 'antecedent'], 'integrated public conclusion antecedent mismatch', {
      expected: input.RequiredPublicConclusion.antecedent,
      actual: integratedNF.publicConclusion.antecedent,
    });
  }

  if (integratedNF.publicConclusion.consequent !== input.RequiredPublicConclusion.consequent) {
    return validationReject0(['IntegratedPipeline', 'NF', 'publicConclusion', 'consequent'], 'integrated public conclusion consequent mismatch', {
      expected: input.RequiredPublicConclusion.consequent,
      actual: integratedNF.publicConclusion.consequent,
    });
  }

  return validationAccept0({
    kind: 'RunAllIntegratedStatus0NF',
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

function arrayContainsAll0(actual, required) {
  if (!Array.isArray(actual)) {
    return false;
  }

  return required.every((entry) => actual.includes(entry));
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}
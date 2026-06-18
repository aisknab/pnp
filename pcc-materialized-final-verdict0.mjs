import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedAcceptRun0,
  CheckMaterializedAcceptRunFile0,
  MATERIALIZED_ACCEPT_RUN_VERDICTS0,
} from './pcc-materialized-accept-run0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_FINAL_VERDICT_PHASES0 = Object.freeze([
  'CheckMaterializedAcceptRun0',
  'CheckMaterializedFinalVerdictPolicy0',
  'EmitMaterializedFinalVerdict0',
]);

export const MATERIALIZED_FINAL_VERDICT_REQUIRED_FIELDS0 = Object.freeze([
  'AcceptRun',
  'VerdictPolicy',
  'PublicClaimBoundary',
]);

export const MATERIALIZED_FINAL_VERDICT_POLICY0 = Object.freeze({
  kind: 'MaterializedFinalVerdictPolicy0',
  version: CHECKER_VERSION,
  acceptsPendingVerdict: true,
  acceptsRejectVerdict: true,
  publicConclusionOnlyAfterAccept: true,
  rejectEmitsNoPublicConclusion: true,
  pendingEmitsNoPublicConclusion: true,
  acceptRunOutsideCore: true,
  generatedPackageRefOnly: true,
});

export function makeMaterializedFinalVerdictInput0({
  acceptRun,
  overrides = {},
} = {}) {
  return {
    kind: 'MaterializedFinalVerdictInput0',
    version: CHECKER_VERSION,
    AcceptRun: acceptRun,
    VerdictPolicy: {
      ...MATERIALIZED_FINAL_VERDICT_POLICY0,
    },
    PublicClaimBoundary: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
    ...overrides,
  };
}

export async function CheckMaterializedFinalVerdict0(input, config = {}) {
  const checker = 'CheckMaterializedFinalVerdict0';
  const ledger = [];
  const normalized = normalizeFinalVerdictInput0(input);

  const shape = validateFinalVerdictInputShape0(normalized);

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

  const acceptRunRecord = await CheckMaterializedAcceptRun0(
    normalized.AcceptRun,
    config.acceptRunConfig ?? {},
  );
  const acceptRun = recordToValidation0(acceptRunRecord, ['AcceptRun']);

  ledger.push({
    phase: 'CheckMaterializedAcceptRun0',
    status: acceptRun.ok ? 'pass' : 'fail',
    digest: acceptRunRecord.Digest ?? acceptRunRecord.digest ?? digestCanonical0(acceptRunRecord),
  });

  if (!acceptRun.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.AcceptRun`,
      path: acceptRun.path,
      witness: acceptRun.witness,
      ledger,
    });
  }

  const policy = validateFinalVerdictPolicy0(normalized.VerdictPolicy);

  ledger.push({
    phase: 'VerdictPolicy',
    status: policy.ok ? 'pass' : 'fail',
    digest: digestCanonical0(policy.nf ?? policy.witness ?? null),
  });

  if (!policy.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.VerdictPolicy`,
      path: policy.path,
      witness: policy.witness,
      ledger,
    });
  }

  const boundary = validatePublicClaimBoundary0(normalized.PublicClaimBoundary);

  ledger.push({
    phase: 'PublicClaimBoundary',
    status: boundary.ok ? 'pass' : 'fail',
    digest: digestCanonical0(boundary.nf ?? boundary.witness ?? null),
  });

  if (!boundary.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.PublicClaimBoundary`,
      path: boundary.path,
      witness: boundary.witness,
      ledger,
    });
  }

  const emission = emitFinalVerdictFromAcceptRunNF0({
    acceptRunNF: acceptRunRecord.NF ?? acceptRunRecord.nf,
    acceptRunDigest: acceptRunRecord.Digest ?? acceptRunRecord.digest,
    publicClaimBoundary: normalized.PublicClaimBoundary,
  });

  ledger.push({
    phase: 'EmitMaterializedFinalVerdict0',
    status: emission.ok ? 'pass' : 'fail',
    digest: digestCanonical0(emission.nf ?? emission.witness ?? null),
  });

  if (!emission.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.EmitFinalVerdict`,
      path: emission.path,
      witness: emission.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedFinalVerdict0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: MATERIALIZED_FINAL_VERDICT_PHASES0,
    verdict: emission.nf.verdict,
    replayAccepted: emission.nf.replayAccepted,
    publicConclusionEmitted: emission.nf.publicConclusionEmitted,
    publicConclusion: emission.nf.publicConclusion,
    claimBoundary: 'conditional-on-accepted-materialized-accept-run-replay',
    acceptRunDigest: acceptRunRecord.Digest ?? acceptRunRecord.digest,
    generatedPackagePath: emission.nf.generatedPackagePath,
    aggregateDigest: emission.nf.aggregateDigest,
    transcriptDigest: emission.nf.transcriptDigest,
    rejectLogCount: emission.nf.rejectLogCount,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckMaterializedFinalVerdictFile0(filePath, config = {}) {
  const checker = 'CheckMaterializedFinalVerdictFile0';
  const ledger = [];

  const acceptRunRecord = await CheckMaterializedAcceptRunFile0(
    filePath,
    config.acceptRunConfig ?? {},
  );
  const acceptRun = recordToValidation0(acceptRunRecord, ['AcceptRunFile']);

  ledger.push({
    phase: 'CheckMaterializedAcceptRunFile0',
    status: acceptRun.ok ? 'pass' : 'fail',
    digest: acceptRunRecord.Digest ?? acceptRunRecord.digest ?? digestCanonical0(acceptRunRecord),
  });

  if (!acceptRun.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.AcceptRunFile`,
      path: acceptRun.path,
      witness: acceptRun.witness,
      ledger,
    });
  }

  const policy = validateFinalVerdictPolicy0(config.VerdictPolicy ?? MATERIALIZED_FINAL_VERDICT_POLICY0);

  ledger.push({
    phase: 'VerdictPolicy',
    status: policy.ok ? 'pass' : 'fail',
    digest: digestCanonical0(policy.nf ?? policy.witness ?? null),
  });

  if (!policy.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.VerdictPolicy`,
      path: policy.path,
      witness: policy.witness,
      ledger,
    });
  }

  const publicClaimBoundary = config.PublicClaimBoundary ?? MATERIALIZED_PACK_PUBLIC_BOUNDARY0;
  const boundary = validatePublicClaimBoundary0(publicClaimBoundary);

  ledger.push({
    phase: 'PublicClaimBoundary',
    status: boundary.ok ? 'pass' : 'fail',
    digest: digestCanonical0(boundary.nf ?? boundary.witness ?? null),
  });

  if (!boundary.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.PublicClaimBoundary`,
      path: boundary.path,
      witness: boundary.witness,
      ledger,
    });
  }

  const emission = emitFinalVerdictFromAcceptRunNF0({
    acceptRunNF: acceptRunRecord.NF ?? acceptRunRecord.nf,
    acceptRunDigest: acceptRunRecord.Digest ?? acceptRunRecord.digest,
    publicClaimBoundary,
  });

  ledger.push({
    phase: 'EmitMaterializedFinalVerdict0',
    status: emission.ok ? 'pass' : 'fail',
    digest: digestCanonical0(emission.nf ?? emission.witness ?? null),
  });

  if (!emission.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.EmitFinalVerdict`,
      path: emission.path,
      witness: emission.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedFinalVerdictFile0NF',
    checker,
    version: CHECKER_VERSION,
    filePath: acceptRunRecord.NF.filePath,
    byteLength: acceptRunRecord.NF.byteLength,
    fileDigest: acceptRunRecord.NF.fileDigest,
    verdict: emission.nf.verdict,
    replayAccepted: emission.nf.replayAccepted,
    publicConclusionEmitted: emission.nf.publicConclusionEmitted,
    publicConclusion: emission.nf.publicConclusion,
    claimBoundary: 'conditional-on-accepted-materialized-accept-run-replay',
    acceptRunDigest: acceptRunRecord.Digest ?? acceptRunRecord.digest,
    generatedPackagePath: emission.nf.generatedPackagePath,
    aggregateDigest: emission.nf.aggregateDigest,
    transcriptDigest: emission.nf.transcriptDigest,
    rejectLogCount: emission.nf.rejectLogCount,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function normalizeFinalVerdictInput0(input) {
  if (isPlainObject(input) && input.kind === 'MaterializedAcceptRun0') {
    return makeMaterializedFinalVerdictInput0({
      acceptRun: input,
    });
  }

  if (isPlainObject(input) && Object.prototype.hasOwnProperty.call(input, 'AcceptRun')) {
    return {
      kind: input.kind ?? 'MaterializedFinalVerdictInput0',
      version: input.version ?? CHECKER_VERSION,
      AcceptRun: input.AcceptRun,
      VerdictPolicy: input.VerdictPolicy ?? MATERIALIZED_FINAL_VERDICT_POLICY0,
      PublicClaimBoundary: input.PublicClaimBoundary ?? MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    };
  }

  return input;
}

function validateFinalVerdictInputShape0(input) {
  if (!isPlainObject(input)) {
    return validationReject0([], 'MaterializedFinalVerdictInput0 must be an object', {
      actual: typeof input,
    });
  }

  if (input.kind !== undefined && input.kind !== 'MaterializedFinalVerdictInput0') {
    return validationReject0(['kind'], 'MaterializedFinalVerdictInput0 kind mismatch', {
      actual: input.kind,
    });
  }

  if (input.version !== undefined && input.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedFinalVerdictInput0 version must be ${CHECKER_VERSION} when present`, {
      actual: input.version,
    });
  }

  for (const field of MATERIALIZED_FINAL_VERDICT_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0([field], 'MaterializedFinalVerdictInput0 is missing a required field', {
        field,
      });
    }
  }

  if (!isPlainObject(input.AcceptRun)) {
    return validationReject0(['AcceptRun'], 'MaterializedFinalVerdictInput0 AcceptRun must be an object', {
      actual: typeof input.AcceptRun,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalVerdictInputShape0NF',
  });
}

function validateFinalVerdictPolicy0(policy) {
  if (!isPlainObject(policy)) {
    return validationReject0(['VerdictPolicy'], 'VerdictPolicy must be an object', {
      actual: typeof policy,
    });
  }

  if (policy.kind !== undefined && policy.kind !== 'MaterializedFinalVerdictPolicy0') {
    return validationReject0(['VerdictPolicy', 'kind'], 'VerdictPolicy kind mismatch', {
      actual: policy.kind,
    });
  }

  for (const field of [
    'acceptsPendingVerdict',
    'acceptsRejectVerdict',
    'publicConclusionOnlyAfterAccept',
    'rejectEmitsNoPublicConclusion',
    'pendingEmitsNoPublicConclusion',
    'acceptRunOutsideCore',
    'generatedPackageRefOnly',
  ]) {
    if (policy[field] !== true) {
      return validationReject0(['VerdictPolicy', field], `VerdictPolicy must certify ${field}`, {
        actual: policy[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedFinalVerdictPolicy0NF',
  });
}

function validatePublicClaimBoundary0(boundary) {
  if (!isPlainObject(boundary)) {
    return validationReject0(['PublicClaimBoundary'], 'PublicClaimBoundary must be an object', {
      actual: typeof boundary,
    });
  }

  if (!samePublicConclusion0(boundary, MATERIALIZED_PACK_PUBLIC_BOUNDARY0)) {
    return validationReject0(['PublicClaimBoundary'], 'PublicClaimBoundary mismatch', {
      expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
      actual: boundary,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalVerdictPublicClaimBoundary0NF',
  });
}

function emitFinalVerdictFromAcceptRunNF0({
  acceptRunNF,
  acceptRunDigest,
  publicClaimBoundary,
}) {
  if (!isPlainObject(acceptRunNF)) {
    return validationReject0(['AcceptRun', 'NF'], 'verified MaterializedAcceptRun normal form must be an object', {
      actual: typeof acceptRunNF,
    });
  }

  if (!MATERIALIZED_ACCEPT_RUN_VERDICTS0.includes(acceptRunNF.verdict)) {
    return validationReject0(['AcceptRun', 'NF', 'verdict'], 'verified MaterializedAcceptRun verdict is not allowed', {
      actual: acceptRunNF.verdict,
    });
  }

  if (acceptRunNF.verdict === 'accept') {
    if (acceptRunNF.replayAccepted !== true) {
      return validationReject0(['AcceptRun', 'NF', 'replayAccepted'], 'accept final verdict requires replayAccepted=true', {
        actual: acceptRunNF.replayAccepted,
      });
    }

    if (acceptRunNF.publicConclusionEmitted !== true) {
      return validationReject0(['AcceptRun', 'NF', 'publicConclusionEmitted'], 'accept final verdict requires publicConclusionEmitted=true', {
        actual: acceptRunNF.publicConclusionEmitted,
      });
    }

    if (!samePublicConclusion0(acceptRunNF.publicConclusion, publicClaimBoundary)) {
      return validationReject0(['AcceptRun', 'NF', 'publicConclusion'], 'accept final verdict public conclusion mismatch', {
        expected: publicClaimBoundary,
        actual: acceptRunNF.publicConclusion,
      });
    }

    return validationAccept0({
      kind: 'MaterializedFinalVerdictEmission0NF',
      verdict: 'accept',
      replayAccepted: true,
      publicConclusionEmitted: true,
      publicConclusion: {
        ...publicClaimBoundary,
      },
      rejectLogCount: acceptRunNF.rejectLogCount,
      generatedPackagePath: acceptRunNF.generatedPackagePath,
      aggregateDigest: acceptRunNF.aggregateDigest,
      transcriptDigest: acceptRunNF.transcriptDigest,
      acceptRunDigest,
    });
  }

  if (acceptRunNF.replayAccepted !== false) {
    return validationReject0(['AcceptRun', 'NF', 'replayAccepted'], 'non-accept final verdict requires replayAccepted=false', {
      verdict: acceptRunNF.verdict,
      actual: acceptRunNF.replayAccepted,
    });
  }

  if (acceptRunNF.publicConclusionEmitted !== false || acceptRunNF.publicConclusion !== null) {
    return validationReject0(['AcceptRun', 'NF', 'publicConclusion'], 'non-accept final verdict must not emit public conclusion', {
      verdict: acceptRunNF.verdict,
      publicConclusionEmitted: acceptRunNF.publicConclusionEmitted,
      publicConclusion: acceptRunNF.publicConclusion,
    });
  }

  return validationAccept0({
    kind: 'MaterializedFinalVerdictEmission0NF',
    verdict: acceptRunNF.verdict,
    replayAccepted: false,
    publicConclusionEmitted: false,
    publicConclusion: null,
    rejectLogCount: acceptRunNF.rejectLogCount,
    generatedPackagePath: acceptRunNF.generatedPackagePath,
    aggregateDigest: acceptRunNF.aggregateDigest,
    transcriptDigest: acceptRunNF.transcriptDigest,
    acceptRunDigest,
  });
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
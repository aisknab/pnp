import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedFinalVerdictFile0,
} from './pcc-materialized-final-verdict0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
} from './pcc-materialized-pack0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_PUBLIC_STATUS_PHASES0 = Object.freeze([
  'CheckMaterializedPublicStatusInput0',
  'CheckMaterializedPublicStatusPolicy0',
  'CheckMaterializedPublicClaimBoundary0',
  'CheckMaterializedFinalVerdictFile0',
  'EmitMaterializedPublicStatus0',
]);

export const MATERIALIZED_PUBLIC_STATUS_VALUES0 = Object.freeze([
  'pending',
  'rejected',
  'accepted',
]);

export const MATERIALIZED_PUBLIC_STATUS_POLICY0 = Object.freeze({
  kind: 'MaterializedPublicStatusPolicy0',
  version: CHECKER_VERSION,
  materializedPathOnly: true,
  separateFromSyntheticRunAll: true,
  acceptsPendingVerdict: true,
  acceptsRejectVerdict: true,
  acceptsAcceptVerdict: true,
  publicConclusionOnlyAfterAccept: true,
  rejectEmitsNoPublicConclusion: true,
  pendingEmitsNoPublicConclusion: true,
  acceptRunOutsideCore: true,
  generatedPackageRefOnly: true,
});

export function makeMaterializedPublicStatusInput0({
  acceptRunFilePath,
  overrides = {},
} = {}) {
  return {
    kind: 'MaterializedPublicStatusInput0',
    version: CHECKER_VERSION,
    AcceptRunFilePath: acceptRunFilePath,
    StatusPolicy: {
      ...MATERIALIZED_PUBLIC_STATUS_POLICY0,
    },
    PublicClaimBoundary: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
    ...overrides,
  };
}

export async function CheckMaterializedPublicStatus0(input, config = {}) {
  const checker = 'CheckMaterializedPublicStatus0';
  const ledger = [];
  const normalized = normalizePublicStatusInput0(input);

  const shape = validatePublicStatusInput0(normalized);

  ledger.push({
    phase: 'CheckMaterializedPublicStatusInput0',
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

  const policy = validatePublicStatusPolicy0(normalized.StatusPolicy);

  ledger.push({
    phase: 'CheckMaterializedPublicStatusPolicy0',
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

  const boundary = validatePublicClaimBoundary0(normalized.PublicClaimBoundary);

  ledger.push({
    phase: 'CheckMaterializedPublicClaimBoundary0',
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

  const finalVerdictRecord = await CheckMaterializedFinalVerdictFile0(
    normalized.AcceptRunFilePath,
    config.finalVerdictConfig ?? {},
  );
  const finalVerdict = recordToValidation0(finalVerdictRecord, ['AcceptRunFilePath']);

  ledger.push({
    phase: 'CheckMaterializedFinalVerdictFile0',
    status: finalVerdict.ok ? 'pass' : 'fail',
    digest: finalVerdictRecord.Digest ?? finalVerdictRecord.digest ?? digestCanonical0(finalVerdictRecord),
  });

  if (!finalVerdict.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.FinalVerdict`,
      path: finalVerdict.path,
      witness: finalVerdict.witness,
      ledger,
    });
  }

  const emission = emitMaterializedPublicStatus0({
    finalVerdictNF: finalVerdictRecord.NF ?? finalVerdictRecord.nf,
    finalVerdictDigest: finalVerdictRecord.Digest ?? finalVerdictRecord.digest,
    publicClaimBoundary: normalized.PublicClaimBoundary,
  });

  ledger.push({
    phase: 'EmitMaterializedPublicStatus0',
    status: emission.ok ? 'pass' : 'fail',
    digest: digestCanonical0(emission.nf ?? emission.witness ?? null),
  });

  if (!emission.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.EmitPublicStatus`,
      path: emission.path,
      witness: emission.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'MaterializedPublicStatus0NF',
    checker,
    version: CHECKER_VERSION,
    phaseOrder: MATERIALIZED_PUBLIC_STATUS_PHASES0,
    materializedPath: true,
    syntheticRunAll: false,
    status: emission.nf.status,
    verdict: emission.nf.verdict,
    replayAccepted: emission.nf.replayAccepted,
    publicConclusionEmitted: emission.nf.publicConclusionEmitted,
    publicConclusion: emission.nf.publicConclusion,
    claimBoundary: 'conditional-on-accepted-materialized-final-verdict',
    acceptRunFilePath: normalized.AcceptRunFilePath,
    acceptRunDigest: emission.nf.acceptRunDigest,
    finalVerdictDigest: finalVerdictRecord.Digest ?? finalVerdictRecord.digest,
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

export async function CheckMaterializedPublicStatusFile0(acceptRunFilePath, config = {}) {
  return CheckMaterializedPublicStatus0(makeMaterializedPublicStatusInput0({
    acceptRunFilePath,
    overrides: {
      StatusPolicy: config.StatusPolicy ?? MATERIALIZED_PUBLIC_STATUS_POLICY0,
      PublicClaimBoundary: config.PublicClaimBoundary ?? MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
  }), config);
}

function normalizePublicStatusInput0(input) {
  if (typeof input === 'string') {
    return makeMaterializedPublicStatusInput0({
      acceptRunFilePath: input,
    });
  }

  if (isPlainObject(input) && Object.prototype.hasOwnProperty.call(input, 'AcceptRunFilePath')) {
    return {
      kind: input.kind ?? 'MaterializedPublicStatusInput0',
      version: input.version ?? CHECKER_VERSION,
      AcceptRunFilePath: input.AcceptRunFilePath,
      StatusPolicy: input.StatusPolicy ?? MATERIALIZED_PUBLIC_STATUS_POLICY0,
      PublicClaimBoundary: input.PublicClaimBoundary ?? MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    };
  }

  return input;
}

function validatePublicStatusInput0(input) {
  if (!isPlainObject(input)) {
    return validationReject0([], 'MaterializedPublicStatusInput0 must be an object or file path string', {
      actual: typeof input,
    });
  }

  if (input.kind !== undefined && input.kind !== 'MaterializedPublicStatusInput0') {
    return validationReject0(['kind'], 'MaterializedPublicStatusInput0 kind mismatch', {
      actual: input.kind,
    });
  }

  if (input.version !== undefined && input.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedPublicStatusInput0 version must be ${CHECKER_VERSION} when present`, {
      actual: input.version,
    });
  }

  if (typeof input.AcceptRunFilePath !== 'string' || input.AcceptRunFilePath.length === 0) {
    return validationReject0(['AcceptRunFilePath'], 'AcceptRunFilePath must be a non-empty string', {
      actual: input.AcceptRunFilePath,
    });
  }

  if (!isPlainObject(input.StatusPolicy)) {
    return validationReject0(['StatusPolicy'], 'StatusPolicy must be an object', {
      actual: typeof input.StatusPolicy,
    });
  }

  if (!isPlainObject(input.PublicClaimBoundary)) {
    return validationReject0(['PublicClaimBoundary'], 'PublicClaimBoundary must be an object', {
      actual: typeof input.PublicClaimBoundary,
    });
  }

  return validationAccept0({
    kind: 'MaterializedPublicStatusInput0NF',
  });
}

function validatePublicStatusPolicy0(policy) {
  if (!isPlainObject(policy)) {
    return validationReject0(['StatusPolicy'], 'StatusPolicy must be an object', {
      actual: typeof policy,
    });
  }

  if (policy.kind !== undefined && policy.kind !== 'MaterializedPublicStatusPolicy0') {
    return validationReject0(['StatusPolicy', 'kind'], 'StatusPolicy kind mismatch', {
      actual: policy.kind,
    });
  }

  for (const field of [
    'materializedPathOnly',
    'separateFromSyntheticRunAll',
    'acceptsPendingVerdict',
    'acceptsRejectVerdict',
    'acceptsAcceptVerdict',
    'publicConclusionOnlyAfterAccept',
    'rejectEmitsNoPublicConclusion',
    'pendingEmitsNoPublicConclusion',
    'acceptRunOutsideCore',
    'generatedPackageRefOnly',
  ]) {
    if (policy[field] !== true) {
      return validationReject0(['StatusPolicy', field], `StatusPolicy must certify ${field}`, {
        actual: policy[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedPublicStatusPolicy0NF',
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
    kind: 'MaterializedPublicStatusClaimBoundary0NF',
  });
}

function emitMaterializedPublicStatus0({
  finalVerdictNF,
  finalVerdictDigest,
  publicClaimBoundary,
}) {
  if (!isPlainObject(finalVerdictNF)) {
    return validationReject0(['FinalVerdict', 'NF'], 'final verdict normal form must be an object', {
      actual: typeof finalVerdictNF,
    });
  }

  if (!['pending', 'reject', 'accept'].includes(finalVerdictNF.verdict)) {
    return validationReject0(['FinalVerdict', 'NF', 'verdict'], 'final verdict value is not allowed', {
      actual: finalVerdictNF.verdict,
    });
  }

  if (finalVerdictNF.verdict === 'accept') {
    if (finalVerdictNF.replayAccepted !== true) {
      return validationReject0(['FinalVerdict', 'NF', 'replayAccepted'], 'accepted public status requires replayAccepted=true', {
        actual: finalVerdictNF.replayAccepted,
      });
    }

    if (finalVerdictNF.publicConclusionEmitted !== true) {
      return validationReject0(['FinalVerdict', 'NF', 'publicConclusionEmitted'], 'accepted public status requires public conclusion emission', {
        actual: finalVerdictNF.publicConclusionEmitted,
      });
    }

    if (!samePublicConclusion0(finalVerdictNF.publicConclusion, publicClaimBoundary)) {
      return validationReject0(['FinalVerdict', 'NF', 'publicConclusion'], 'accepted public status conclusion mismatch', {
        expected: publicClaimBoundary,
        actual: finalVerdictNF.publicConclusion,
      });
    }

    return validationAccept0({
      kind: 'MaterializedPublicStatusEmission0NF',
      status: 'accepted',
      verdict: 'accept',
      replayAccepted: true,
      publicConclusionEmitted: true,
      publicConclusion: {
        ...publicClaimBoundary,
      },
      acceptRunDigest: finalVerdictNF.acceptRunDigest,
      finalVerdictDigest,
      generatedPackagePath: finalVerdictNF.generatedPackagePath,
      aggregateDigest: finalVerdictNF.aggregateDigest,
      transcriptDigest: finalVerdictNF.transcriptDigest,
      rejectLogCount: finalVerdictNF.rejectLogCount,
    });
  }

  if (finalVerdictNF.replayAccepted !== false) {
    return validationReject0(['FinalVerdict', 'NF', 'replayAccepted'], 'non-accepted public status requires replayAccepted=false', {
      verdict: finalVerdictNF.verdict,
      actual: finalVerdictNF.replayAccepted,
    });
  }

  if (finalVerdictNF.publicConclusionEmitted !== false || finalVerdictNF.publicConclusion !== null) {
    return validationReject0(['FinalVerdict', 'NF', 'publicConclusion'], 'non-accepted public status must emit no public conclusion', {
      verdict: finalVerdictNF.verdict,
      publicConclusionEmitted: finalVerdictNF.publicConclusionEmitted,
      publicConclusion: finalVerdictNF.publicConclusion,
    });
  }

  return validationAccept0({
    kind: 'MaterializedPublicStatusEmission0NF',
    status: finalVerdictNF.verdict === 'reject' ? 'rejected' : 'pending',
    verdict: finalVerdictNF.verdict,
    replayAccepted: false,
    publicConclusionEmitted: false,
    publicConclusion: null,
    acceptRunDigest: finalVerdictNF.acceptRunDigest,
    finalVerdictDigest,
    generatedPackagePath: finalVerdictNF.generatedPackagePath,
    aggregateDigest: finalVerdictNF.aggregateDigest,
    transcriptDigest: finalVerdictNF.transcriptDigest,
    rejectLogCount: finalVerdictNF.rejectLogCount,
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
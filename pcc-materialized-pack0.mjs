import { createHash } from 'node:crypto';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterialized0,
  makeMaterializedGateConfig0,
} from './pcc-materialized0.mjs';

const CHECKER_VERSION = 0;

export const MATERIALIZED_PACK_REQUIRED_FIELDS0 = Object.freeze([
  'CoreBytes',
  'CoreDigest',
  'PackBytes',
  'PackDigest',
  'CanonicalBytePolicy',
  'Manifest',
  'ProofInventory',
  'CheckPlan',
  'PublicClaimBoundary',
]);

export const MATERIALIZED_PACK_REQUIRED_CHECKS0 = Object.freeze([
  'CheckMaterialized0',
  'CheckPCCPackexp',
  'CheckPackSufficiency0',
  'ReplayAcceptRun0',
  'CheckAcceptRun0',
  'EmitFinalVerdict0',
]);

export const MATERIALIZED_PACK_PUBLIC_BOUNDARY0 = Object.freeze({
  antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
  consequent: 'P = NP',
  conditional: true,
});

export function sha256Utf8DigestRecord0(value) {
  return {
    alg: 'SHA256',
    bytes: 'utf8',
    hex: createHash('sha256').update(String(value), 'utf8').digest('hex'),
  };
}

export function canonicalBytesForMaterializedObject0(value) {
  return stableStringify0(value);
}

export function makeMaterializedPCCPackShell0(overrides = {}) {
  const coreObject = {
    kind: 'PCCCorePackage0',
    version: CHECKER_VERSION,
    packageId: 'MaterializedCandidateCore0',
    generatedBy: 'GeneratePCCPack',
    excludesAcceptRun: true,
    includesAcceptRun: false,
    canonicalByteEquality: true,
    materializedOutputOnly: true,
    noDigestOnlyEquality: true,
  };

  const packObject = {
    kind: 'PCCPack0',
    version: CHECKER_VERSION,
    packageId: 'MaterializedCandidatePack0',
    Core: coreObject,
    Manifest: {
      kind: 'MaterializedManifest0',
      version: CHECKER_VERSION,
      checker: 'CheckPCCPackexp',
    },
  };

  const coreBytes = canonicalBytesForMaterializedObject0(coreObject);
  const packBytes = canonicalBytesForMaterializedObject0(packObject);

  const shell = {
    kind: 'MaterializedPCCPack0',
    version: CHECKER_VERSION,

    CoreBytes: coreBytes,
    CoreDigest: sha256Utf8DigestRecord0(coreBytes),

    PackBytes: packBytes,
    PackDigest: sha256Utf8DigestRecord0(packBytes),

    CanonicalBytePolicy: {
      kind: 'CanonicalBytePolicy0',
      version: CHECKER_VERSION,
      canonicalJson: true,
      fullBytesCompared: true,
      digestEqualityIsNotObjectEquality: true,
      materializedOutputOnly: true,
      generatorUntrusted: true,
    },

    Manifest: {
      kind: 'MaterializedPackManifest0',
      version: CHECKER_VERSION,
      checker: 'CheckPCCPackexp',
      requiredChecks: MATERIALIZED_PACK_REQUIRED_CHECKS0,
      coreDigestField: 'CoreDigest',
      packDigestField: 'PackDigest',
      acceptsOnlyAfterReplay: true,
    },

    ProofInventory: {
      kind: 'ProofInventoryShell0',
      version: CHECKER_VERSION,
      entries: [],
      complete: false,
      requiresFutureCertificates: true,
      rejectsOpaqueProofMaterial: true,
    },

    CheckPlan: {
      kind: 'MaterializedCheckPlan0',
      version: CHECKER_VERSION,
      phases: MATERIALIZED_PACK_REQUIRED_CHECKS0,
      firstFailureReplayable: true,
      publicConclusionOnlyAfterAccept: true,
    },

    PublicClaimBoundary: MATERIALIZED_PACK_PUBLIC_BOUNDARY0,

    PiMaterializedShell: {
      kind: 'PiMaterializedShell0',
      version: CHECKER_VERSION,
      proofStatus: 'envelope-only',
    },

    ...overrides,
  };

  return shell;
}

export async function CheckMaterializedPCCPackShell0(shell) {
  const checker = 'CheckMaterializedPCCPackShell0';
  const ledger = [];

  const shape = validateShellShape0(shell);

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

  const bytes = validateCanonicalBytes0(shell);

  ledger.push({
    phase: 'canonicalBytes',
    status: bytes.ok ? 'pass' : 'fail',
    digest: digestCanonical0(bytes.nf ?? bytes.witness ?? null),
  });

  if (!bytes.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.canonicalBytes`,
      path: bytes.path,
      witness: bytes.witness,
      ledger,
    });
  }

  const materializedRecord = await CheckMaterialized0(
    shell,
    makeMaterializedGateConfig0({
      rejectSyntheticText: true,
      rejectPlaceholderNotes: true,
      rejectInvalidDigestHex: true,
      rejectOpaqueProofMaterial: true,
    }),
  );

  const materialized = recordToValidation0(materializedRecord, []);

  ledger.push({
    phase: 'CheckMaterialized0',
    status: materialized.ok ? 'pass' : 'fail',
    digest: materializedRecord.Digest ?? materializedRecord.digest ?? digestCanonical0(materializedRecord),
  });

  if (!materialized.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.materialized`,
      path: materialized.path,
      witness: materialized.witness,
      ledger,
    });
  }

  const policy = validateCanonicalBytePolicy0(shell);

  ledger.push({
    phase: 'canonicalBytePolicy',
    status: policy.ok ? 'pass' : 'fail',
    digest: digestCanonical0(policy.nf ?? policy.witness ?? null),
  });

  if (!policy.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.canonicalBytePolicy`,
      path: policy.path,
      witness: policy.witness,
      ledger,
    });
  }

  const plan = validateCheckPlan0(shell);

  ledger.push({
    phase: 'checkPlan',
    status: plan.ok ? 'pass' : 'fail',
    digest: digestCanonical0(plan.nf ?? plan.witness ?? null),
  });

  if (!plan.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.checkPlan`,
      path: plan.path,
      witness: plan.witness,
      ledger,
    });
  }

  const claim = validatePublicClaimBoundary0(shell);

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

  const nf = {
    kind: 'MaterializedPCCPackShell0NF',
    checker,
    version: CHECKER_VERSION,
    envelopeOnly: true,
    coreDigest: shell.CoreDigest,
    packDigest: shell.PackDigest,
    requiredChecks: MATERIALIZED_PACK_REQUIRED_CHECKS0,
    publicClaimBoundary: MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    materializedDigest: materializedRecord.Digest ?? materializedRecord.digest,
    piMaterializedShellDigest: digestCanonical0(getPiMaterializedShell0(shell)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateShellShape0(shell) {
  if (!isPlainObject(shell)) {
    return validationReject0([], 'MaterializedPCCPack0 must be an object', {
      actual: typeof shell,
    });
  }

  if (shell.kind !== undefined && shell.kind !== 'MaterializedPCCPack0') {
    return validationReject0(['kind'], 'MaterializedPCCPack0 kind must be MaterializedPCCPack0 when present', {
      actual: shell.kind,
    });
  }

  if (shell.version !== undefined && shell.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `MaterializedPCCPack0 version must be ${CHECKER_VERSION} when present`, {
      actual: shell.version,
    });
  }

  for (const field of MATERIALIZED_PACK_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(shell, field)) {
      return validationReject0([field], 'MaterializedPCCPack0 is missing a required field', {
        field,
      });
    }
  }

  if (getPiMaterializedShell0(shell) === undefined) {
    return validationReject0(['PiMaterializedShell'], 'MaterializedPCCPack0 is missing PiMaterializedShell or Πmaterialized', null);
  }

  return validationAccept0({
    kind: 'MaterializedPCCPackShape0NF',
  });
}

function validateCanonicalBytes0(shell) {
  if (typeof shell.CoreBytes !== 'string' || shell.CoreBytes.length === 0) {
    return validationReject0(['CoreBytes'], 'CoreBytes must be a non-empty canonical byte string', {
      actual: typeof shell.CoreBytes,
    });
  }

  if (typeof shell.PackBytes !== 'string' || shell.PackBytes.length === 0) {
    return validationReject0(['PackBytes'], 'PackBytes must be a non-empty canonical byte string', {
      actual: typeof shell.PackBytes,
    });
  }

  const coreParsed = parseCanonicalJson0(shell.CoreBytes, ['CoreBytes']);

  if (!coreParsed.ok) {
    return coreParsed;
  }

  const packParsed = parseCanonicalJson0(shell.PackBytes, ['PackBytes']);

  if (!packParsed.ok) {
    return packParsed;
  }

  const coreCanonical = stableStringify0(coreParsed.value);
  const packCanonical = stableStringify0(packParsed.value);

  if (coreCanonical !== shell.CoreBytes) {
    return validationReject0(['CoreBytes'], 'CoreBytes must be canonical JSON bytes', {
      expectedDigest: sha256Utf8DigestRecord0(coreCanonical),
      actualDigest: sha256Utf8DigestRecord0(shell.CoreBytes),
    });
  }

  if (packCanonical !== shell.PackBytes) {
    return validationReject0(['PackBytes'], 'PackBytes must be canonical JSON bytes', {
      expectedDigest: sha256Utf8DigestRecord0(packCanonical),
      actualDigest: sha256Utf8DigestRecord0(shell.PackBytes),
    });
  }

  if (!sameDigestRecord0(shell.CoreDigest, sha256Utf8DigestRecord0(shell.CoreBytes))) {
    return validationReject0(['CoreDigest'], 'CoreDigest must be SHA256 over CoreBytes', {
      expected: sha256Utf8DigestRecord0(shell.CoreBytes),
      actual: shell.CoreDigest,
    });
  }

  if (!sameDigestRecord0(shell.PackDigest, sha256Utf8DigestRecord0(shell.PackBytes))) {
    return validationReject0(['PackDigest'], 'PackDigest must be SHA256 over PackBytes', {
      expected: sha256Utf8DigestRecord0(shell.PackBytes),
      actual: shell.PackDigest,
    });
  }

  if (containsAcceptRun0(coreParsed.value)) {
    return validationReject0(['CoreBytes'], 'materialized core bytes must not embed AcceptRun', null);
  }

  if (containsAcceptRun0(packParsed.value.Core ?? null)) {
    return validationReject0(['PackBytes', 'Core'], 'materialized pack Core must not embed AcceptRun', null);
  }

  return validationAccept0({
    kind: 'MaterializedCanonicalBytes0NF',
    coreDigest: shell.CoreDigest,
    packDigest: shell.PackDigest,
  });
}

function parseCanonicalJson0(bytes, path) {
  try {
    return validationAccept0WithValue0(JSON.parse(bytes));
  } catch (error) {
    return validationReject0(path, 'canonical byte string must parse as JSON', {
      error: error.message,
    });
  }
}

function validateCanonicalBytePolicy0(shell) {
  const policy = shell.CanonicalBytePolicy;

  if (!isPlainObject(policy)) {
    return validationReject0(['CanonicalBytePolicy'], 'CanonicalBytePolicy must be an object', {
      actual: typeof policy,
    });
  }

  for (const field of [
    'canonicalJson',
    'fullBytesCompared',
    'digestEqualityIsNotObjectEquality',
    'materializedOutputOnly',
    'generatorUntrusted',
  ]) {
    if (policy[field] !== true) {
      return validationReject0(['CanonicalBytePolicy', field], `CanonicalBytePolicy must certify ${field}`, {
        actual: policy[field],
      });
    }
  }

  return validationAccept0({
    kind: 'MaterializedCanonicalBytePolicy0NF',
  });
}

function validateCheckPlan0(shell) {
  if (!isPlainObject(shell.CheckPlan)) {
    return validationReject0(['CheckPlan'], 'CheckPlan must be an object', {
      actual: typeof shell.CheckPlan,
    });
  }

  if (!Array.isArray(shell.CheckPlan.phases)) {
    return validationReject0(['CheckPlan', 'phases'], 'CheckPlan phases must be an array', {
      actual: typeof shell.CheckPlan.phases,
    });
  }

  for (const phase of MATERIALIZED_PACK_REQUIRED_CHECKS0) {
    if (!shell.CheckPlan.phases.includes(phase)) {
      return validationReject0(['CheckPlan', 'phases', phase], 'CheckPlan is missing a required future check phase', {
        phase,
      });
    }
  }

  if (shell.CheckPlan.firstFailureReplayable !== true) {
    return validationReject0(['CheckPlan', 'firstFailureReplayable'], 'CheckPlan must require replayable first failure', {
      actual: shell.CheckPlan.firstFailureReplayable,
    });
  }

  if (shell.CheckPlan.publicConclusionOnlyAfterAccept !== true) {
    return validationReject0(['CheckPlan', 'publicConclusionOnlyAfterAccept'], 'CheckPlan must require public conclusion only after accept', {
      actual: shell.CheckPlan.publicConclusionOnlyAfterAccept,
    });
  }

  return validationAccept0({
    kind: 'MaterializedCheckPlan0NF',
  });
}

function validatePublicClaimBoundary0(shell) {
  const boundary = shell.PublicClaimBoundary;

  if (!isPlainObject(boundary)) {
    return validationReject0(['PublicClaimBoundary'], 'PublicClaimBoundary must be an object', {
      actual: typeof boundary,
    });
  }

  if (boundary.antecedent !== MATERIALIZED_PACK_PUBLIC_BOUNDARY0.antecedent) {
    return validationReject0(['PublicClaimBoundary', 'antecedent'], 'PublicClaimBoundary antecedent mismatch', {
      expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0.antecedent,
      actual: boundary.antecedent,
    });
  }

  if (boundary.consequent !== MATERIALIZED_PACK_PUBLIC_BOUNDARY0.consequent) {
    return validationReject0(['PublicClaimBoundary', 'consequent'], 'PublicClaimBoundary consequent mismatch', {
      expected: MATERIALIZED_PACK_PUBLIC_BOUNDARY0.consequent,
      actual: boundary.consequent,
    });
  }

  if (boundary.conditional !== true) {
    return validationReject0(['PublicClaimBoundary', 'conditional'], 'PublicClaimBoundary must be conditional', {
      actual: boundary.conditional,
    });
  }

  return validationAccept0({
    kind: 'MaterializedPublicClaimBoundary0NF',
  });
}

function containsAcceptRun0(value) {
  if (value === null || value === undefined) {
    return false;
  }

  if (typeof value === 'string') {
    return value === 'AcceptRun' || value === 'AcceptRun0';
  }

  if (Array.isArray(value)) {
    return value.some((entry) => containsAcceptRun0(entry));
  }

  if (!isPlainObject(value)) {
    return false;
  }

  for (const key of Object.keys(value)) {
    if (key === 'AcceptRun' || key === 'AcceptRun0') {
      return true;
    }

    if (containsAcceptRun0(value[key])) {
      return true;
    }
  }

  return false;
}

function sameDigestRecord0(actual, expected) {
  return (
    isPlainObject(actual) &&
    actual.alg === expected.alg &&
    actual.bytes === expected.bytes &&
    actual.hex === expected.hex
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

function getPiMaterializedShell0(shell) {
  return shell.PiMaterializedShell ?? shell['Πmaterialized'] ?? shell.piMaterializedShell;
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

function validationAccept0WithValue0(value) {
  return {
    ok: true,
    value,
    nf: {
      kind: 'ParsedCanonicalJson0NF',
    },
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
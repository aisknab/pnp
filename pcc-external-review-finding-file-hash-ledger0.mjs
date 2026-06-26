import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckExternalReviewFindingFiles0,
  EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0,
  EXTERNAL_REVIEW_FINDING_FILES_COORDINATE0,
  EXTERNAL_REVIEW_FINDING_FILES_DIRECTORY0,
  makeExternalReviewFindingFilesInput0,
} from './pcc-external-review-finding-files0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

const CHECKER_VERSION = 0;

export const EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_COORDINATE0 =
  'ExternalReview.SignedFindingFileHashes';

export const EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_ENTRIES0 = Object.freeze([
  Object.freeze({
    path: 'external-review/findings/MANIFEST.json',
    sha256:
      '2f8ecf1ca93e6f94db967b7808948e97a330850bda7ee4211defcc151d2e5869',
  }),
  Object.freeze({
    path: 'external-review/findings/README.md',
    sha256:
      '0243c7fe3c77968a5000cfdc471c5c651e9de790285e990464d06518510f4edb',
  }),
]);

export const EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0 = Object.freeze({
  kind: 'ExternalReviewSignedFindingFileHashLedger0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_COORDINATE0,
  predecessorCoordinate: EXTERNAL_REVIEW_FINDING_FILES_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewFindingFiles0',
  findingDirectory: EXTERNAL_REVIEW_FINDING_FILES_DIRECTORY0,
  sha256SumsPath: 'external-review/findings/SHA256SUMS',
  manifestPath: 'external-review/findings/MANIFEST.json',
  readmePath: 'external-review/findings/README.md',
  entries: EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_ENTRIES0,
  entryCount: EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_ENTRIES0.length,
  manifestDigest: digestCanonical0(EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0),
  signedFindingFileCount: 0,
  acceptanceFindingFileCount: 0,
  externalReviewSignedFindingFileHashesReady: true,
  externalReviewSignedFindingFilesReady: false,
  externalReviewSignedFindingsReady: false,
  externalReviewAcceptanceReady: false,
  externalReviewAcceptanceReleased: false,
  externalReviewAcceptanceNotClaimed: true,
  unrestrictedFinalSoundnessReady: false,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
  activeFinalNodeIdsMustRemainEmpty: true,
  sealedReleaseNotOverwritten: true,
});

export const EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_POLICY0 = Object.freeze({
  kind: 'ExternalReviewSignedFindingFileHashLedgerPolicy0',
  version: CHECKER_VERSION,
  requiresFindingFileGateAcceptance: true,
  requiresExactFindingFileHashLedger: true,
  requiresSha256SumsVerification: true,
  requiresEmptyFindingFileIntake: true,
  requiresNoCallerSuppliedAcceptance: true,
  representsFindingFileHashLedgerOnly: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export const EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_CONTRACT0 = Object.freeze({
  kind: 'ExternalReviewSignedFindingFileHashLedgerContract0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewFindingFiles0',
  hashLedgerKind: EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0.kind,
  sha256SumsPath: EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0.sha256SumsPath,
  remainingBlockers: [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ],
  publicTheoremEmissionAllowed: false,
});

export function makeExternalReviewFindingFileHashLedgerSuite0({
  HashLedger = EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0,
} = {}) {
  const base = Object.freeze({
    kind: 'ExternalReviewSignedFindingFileHashLedgerBinding0',
    version: CHECKER_VERSION,
    coordinate: EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_COORDINATE0,
    hashLedgerDigest: digestCanonical0(HashLedger),
    checkerContractDigest:
      digestCanonical0(EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_CONTRACT0),
    policyDigest: digestCanonical0(EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_POLICY0),
  });
  return Object.freeze({
    kind: 'ExternalReviewSignedFindingFileHashLedgerSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.signed-finding-file-hashes.phase48',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_POLICY0 },
  });
}

export function makeExternalReviewFindingFileHashLedgerInput0({
  PredecessorInput = makeExternalReviewFindingFilesInput0(),
  HashLedger = EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0,
  HashLedgerGate = makeExternalReviewFindingFileHashLedgerSuite0({
    HashLedger,
  }),
} = {}) {
  return Object.freeze({
    kind: 'ExternalReviewSignedFindingFileHashLedgerInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    HashLedger,
    HashLedgerGate,
    Policy: { ...EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_POLICY0 },
  });
}

export async function CheckExternalReviewFindingFileHashLedger0(input) {
  const checker = 'CheckExternalReviewFindingFileHashLedger0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckExternalReviewFindingFiles0',
    () => CheckExternalReviewFindingFiles0(input.PredecessorInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckExternalReviewFindingFiles0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.findingFilesPredecessor.exception`,
      path: ['PredecessorInput'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.findingFilesPredecessor`,
      path: ['PredecessorInput'],
      witness: {
        reason: 'finding-file hash ledger requires an accepted finding-file intake predecessor',
        inner: compactRecord0(predecessorCall.record),
      },
      ledger,
    });
  }

  const predecessorNF = predecessorCall.record.NF
    ?? predecessorCall.record.nf
    ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'findingFilesPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.findingFilesPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const hashLedger = validateHashLedger0(input.HashLedger);
  ledger.push(makeLedgerEntry0('hashLedger', hashLedger.ok, hashLedger.nf ?? hashLedger.witness));
  if (!hashLedger.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.hashLedger`,
      hashLedger,
      ledger,
    );
  }

  const suite = validateGateSuite0(input.HashLedgerGate, input.HashLedger);
  ledger.push(makeLedgerEntry0('hashLedgerGateSuite', suite.ok, suite.nf ?? suite.witness));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.hashLedgerGateSuite`,
      suite,
      ledger,
    );
  }

  const remainingBlockers = makeRemainingBlockers0({
    hashLedger: input.HashLedger,
    predecessorDigest: predecessorCall.record.Digest ?? predecessorCall.record.digest,
  });

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'ExternalReviewSignedFindingFileHashLedger0NF',
      checker,
      version: CHECKER_VERSION,
      externalReviewFindingFileHashLedgerReady: true,
      externalReviewSignedFindingFileHashesReady: true,
      externalReviewSignedFindingFilesReady: false,
      externalReviewSignedFindingsReady: false,
      externalReviewAcceptanceReady: false,
      externalReviewAcceptanceReleased: false,
      externalReviewAcceptanceBlocked: true,
      unrestrictedFinalSoundnessReady: false,
      unrestrictedFinalSoundnessBlocked: true,
      findingFilesPredecessorAccepted: true,
      findingFilesPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      hashLedger: input.HashLedger,
      hashLedgerDigest: digestCanonical0(input.HashLedger),
      sha256SumsPath: input.HashLedger.sha256SumsPath,
      hashLedgerEntryCount: input.HashLedger.entryCount,
      signedFindingFileCount: input.HashLedger.signedFindingFileCount,
      acceptanceFindingFileCount: input.HashLedger.acceptanceFindingFileCount,
      gateBinding: input.HashLedgerGate.binding,
      gateBindingDigest: input.HashLedgerGate.binding.bindingDigest,
      remainingBlockers,
      remainingBlockerCoordinates:
        remainingBlockers.map((entry) => entry.coordinate),
      releasePublicTheoremEmissionBlocked: true,
      releasePublicTheoremEmissionBlockerDigest:
        digestCanonical0(remainingBlockers),
      globalSemanticNodeDerivationsReady: true,
      globalFinalDerivationsReady: true,
      publicTheoremEmissionReady: false,
      publicTheoremEmissionAllowed: false,
      finalTheoremReady: false,
      activeFinalNodeIds: [],
      quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
      sealedReleaseNotOverwritten: true,
      externalReviewAcceptanceNotClaimed: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeRemainingBlockers0({ hashLedger, predecessorDigest }) {
  return [
    Object.freeze({
      coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
      ready: false,
      reason: 'unrestricted final soundness remains blocked until independent unrestricted-soundness review is supplied',
      digest: digestCanonical0({
        coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
        predecessorDigest,
      }),
    }),
    Object.freeze({
      coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
      ready: false,
      reason: 'finding-file hash ledger binds an empty intake; no signed acceptance file is supplied',
      hashLedgerDigest: digestCanonical0(hashLedger),
      digest: digestCanonical0({
        coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
        hashLedgerDigest: digestCanonical0(hashLedger),
        predecessorDigest,
      }),
    }),
  ];
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) return validationReject0([], 'finding-file hash ledger input must be an object', { actual: typeof input });
  if (input.kind !== 'ExternalReviewSignedFindingFileHashLedgerInput0') return validationReject0(['kind'], 'finding-file hash ledger input kind must be ExternalReviewSignedFindingFileHashLedgerInput0', { actual: input.kind });
  if (input.version !== CHECKER_VERSION) return validationReject0(['version'], `finding-file hash ledger input version must be ${CHECKER_VERSION}`, { actual: input.version });
  const required = ['PredecessorInput', 'HashLedger', 'HashLedgerGate', 'Policy'];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) return validationReject0([field], 'finding-file hash ledger input is missing a required field', { field });
  }
  for (const field of required.slice(0, -1)) {
    if (!isPlainObject0(input[field])) return validationReject0([field], 'finding-file hash ledger dependency surfaces must be objects', { field, actual: typeof input[field] });
  }
  if (!sameCanonical0(input.Policy, EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_POLICY0)) return validationReject0(['Policy'], 'finding-file hash ledger policy must match the fail-closed policy', { expected: EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER_POLICY0, actual: input.Policy });
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return validationReject0([unexpected[0]], 'finding-file hash ledger checker rejects caller-supplied readiness or truth assertions', { unexpectedFields: unexpected.sort() });
  return validationAccept0({ kind: 'ExternalReviewSignedFindingFileHashLedgerInputShape0NF' });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    externalReviewFindingFileIntakeReady: true,
    externalReviewSignedFindingFilesReady: false,
    externalReviewSignedFindingsReady: false,
    externalReviewAcceptanceReady: false,
    externalReviewAcceptanceReleased: false,
    externalReviewAcceptanceBlocked: true,
    unrestrictedFinalSoundnessReady: false,
    unrestrictedFinalSoundnessBlocked: true,
    publicTheoremEmissionReady: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    releasePublicTheoremEmissionBlocked: true,
    sealedReleaseNotOverwritten: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) return validationReject0(['FindingFilesPredecessor', 'NF', field], 'finding-file predecessor boundary mismatch', { field, expected: value, actual: nf[field] });
  }
  const expectedBlockers = [UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0, EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0];
  if (!sameCanonical0(nf.activeFinalNodeIds, []) || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0) || !sameCanonical0(nf.remainingBlockerCoordinates, expectedBlockers)) {
    return validationReject0(['FindingFilesPredecessor', 'NF', 'remainingBlockerCoordinates'], 'finding-file predecessor must expose only unrestricted-soundness and external-review blockers', { activeFinalNodeIds: nf.activeFinalNodeIds, quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds, remainingBlockerCoordinates: nf.remainingBlockerCoordinates });
  }
  return validationAccept0({ kind: 'ExternalReviewSignedFindingFileHashLedgerPredecessorBoundary0NF', ...expected, remainingBlockerCoordinates: expectedBlockers });
}

function validateHashLedger0(hashLedger) {
  if (!sameCanonical0(hashLedger, EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0)) return validationReject0(['HashLedger'], 'finding-file hash ledger requires the exact empty-intake SHA256 ledger', { expected: EXTERNAL_REVIEW_FINDING_FILE_HASH_LEDGER0, actual: hashLedger });
  return validationAccept0({ kind: 'ExternalReviewSignedFindingFileHashLedger0NF', coordinate: hashLedger.coordinate, entryCount: hashLedger.entryCount, hashLedgerDigest: digestCanonical0(hashLedger) });
}

function validateGateSuite0(suite, hashLedger) {
  if (!isPlainObject0(suite)) return validationReject0(['HashLedgerGate'], 'finding-file hash ledger suite must be an object', { actual: typeof suite });
  const expected = makeExternalReviewFindingFileHashLedgerSuite0({ HashLedger: hashLedger });
  if (!sameCanonical0(suite, expected)) return validationReject0(['HashLedgerGate'], 'finding-file hash ledger suite must exactly match the computed ledger and policy binding', { expected, actual: suite });
  return validationAccept0({ kind: 'ExternalReviewSignedFindingFileHashLedgerSuite0NF', suiteId: suite.suiteId, bindingDigest: suite.binding.bindingDigest });
}

async function callChecker0(name, thunk) {
  try {
    const record = await thunk();
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) return { ok: false, witness: { reason: `${name} did not return a total accept/reject record`, actual: record } };
    return { ok: true, record };
  } catch (error) {
    return { ok: false, witness: { reason: `${name} threw instead of returning a reject record`, errorName: error?.name ?? null, errorMessage: error?.message ?? String(error) } };
  }
}

function compactRecord0(record) {
  return { tag: record?.tag ?? null, checker: record?.checker ?? null, coord: record?.Coord ?? record?.coord ?? null, path: record?.Path ?? record?.path ?? null, witness: record?.Witness ?? record?.witness ?? null, digest: record?.Digest ?? record?.digest ?? null };
}

function makeLedgerEntry0(phase, ok, material) { return { phase, status: ok ? 'pass' : 'fail', digest: digestCanonical0(material ?? null) }; }
function makeAcceptRecord0({ checker, nf, ledger }) { const digest = digestCanonical0(nf); return { tag: 'accept', kind: 'accept', checker, version: CHECKER_VERSION, NF: nf, Digest: digest, Ledger: ledger, nf, digest, ledger }; }
function makeRejectFromValidation0(checker, coord, result, ledger) { return makeRejectRecord0({ checker, coord, path: result.path, witness: result.witness, ledger }); }
function makeRejectRecord0({ checker, coord, path, witness, ledger }) { const nf = { kind: `${checker}RejectNF`, checker, version: CHECKER_VERSION, coord, path, witness, ledger }; const digest = digestCanonical0(nf); return { tag: 'reject', kind: 'reject', checker, version: CHECKER_VERSION, Coord: coord, Path: path, Witness: witness, Digest: digest, Ledger: ledger, coord, path, witness, digest, ledger }; }
function validationAccept0(nf) { return { ok: true, nf }; }
function validationReject0(path, reason, details = {}) { return { ok: false, path, witness: { reason, ...(details ?? {}) } }; }
function sameCanonical0(left, right) { return stableStringify0(left) === stableStringify0(right); }
function isPlainObject0(value) { if (value === null || typeof value !== 'object' || Array.isArray(value)) return false; const prototype = Object.getPrototypeOf(value); return prototype === Object.prototype || prototype === null; }

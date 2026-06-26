import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckSignedExternalReviewFindings0,
  SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0,
  SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0,
  SIGNED_EXTERNAL_REVIEW_FINDINGS_COORDINATE0,
  makeSignedExternalReviewFindingsInput0,
} from './pcc-external-review-signed-findings0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

const CHECKER_VERSION = 0;

export const EXTERNAL_REVIEW_FINDING_FILES_COORDINATE0 =
  'ExternalReview.SignedFindingFiles';

export const EXTERNAL_REVIEW_FINDING_FILES_DIRECTORY0 =
  'external-review/findings/';

export const EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0 = Object.freeze({
  kind: 'ExternalReviewSignedFindingFileManifest0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_FINDING_FILES_COORDINATE0,
  predecessorCoordinate: SIGNED_EXTERNAL_REVIEW_FINDINGS_COORDINATE0,
  predecessorChecker: 'CheckSignedExternalReviewFindings0',
  findingDirectory: EXTERNAL_REVIEW_FINDING_FILES_DIRECTORY0,
  manifestPath: 'external-review/findings/MANIFEST.json',
  readmePath: 'external-review/findings/README.md',
  acceptedFileExtensions: Object.freeze(['.json', '.json.asc', '.minisig']),
  requiredPerFindingFields:
    [...SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0.requiredFindingFields],
  signedFindingFileCount: 0,
  acceptanceFindingFileCount: 0,
  rejectionFindingFileCount: 0,
  revisionRequestFindingFileCount: 0,
  signedFindingFiles: Object.freeze([]),
  predecessorBundleDigest: digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDINGS_BUNDLE0),
  schemaDigest: digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0),
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

export const EXTERNAL_REVIEW_FINDING_FILES_POLICY0 = Object.freeze({
  kind: 'ExternalReviewSignedFindingFilesPolicy0',
  version: CHECKER_VERSION,
  requiresSignedFindingsGateAcceptance: true,
  requiresExactEmptyFindingFileManifest: true,
  requiresNoFindingFileAcceptanceWithoutDigestBoundFile: true,
  requiresNoCallerSuppliedAcceptance: true,
  representsFindingFileIntakeOnly: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export const EXTERNAL_REVIEW_FINDING_FILES_CONTRACT0 = Object.freeze({
  kind: 'ExternalReviewSignedFindingFilesContract0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_FINDING_FILES_COORDINATE0,
  predecessorChecker: 'CheckSignedExternalReviewFindings0',
  manifestKind: EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0.kind,
  findingDirectory: EXTERNAL_REVIEW_FINDING_FILES_DIRECTORY0,
  remainingBlockers: [
    UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
    EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  ],
  publicTheoremEmissionAllowed: false,
});

export function makeExternalReviewFindingFilesSuite0({
  FindingFileManifest = EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0,
} = {}) {
  const base = Object.freeze({
    kind: 'ExternalReviewSignedFindingFilesBinding0',
    version: CHECKER_VERSION,
    coordinate: EXTERNAL_REVIEW_FINDING_FILES_COORDINATE0,
    findingFileManifestDigest: digestCanonical0(FindingFileManifest),
    checkerContractDigest:
      digestCanonical0(EXTERNAL_REVIEW_FINDING_FILES_CONTRACT0),
    policyDigest: digestCanonical0(EXTERNAL_REVIEW_FINDING_FILES_POLICY0),
  });
  return Object.freeze({
    kind: 'ExternalReviewSignedFindingFilesSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.signed-finding-files.phase47',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...EXTERNAL_REVIEW_FINDING_FILES_POLICY0 },
  });
}

export function makeExternalReviewFindingFilesInput0({
  PredecessorInput = makeSignedExternalReviewFindingsInput0(),
  FindingFileManifest = EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0,
  FindingFilesGate = makeExternalReviewFindingFilesSuite0({
    FindingFileManifest,
  }),
} = {}) {
  return Object.freeze({
    kind: 'ExternalReviewSignedFindingFilesInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    FindingFileManifest,
    FindingFilesGate,
    Policy: { ...EXTERNAL_REVIEW_FINDING_FILES_POLICY0 },
  });
}

export async function CheckExternalReviewFindingFiles0(input) {
  const checker = 'CheckExternalReviewFindingFiles0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckSignedExternalReviewFindings0',
    () => CheckSignedExternalReviewFindings0(input.PredecessorInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckSignedExternalReviewFindings0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.signedFindingsPredecessor.exception`,
      path: ['PredecessorInput'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.signedFindingsPredecessor`,
      path: ['PredecessorInput'],
      witness: {
        reason: 'finding-file intake gate requires an accepted signed-findings predecessor',
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
    'signedFindingsPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.signedFindingsPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const manifest = validateFindingFileManifest0(input.FindingFileManifest);
  ledger.push(makeLedgerEntry0(
    'findingFileManifest',
    manifest.ok,
    manifest.nf ?? manifest.witness,
  ));
  if (!manifest.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.findingFileManifest`,
      manifest,
      ledger,
    );
  }

  const suite = validateGateSuite0(input.FindingFilesGate, input.FindingFileManifest);
  ledger.push(makeLedgerEntry0(
    'findingFilesGateSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.findingFilesGateSuite`,
      suite,
      ledger,
    );
  }

  const remainingBlockers = [
    Object.freeze({
      coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
      ready: false,
      reason: 'unrestricted final soundness remains blocked until independent unrestricted-soundness review is supplied',
      digest: digestCanonical0({
        coordinate: UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
        predecessorDigest:
          predecessorCall.record.Digest ?? predecessorCall.record.digest,
      }),
    }),
    Object.freeze({
      coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
      ready: false,
      reason: 'signed finding-file manifest is empty; no signed acceptance file is supplied',
      findingFileManifestDigest: digestCanonical0(input.FindingFileManifest),
      digest: digestCanonical0({
        coordinate: EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
        findingFileManifestDigest: digestCanonical0(input.FindingFileManifest),
        predecessorDigest:
          predecessorCall.record.Digest ?? predecessorCall.record.digest,
      }),
    }),
  ];

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'ExternalReviewSignedFindingFiles0NF',
      checker,
      version: CHECKER_VERSION,
      externalReviewFindingFileIntakeReady: true,
      externalReviewSignedFindingFilesReady: false,
      externalReviewSignedFindingsReady: false,
      externalReviewAcceptanceReady: false,
      externalReviewAcceptanceReleased: false,
      externalReviewAcceptanceBlocked: true,
      unrestrictedFinalSoundnessReady: false,
      unrestrictedFinalSoundnessBlocked: true,
      signedFindingsPredecessorAccepted: true,
      signedFindingsPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      findingFileManifest: input.FindingFileManifest,
      findingFileManifestDigest: digestCanonical0(input.FindingFileManifest),
      signedFindingFileCount: input.FindingFileManifest.signedFindingFileCount,
      acceptanceFindingFileCount: input.FindingFileManifest.acceptanceFindingFileCount,
      gateBinding: input.FindingFilesGate.binding,
      gateBindingDigest: input.FindingFilesGate.binding.bindingDigest,
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

function validateInputShape0(input) {
  if (!isPlainObject0(input)) return validationReject0([], 'signed finding-file input must be an object', { actual: typeof input });
  if (input.kind !== 'ExternalReviewSignedFindingFilesInput0') return validationReject0(['kind'], 'signed finding-file input kind must be ExternalReviewSignedFindingFilesInput0', { actual: input.kind });
  if (input.version !== CHECKER_VERSION) return validationReject0(['version'], `signed finding-file input version must be ${CHECKER_VERSION}`, { actual: input.version });
  const required = ['PredecessorInput', 'FindingFileManifest', 'FindingFilesGate', 'Policy'];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) return validationReject0([field], 'signed finding-file input is missing a required field', { field });
  }
  for (const field of required.slice(0, -1)) {
    if (!isPlainObject0(input[field])) return validationReject0([field], 'signed finding-file dependency surfaces must be objects', { field, actual: typeof input[field] });
  }
  if (!sameCanonical0(input.Policy, EXTERNAL_REVIEW_FINDING_FILES_POLICY0)) return validationReject0(['Policy'], 'signed finding-file policy must match the fail-closed policy', { expected: EXTERNAL_REVIEW_FINDING_FILES_POLICY0, actual: input.Policy });
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return validationReject0([unexpected[0]], 'signed finding-file checker rejects caller-supplied readiness or truth assertions', { unexpectedFields: unexpected.sort() });
  return validationAccept0({ kind: 'ExternalReviewSignedFindingFilesInputShape0NF' });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    signedExternalReviewFindingsGateReady: true,
    signedExternalReviewFindingsBundleReady: true,
    signedExternalReviewFindingsReady: false,
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
    if (nf[field] !== value) return validationReject0(['SignedFindingsPredecessor', 'NF', field], 'signed-findings predecessor boundary mismatch', { field, expected: value, actual: nf[field] });
  }
  const expectedBlockers = [UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0, EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0];
  if (!sameCanonical0(nf.activeFinalNodeIds, []) || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0) || !sameCanonical0(nf.remainingBlockerCoordinates, expectedBlockers)) {
    return validationReject0(['SignedFindingsPredecessor', 'NF', 'remainingBlockerCoordinates'], 'signed-findings predecessor must expose only unrestricted-soundness and external-review blockers', { activeFinalNodeIds: nf.activeFinalNodeIds, quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds, remainingBlockerCoordinates: nf.remainingBlockerCoordinates });
  }
  return validationAccept0({ kind: 'ExternalReviewSignedFindingFilesPredecessorBoundary0NF', ...expected, remainingBlockerCoordinates: expectedBlockers });
}

function validateFindingFileManifest0(manifest) {
  if (!sameCanonical0(manifest, EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0)) {
    return validationReject0(['FindingFileManifest'], 'signed finding-file checker requires the exact empty finding-file manifest', { expected: EXTERNAL_REVIEW_FINDING_FILE_MANIFEST0, actual: manifest });
  }
  return validationAccept0({ kind: 'ExternalReviewSignedFindingFileManifest0NF', coordinate: manifest.coordinate, signedFindingFileCount: manifest.signedFindingFileCount, manifestDigest: digestCanonical0(manifest) });
}

function validateGateSuite0(suite, findingFileManifest) {
  if (!isPlainObject0(suite)) return validationReject0(['FindingFilesGate'], 'signed finding-file gate suite must be an object', { actual: typeof suite });
  const expected = makeExternalReviewFindingFilesSuite0({ FindingFileManifest: findingFileManifest });
  if (!sameCanonical0(suite, expected)) return validationReject0(['FindingFilesGate'], 'signed finding-file gate suite must exactly match the computed manifest and policy binding', { expected, actual: suite });
  return validationAccept0({ kind: 'ExternalReviewSignedFindingFilesSuite0NF', suiteId: suite.suiteId, bindingDigest: suite.binding.bindingDigest });
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

function makeLedgerEntry0(phase, ok, material) {
  return { phase, status: ok ? 'pass' : 'fail', digest: digestCanonical0(material ?? null) };
}

function makeAcceptRecord0({ checker, nf, ledger }) {
  const digest = digestCanonical0(nf);
  return { tag: 'accept', kind: 'accept', checker, version: CHECKER_VERSION, NF: nf, Digest: digest, Ledger: ledger, nf, digest, ledger };
}

function makeRejectFromValidation0(checker, coord, result, ledger) {
  return makeRejectRecord0({ checker, coord, path: result.path, witness: result.witness, ledger });
}

function makeRejectRecord0({ checker, coord, path, witness, ledger }) {
  const nf = { kind: `${checker}RejectNF`, checker, version: CHECKER_VERSION, coord, path, witness, ledger };
  const digest = digestCanonical0(nf);
  return { tag: 'reject', kind: 'reject', checker, version: CHECKER_VERSION, Coord: coord, Path: path, Witness: witness, Digest: digest, Ledger: ledger, coord, path, witness, digest, ledger };
}

function validationAccept0(nf) { return { ok: true, nf }; }
function validationReject0(path, reason, details = {}) { return { ok: false, path, witness: { reason, ...(details ?? {}) } }; }
function sameCanonical0(left, right) { return stableStringify0(left) === stableStringify0(right); }
function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

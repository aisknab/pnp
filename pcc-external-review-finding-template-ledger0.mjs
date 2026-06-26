import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckExternalReviewFindingFileHashLedger0,
  makeExternalReviewFindingFileHashLedgerInput0,
} from './pcc-external-review-finding-file-hash-ledger0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

import {
  SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0,
} from './pcc-external-review-signed-findings0.mjs';

const CHECKER_VERSION = 0;

export const EXTERNAL_REVIEW_FINDING_TEMPLATES_COORDINATE0 =
  'ExternalReview.SignedFindingTemplates';

export const EXTERNAL_REVIEW_FINDING_TEMPLATE_ENTRIES0 = Object.freeze([
  Object.freeze({
    path: 'external-review/templates/acceptance-finding.template.json',
    kind: 'ExternalReviewAcceptanceFinding0',
    finding: 'accept',
    sha256:
      '110d35baea012ebf8bbef17314bb289ca949edfa03f8fa7346f7a68232348f14',
  }),
  Object.freeze({
    path: 'external-review/templates/rejection-finding.template.json',
    kind: 'ExternalReviewRejectionFinding0',
    finding: 'reject',
    sha256:
      'f97527a3ab8660d961707ecdfe8f39a90a9d3ad2bb758a872903f62172ac706e',
  }),
  Object.freeze({
    path: 'external-review/templates/revision-request-finding.template.json',
    kind: 'ExternalReviewRevisionRequestFinding0',
    finding: 'revision-request',
    sha256:
      '9d702f97d85502e271716c444eda47fcf662db57c09d210bd4788074747c0aa3',
  }),
]);

export const EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0 = Object.freeze({
  kind: 'ExternalReviewSignedFindingTemplateLedger0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_FINDING_TEMPLATES_COORDINATE0,
  predecessorCoordinate: 'ExternalReview.SignedFindingFileHashes',
  predecessorChecker: 'CheckExternalReviewFindingFileHashLedger0',
  templateDirectory: 'external-review/templates/',
  sha256SumsPath: 'external-review/templates/SHA256SUMS',
  entries: EXTERNAL_REVIEW_FINDING_TEMPLATE_ENTRIES0,
  entryCount: EXTERNAL_REVIEW_FINDING_TEMPLATE_ENTRIES0.length,
  signedFindingSchemaDigest:
    digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0),
  templateLedgerReady: true,
  signedFindingFileCount: 0,
  acceptanceFindingFileCount: 0,
  externalReviewSignedFindingTemplatesReady: true,
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

export const EXTERNAL_REVIEW_FINDING_TEMPLATE_POLICY0 = Object.freeze({
  kind: 'ExternalReviewSignedFindingTemplatePolicy0',
  version: CHECKER_VERSION,
  requiresFindingFileHashLedgerAcceptance: true,
  requiresTemplateSha256SumsVerification: true,
  requiresExactTemplateLedger: true,
  requiresNoTemplateToActAsFinding: true,
  representsTemplatesOnly: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export function makeExternalReviewFindingTemplateSuite0({
  TemplateLedger = EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0,
} = {}) {
  const base = Object.freeze({
    kind: 'ExternalReviewSignedFindingTemplateBinding0',
    version: CHECKER_VERSION,
    coordinate: EXTERNAL_REVIEW_FINDING_TEMPLATES_COORDINATE0,
    templateLedgerDigest: digestCanonical0(TemplateLedger),
    policyDigest: digestCanonical0(EXTERNAL_REVIEW_FINDING_TEMPLATE_POLICY0),
  });
  return Object.freeze({
    kind: 'ExternalReviewSignedFindingTemplateSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.signed-finding-templates.phase49',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...EXTERNAL_REVIEW_FINDING_TEMPLATE_POLICY0 },
  });
}

export function makeExternalReviewFindingTemplateInput0({
  PredecessorInput = makeExternalReviewFindingFileHashLedgerInput0(),
  TemplateLedger = EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0,
  TemplateGate = makeExternalReviewFindingTemplateSuite0({ TemplateLedger }),
} = {}) {
  return Object.freeze({
    kind: 'ExternalReviewSignedFindingTemplateInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    TemplateLedger,
    TemplateGate,
    Policy: { ...EXTERNAL_REVIEW_FINDING_TEMPLATE_POLICY0 },
  });
}

export async function CheckExternalReviewFindingTemplateLedger0(input) {
  const checker = 'CheckExternalReviewFindingTemplateLedger0';
  const shape = validateInputShape0(input);
  if (!shape.ok) return makeRejectRecord0(checker, `${checker}.input`, shape.path, shape.witness, []);
  const ledgerResult = validateTemplateLedger0(input.TemplateLedger);
  if (!ledgerResult.ok) return makeRejectRecord0(checker, `${checker}.templateLedger`, ledgerResult.path, ledgerResult.witness, []);
  const suiteResult = validateGateSuite0(input.TemplateGate, input.TemplateLedger);
  if (!suiteResult.ok) return makeRejectRecord0(checker, `${checker}.templateGate`, suiteResult.path, suiteResult.witness, []);

  const predecessor = await callChecker0(
    'CheckExternalReviewFindingFileHashLedger0',
    () => CheckExternalReviewFindingFileHashLedger0(input.PredecessorInput),
  );
  if (!predecessor.ok || predecessor.record.tag !== 'accept') {
    return makeRejectRecord0(checker, `${checker}.predecessor`, ['PredecessorInput'], {
      reason: 'finding-template ledger requires an accepted finding-file hash-ledger predecessor',
      inner: predecessor.ok ? compactRecord0(predecessor.record) : predecessor.witness,
    }, []);
  }

  const remainingBlockers = [
    blocker0(UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0, 'unrestricted final soundness remains blocked'),
    blocker0(EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0, 'template files are not signed findings and cannot supply external-review acceptance'),
  ];
  return makeAcceptRecord0(checker, {
    kind: 'ExternalReviewSignedFindingTemplateLedger0NF',
    checker,
    version: CHECKER_VERSION,
    externalReviewSignedFindingTemplatesReady: true,
    externalReviewSignedFindingFilesReady: false,
    externalReviewSignedFindingsReady: false,
    externalReviewAcceptanceReady: false,
    externalReviewAcceptanceBlocked: true,
    unrestrictedFinalSoundnessReady: false,
    templateLedger: input.TemplateLedger,
    templateLedgerDigest: digestCanonical0(input.TemplateLedger),
    templateEntryCount: input.TemplateLedger.entryCount,
    remainingBlockers,
    remainingBlockerCoordinates: remainingBlockers.map((entry) => entry.coordinate),
    publicTheoremEmissionReady: false,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    activeFinalNodeIds: [],
    quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    sealedReleaseNotOverwritten: true,
    externalReviewAcceptanceNotClaimed: true,
    policyDigest: digestCanonical0(input.Policy),
  }, []);
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) return reject0([], 'finding-template input must be an object');
  if (input.kind !== 'ExternalReviewSignedFindingTemplateInput0') return reject0(['kind'], 'finding-template input kind mismatch');
  const required = ['PredecessorInput', 'TemplateLedger', 'TemplateGate', 'Policy'];
  for (const field of required) if (!Object.hasOwn(input, field)) return reject0([field], 'finding-template input is missing a required field');
  if (!sameCanonical0(input.Policy, EXTERNAL_REVIEW_FINDING_TEMPLATE_POLICY0)) return reject0(['Policy'], 'finding-template policy mismatch');
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return reject0([unexpected[0]], 'finding-template checker rejects caller-supplied readiness or truth assertions');
  return { ok: true };
}

function validateTemplateLedger0(ledger) {
  if (!sameCanonical0(ledger, EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0)) return reject0(['TemplateLedger'], 'finding-template ledger requires the exact template checksum ledger');
  return { ok: true };
}

function validateGateSuite0(suite, templateLedger) {
  const expected = makeExternalReviewFindingTemplateSuite0({ TemplateLedger: templateLedger });
  if (!sameCanonical0(suite, expected)) return reject0(['TemplateGate'], 'finding-template gate suite must match the computed ledger binding');
  return { ok: true };
}

async function callChecker0(name, thunk) {
  try {
    const record = await thunk();
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) return { ok: false, witness: { reason: `${name} returned a non-total record`, actual: record } };
    return { ok: true, record };
  } catch (error) {
    return { ok: false, witness: { reason: `${name} threw`, errorName: error?.name ?? null, errorMessage: error?.message ?? String(error) } };
  }
}

function blocker0(coordinate, reason) {
  return Object.freeze({ coordinate, ready: false, reason, digest: digestCanonical0({ coordinate, reason }) });
}

function compactRecord0(record) {
  return { tag: record?.tag ?? null, checker: record?.checker ?? null, coord: record?.Coord ?? record?.coord ?? null, digest: record?.Digest ?? record?.digest ?? null };
}

function makeAcceptRecord0(checker, nf, ledger) {
  const digest = digestCanonical0(nf);
  return { tag: 'accept', kind: 'accept', checker, version: CHECKER_VERSION, NF: nf, Digest: digest, Ledger: ledger, nf, digest, ledger };
}

function makeRejectRecord0(checker, coord, path, witness, ledger) {
  const nf = { kind: `${checker}RejectNF`, checker, version: CHECKER_VERSION, coord, path, witness, ledger };
  const digest = digestCanonical0(nf);
  return { tag: 'reject', kind: 'reject', checker, version: CHECKER_VERSION, Coord: coord, Path: path, Witness: witness, Digest: digest, Ledger: ledger, coord, path, witness, digest, ledger };
}

function reject0(path, reason) { return { ok: false, path, witness: { reason } }; }
function sameCanonical0(left, right) { return stableStringify0(left) === stableStringify0(right); }
function isPlainObject0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }

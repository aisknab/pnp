import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckExternalReviewFindingTemplateLedger0,
  EXTERNAL_REVIEW_FINDING_TEMPLATE_ENTRIES0,
  EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0,
  EXTERNAL_REVIEW_FINDING_TEMPLATES_COORDINATE0,
  makeExternalReviewFindingTemplateInput0,
} from './pcc-external-review-finding-template-ledger0.mjs';

import {
  SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0,
} from './pcc-external-review-signed-findings0.mjs';

import {
  EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
  UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
} from './pcc-unrestricted-final-soundness-gate0.mjs';

const CHECKER_VERSION = 0;
const HEX_PLACEHOLDER = '<64 lowercase hex characters>';

export const EXTERNAL_REVIEW_TEMPLATE_SHAPE_COORDINATE0 =
  'ExternalReview.SignedFindingTemplateShapes';

export const EXTERNAL_REVIEW_TEMPLATE_REQUIRED_DIGEST_FIELDS0 = Object.freeze([
  'reviewerIdentityDigest',
  'reviewScopeDigest',
  'findingDigest',
  'signatureDigest',
]);

export const EXTERNAL_REVIEW_TEMPLATE_SHAPE_ENTRIES0 = Object.freeze(
  EXTERNAL_REVIEW_FINDING_TEMPLATE_ENTRIES0.map((entry) => Object.freeze({
    path: entry.path,
    kind: entry.kind,
    finding: entry.finding,
    version: CHECKER_VERSION,
    documentationCoordinate: 'PNP-DOC-CPR-2026-06-26-01',
    sealedSourceCommit: '7072f8d0bda6d44d240f9bb3fad624fd357e1278',
    sealedArtifactTag:
      'final-pnp-proof-report-artifacts-hardened-7072f8d-sealed',
    requiredDigestFields: [...EXTERNAL_REVIEW_TEMPLATE_REQUIRED_DIGEST_FIELDS0],
    digestAlg: 'SHA256',
    digestHexPlaceholder: HEX_PLACEHOLDER,
    inertTemplateOnly: true,
    signedFindingSupplied: false,
    sha256: entry.sha256,
  })),
);

export const EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0 = Object.freeze({
  kind: 'ExternalReviewSignedFindingTemplateShapeLedger0',
  version: CHECKER_VERSION,
  coordinate: EXTERNAL_REVIEW_TEMPLATE_SHAPE_COORDINATE0,
  predecessorCoordinate: EXTERNAL_REVIEW_FINDING_TEMPLATES_COORDINATE0,
  predecessorChecker: 'CheckExternalReviewFindingTemplateLedger0',
  templateLedgerDigest: digestCanonical0(EXTERNAL_REVIEW_FINDING_TEMPLATE_LEDGER0),
  signedFindingSchemaDigest:
    digestCanonical0(SIGNED_EXTERNAL_REVIEW_FINDING_SCHEMA0),
  entries: EXTERNAL_REVIEW_TEMPLATE_SHAPE_ENTRIES0,
  entryCount: EXTERNAL_REVIEW_TEMPLATE_SHAPE_ENTRIES0.length,
  templateShapeLedgerReady: true,
  externalReviewSignedFindingTemplatesReady: true,
  externalReviewSignedFindingTemplateShapesReady: true,
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

export const EXTERNAL_REVIEW_TEMPLATE_SHAPE_POLICY0 = Object.freeze({
  kind: 'ExternalReviewSignedFindingTemplateShapePolicy0',
  version: CHECKER_VERSION,
  requiresTemplateLedgerAcceptance: true,
  requiresExactTemplateShapeLedger: true,
  requiresTemplatePlaceholderDigests: true,
  requiresTemplatesRemainInert: true,
  requiresNoTemplateToActAsFinding: true,
  dischargesExternalReviewAcceptance: false,
  leavesExternalReviewAcceptanceBlocked: true,
  leavesUnrestrictedFinalSoundnessBlocked: true,
  publicTheoremEmissionAllowed: false,
  callerReadinessAssertionsForbidden: true,
});

export function makeExternalReviewTemplateShapeSuite0({
  TemplateShapeLedger = EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0,
} = {}) {
  const base = Object.freeze({
    kind: 'ExternalReviewSignedFindingTemplateShapeBinding0',
    version: CHECKER_VERSION,
    coordinate: EXTERNAL_REVIEW_TEMPLATE_SHAPE_COORDINATE0,
    templateShapeLedgerDigest: digestCanonical0(TemplateShapeLedger),
    policyDigest: digestCanonical0(EXTERNAL_REVIEW_TEMPLATE_SHAPE_POLICY0),
  });
  return Object.freeze({
    kind: 'ExternalReviewSignedFindingTemplateShapeSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Release.external-review.signed-finding-template-shapes.phase50',
    binding: Object.freeze({
      ...base,
      bindingDigest: digestCanonical0(base),
    }),
    Policy: { ...EXTERNAL_REVIEW_TEMPLATE_SHAPE_POLICY0 },
  });
}

export function makeExternalReviewTemplateShapeInput0({
  PredecessorInput = makeExternalReviewFindingTemplateInput0(),
  TemplateShapeLedger = EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0,
  TemplateShapeGate = makeExternalReviewTemplateShapeSuite0({
    TemplateShapeLedger,
  }),
} = {}) {
  return Object.freeze({
    kind: 'ExternalReviewSignedFindingTemplateShapeInput0',
    version: CHECKER_VERSION,
    PredecessorInput,
    TemplateShapeLedger,
    TemplateShapeGate,
    Policy: { ...EXTERNAL_REVIEW_TEMPLATE_SHAPE_POLICY0 },
  });
}

export async function CheckExternalReviewTemplateShape0(input) {
  const checker = 'CheckExternalReviewTemplateShape0';
  const shape = validateInputShape0(input);
  if (!shape.ok) {
    return reject0(checker, `${checker}.input`, shape.path, shape.witness);
  }
  const ledger = validateTemplateShapeLedger0(input.TemplateShapeLedger);
  if (!ledger.ok) {
    return reject0(checker, `${checker}.templateShapeLedger`, ledger.path, ledger.witness);
  }
  const suite = validateGateSuite0(input.TemplateShapeGate, input.TemplateShapeLedger);
  if (!suite.ok) {
    return reject0(checker, `${checker}.templateShapeGate`, suite.path, suite.witness);
  }

  const predecessor = await callChecker0(
    'CheckExternalReviewFindingTemplateLedger0',
    () => CheckExternalReviewFindingTemplateLedger0(input.PredecessorInput),
  );
  if (!predecessor.ok || predecessor.record.tag !== 'accept') {
    return reject0(checker, `${checker}.predecessor`, ['PredecessorInput'], {
      reason: 'template-shape ledger requires an accepted template-ledger predecessor',
      inner: predecessor.ok ? compactRecord0(predecessor.record) : predecessor.witness,
    });
  }

  const remainingBlockers = [
    blocker0(
      UNRESTRICTED_FINAL_SOUNDNESS_COORDINATE0,
      'unrestricted final soundness remains blocked',
    ),
    blocker0(
      EXTERNAL_REVIEW_ACCEPTANCE_COORDINATE0,
      'template shape validation does not supply signed external-review acceptance',
    ),
  ];
  const nf = {
    kind: 'ExternalReviewSignedFindingTemplateShape0NF',
    checker,
    version: CHECKER_VERSION,
    externalReviewSignedFindingTemplatesReady: true,
    externalReviewSignedFindingTemplateShapesReady: true,
    externalReviewSignedFindingFilesReady: false,
    externalReviewSignedFindingsReady: false,
    externalReviewAcceptanceReady: false,
    externalReviewAcceptanceBlocked: true,
    unrestrictedFinalSoundnessReady: false,
    templateShapeLedger: input.TemplateShapeLedger,
    templateShapeLedgerDigest: digestCanonical0(input.TemplateShapeLedger),
    templateShapeEntryCount: input.TemplateShapeLedger.entryCount,
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
  };
  const digest = digestCanonical0(nf);
  return {
    tag: 'accept',
    kind: 'accept',
    checker,
    version: CHECKER_VERSION,
    NF: nf,
    Digest: digest,
    nf,
    digest,
  };
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) return validationReject0([], 'template-shape input must be an object');
  if (input.kind !== 'ExternalReviewSignedFindingTemplateShapeInput0') return validationReject0(['kind'], 'template-shape input kind mismatch');
  if (input.version !== CHECKER_VERSION) return validationReject0(['version'], 'template-shape input version mismatch');
  const required = ['PredecessorInput', 'TemplateShapeLedger', 'TemplateShapeGate', 'Policy'];
  for (const field of required) {
    if (!Object.hasOwn(input, field)) return validationReject0([field], 'template-shape input is missing a required field');
  }
  if (!sameCanonical0(input.Policy, EXTERNAL_REVIEW_TEMPLATE_SHAPE_POLICY0)) return validationReject0(['Policy'], 'template-shape policy mismatch');
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return validationReject0([unexpected[0]], 'template-shape checker rejects caller-supplied readiness or truth assertions');
  return { ok: true };
}

function validateTemplateShapeLedger0(ledger) {
  if (!sameCanonical0(ledger, EXTERNAL_REVIEW_TEMPLATE_SHAPE_LEDGER0)) return validationReject0(['TemplateShapeLedger'], 'template-shape checker requires the exact inert template-shape ledger');
  return { ok: true };
}

function validateGateSuite0(suite, templateShapeLedger) {
  const expected = makeExternalReviewTemplateShapeSuite0({
    TemplateShapeLedger: templateShapeLedger,
  });
  if (!sameCanonical0(suite, expected)) return validationReject0(['TemplateShapeGate'], 'template-shape gate suite must match the computed shape-ledger binding');
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

function reject0(checker, coord, path, witness) {
  const nf = { kind: `${checker}RejectNF`, checker, version: CHECKER_VERSION, coord, path, witness };
  const digest = digestCanonical0(nf);
  return { tag: 'reject', kind: 'reject', checker, version: CHECKER_VERSION, Coord: coord, Path: path, Witness: witness, Digest: digest, coord, path, witness, digest };
}

function validationReject0(path, reason) { return { ok: false, path, witness: { reason } }; }
function sameCanonical0(left, right) { return stableStringify0(left) === stableStringify0(right); }
function isPlainObject0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }

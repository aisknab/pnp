import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0,
} from './pcc-global-proof-dag0.mjs';

import {
  KERNEL_RULES0,
  SIGMA_REQUIRED_THEOREMS0,
} from './pcc-kimpl0.mjs';

const CHECKER_VERSION = 0;

export const PNP_MINIMAL_KERNEL_COORDINATE0 = 'PNP-MINIMAL-KERNEL-2026-06-27-01';

export const MINIMAL_KERNEL_REMAINING_BLOCKERS0 = Object.freeze([
  'Release.UnrestrictedFinalSoundness',
  'ExternalReview.Acceptance',
]);

export const MINIMAL_KERNEL_REQUIRED_CHECKERS0 = Object.freeze([
  'CheckVerifierFrag0',
  'CheckKImpl0',
  'CheckGlobalProofDAG0',
  'CheckGPack0',
  'CheckFinalFrameworkMatch0',
  'CheckSATDecision0',
  'CheckSATBounds0',
  'CheckPCCPackexp0',
  'CheckFinalPNPProofReport0',
  'CheckSuccessorPublicReviewReportSeal0',
  'audit-report-theorem-bindings0',
]);

export const MINIMAL_KERNEL_REQUIRED_SPINE_IDS0 = Object.freeze([
  'spine.kernel-rules',
  'spine.direct-wire-semantics',
  'spine.residual-band-minimization',
  'spine.locked-nand-sat-threshold',
  'spine.complexity-implication',
  'spine.package-acceptance',
  'spine.report-and-release-boundary',
]);

const MINIMAL_KERNEL_CHECKER_SURFACE0 = Object.freeze([
  Object.freeze({
    id: 'CheckVerifierFrag0',
    file: 'pcc-verifier-frag0.mjs',
    role: 'canonical JSON digesting and finite audit-case harness',
    minimumKernelRole: 'canonicalization-digest-entrypoint',
  }),
  Object.freeze({
    id: 'CheckKImpl0',
    file: 'pcc-kimpl0.mjs',
    role: 'PCC-K primitive rule table, Sigma registry, reflection registry, and bounded proof-node checks',
    minimumKernelRole: 'primitive-rule-and-schema-entrypoint',
  }),
  Object.freeze({
    id: 'CheckGlobalProofDAG0',
    file: 'pcc-global-proof-dag0.mjs',
    role: 'global dependency DAG, required package-theorem nodes, final nodes, imports, and no-min policy',
    minimumKernelRole: 'proof-spine-dependency-entrypoint',
  }),
  Object.freeze({
    id: 'CheckGPack0',
    file: 'pcc-gpack0.mjs',
    role: 'locked NAND construction package and threshold certificate surface',
    minimumKernelRole: 'sat-reduction-entrypoint',
  }),
  Object.freeze({
    id: 'CheckFinalFrameworkMatch0',
    file: 'pcc-final-framework0.mjs',
    role: 'framework compatibility between residual-band minimizer and locked NAND reduction',
    minimumKernelRole: 'cross-framework-interface-entrypoint',
  }),
  Object.freeze({
    id: 'CheckSATDecision0',
    file: 'pcc-global-final-sat-reduction-semantic0.mjs',
    role: 'SAT decision and locked-threshold semantic surface',
    minimumKernelRole: 'sat-threshold-decision-entrypoint',
  }),
  Object.freeze({
    id: 'CheckSATBounds0',
    file: 'pcc-global-final-complexity-semantic0.mjs',
    role: 'polynomial-bound and SAT-in-P to P=NP implication surface',
    minimumKernelRole: 'complexity-implication-entrypoint',
  }),
  Object.freeze({
    id: 'CheckPCCPackexp0',
    file: 'pcc-check-pcc-pack-exp0.mjs',
    role: 'top-level generated package checker surface',
    minimumKernelRole: 'accepted-package-entrypoint',
  }),
  Object.freeze({
    id: 'CheckFinalPNPProofReport0',
    file: 'pcc-final-proof-report0.mjs',
    role: 'historical final proof-report acceptance surface',
    minimumKernelRole: 'historical-report-surface',
  }),
  Object.freeze({
    id: 'CheckSuccessorPublicReviewReportSeal0',
    file: 'pcc-successor-report-seal0.mjs',
    role: 'successor public-review boundary preserving blocker and non-emission policy',
    minimumKernelRole: 'current-public-boundary-entrypoint',
  }),
  Object.freeze({
    id: 'audit-report-theorem-bindings0',
    file: 'scripts/audit-report-theorem-bindings.mjs',
    role: 'machine-readable theorem-to-checker binding ledger audit',
    minimumKernelRole: 'report-theorem-binding-entrypoint',
  }),
]);

const MINIMAL_KERNEL_PROOF_SPINE0 = Object.freeze([
  Object.freeze({
    id: 'spine.kernel-rules',
    summary: 'Start with the PCC-K primitive rules, Sigma theorems, proof-DAG discipline, canonical bytes, and digest protocol.',
    ruleFamilies: Object.freeze(['Eq', 'Subst', 'Record', 'DAGInd', 'FiniteExhaust', 'IntArith', 'TruthVec', 'FiniteRel']),
    checkerIds: Object.freeze(['CheckVerifierFrag0', 'CheckKImpl0', 'CheckGlobalProofDAG0']),
    packageTheoremIds: Object.freeze([]),
    reportBindingIds: Object.freeze(['THM-19-2']),
  }),
  Object.freeze({
    id: 'spine.direct-wire-semantics',
    summary: 'Direct-wire words, compatible replacement, VerifyDW soundness, mode firewall, charge ownership, and row/proof-reference discipline.',
    ruleFamilies: Object.freeze(['Eq', 'Record', 'DAGInd', 'LedgerInd', 'TraceInd', 'Transport', 'TruthVec', 'FiniteRel']),
    checkerIds: Object.freeze(['CheckVerifierFrag0', 'CheckPCCPackexp0', 'CheckGlobalProofDAG0']),
    packageTheoremIds: Object.freeze([
      'E.VerifyDWSoundness',
      'N.TraceableNormalization',
      'NORFF.FrontierFaithfulComparison',
    ]),
    reportBindingIds: Object.freeze(['THM-6-1', 'THM-10-1', 'THM-19-2']),
  }),
  Object.freeze({
    id: 'spine.residual-band-minimization',
    summary: 'Residual slack descent, BCEL-ready positive nuclei, BN2-BN6 packet extraction, selector realization, HB closure, ZeroSlack, and residual-band exact minimization.',
    ruleFamilies: Object.freeze(['DAGInd', 'LedgerInd', 'FiniteExhaust', 'DPInd', 'Hall', 'RankInd', 'MinCounterexample', 'IntArith']),
    checkerIds: Object.freeze(['CheckPCCPackexp0', 'CheckGlobalProofDAG0']),
    packageTheoremIds: Object.freeze([
      'RW.BCELReady',
      'BN2.SideTightCoherentOptimum',
      'BN3.SimultaneousEnvelope',
      'BN4.ActivationExact',
      'BN5.FullShadowLocalization',
      'PkgC.SeparatingConsumers',
      'BN6.HypergraphPacket',
      'Packet.SelectorSeeds',
      'R.SelectorRealization',
      'HB.NegativeClosure',
      'O.ZeroSlackOracle',
    ]),
    reportBindingIds: Object.freeze([
      'THM-10-4',
      'THM-11-1',
      'THM-11-2',
      'THM-11-3',
      'THM-11-4',
      'THM-11-6',
      'THM-13-4',
      'THM-14-1',
      'THM-14-2',
      'THM-15-1',
      'THM-16-1',
      'THM-16-2',
    ]),
  }),
  Object.freeze({
    id: 'spine.locked-nand-sat-threshold',
    summary: 'Locked NAND SAT embedding, baseline distinctness, trace equivalence, final lock separation, threshold, and residual slack at most four.',
    ruleFamilies: Object.freeze(['Eq', 'DAGInd', 'TraceInd', 'FiniteExhaust', 'IntArith', 'TruthVec']),
    checkerIds: Object.freeze(['CheckGPack0', 'CheckFinalFrameworkMatch0', 'CheckSATDecision0', 'CheckGlobalProofDAG0']),
    packageTheoremIds: Object.freeze(['G.LockedNANDThreshold', 'Final.FrameworkMatch']),
    reportBindingIds: Object.freeze(['THM-17-2']),
  }),
  Object.freeze({
    id: 'spine.complexity-implication',
    summary: 'Residual-band exact minimization plus locked NAND threshold yields SAT in P; the complexity ledger records the remaining implication surface without public theorem activation.',
    ruleFamilies: Object.freeze(['Record', 'DAGInd', 'IntArith', 'Transport']),
    checkerIds: Object.freeze(['CheckSATDecision0', 'CheckSATBounds0', 'CheckGlobalProofDAG0']),
    packageTheoremIds: Object.freeze(['Final.AcceptedPackageImpliesSATinP', 'Final.AcceptedPackageImpliesPEqualsNP']),
    reportBindingIds: Object.freeze(['THM-18-2']),
  }),
  Object.freeze({
    id: 'spine.package-acceptance',
    summary: 'Generated-package acceptance, global proof DAG, no-hidden-minimization discipline, bounds, final integration, and CheckPCCPackexp0.',
    ruleFamilies: Object.freeze(['Record', 'LedgerInd', 'FiniteExhaust', 'DPInd', 'IntArith']),
    checkerIds: Object.freeze(['CheckPCCPackexp0', 'CheckGlobalProofDAG0', 'CheckFinalFrameworkMatch0', 'CheckSATBounds0']),
    packageTheoremIds: Object.freeze(['PACK.PackageSufficiency', 'Final.PackageSoundness', 'Final.GeneratedPackageSufficiency']),
    reportBindingIds: Object.freeze(['THM-18-1', 'THM-20-19']),
  }),
  Object.freeze({
    id: 'spine.report-and-release-boundary',
    summary: 'Historical final proof-report surface is bound to the successor public-review seal; final theorem nodes remain quarantined and non-emitting.',
    ruleFamilies: Object.freeze(['Record', 'LedgerInd', 'IntArith']),
    checkerIds: Object.freeze(['CheckFinalPNPProofReport0', 'CheckSuccessorPublicReviewReportSeal0', 'audit-report-theorem-bindings0']),
    packageTheoremIds: Object.freeze([]),
    reportBindingIds: Object.freeze(['THM-1-1', 'THM-20-19']),
  }),
]);

export const PNP_MINIMAL_KERNEL0 = Object.freeze({
  kind: 'PNPMinimalKernel0',
  version: CHECKER_VERSION,
  coordinate: PNP_MINIMAL_KERNEL_COORDINATE0,
  title: 'Minimal proof-kernel coordinate',
  purpose: 'Provide a small, explicit entrypoint that tells reviewers which kernel rules, checker surfaces, proof-spine stages, and release-boundary gates must be inspected before reading the rest of the repository.',
  status: 'minimal-kernel-coordinate-ready',
  createdForPrTrack: 'PR-80 kernel: add minimal proof kernel coordinate',
  claimBoundary: Object.freeze({
    project: 'PNP',
    currentPublicStatus: 'public-review successor-boundary; internal proof-certificate stack under checker trust model',
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    activeFinalNodeIds: Object.freeze([]),
    quarantinedFinalNodeIds: GLOBAL_DAG_REQUIRED_FINALS0,
    remainingBlockers: MINIMAL_KERNEL_REMAINING_BLOCKERS0,
  }),
  entrypoints: Object.freeze({
    kernelJson: 'kernel/PNP_MINIMAL_KERNEL.json',
    checker: 'pcc-minimal-kernel0.mjs',
    tests: 'test/pcc-minimal-kernel0.test.mjs',
    theoremBindingLedger: 'report-bindings/REPORT_THEOREM_BINDINGS.json',
    successorReportSeal: 'successor-report-seals/PNP-REPORT-SEAL-2026-06-27-01/SEAL.json',
  }),
  predecessors: Object.freeze([
    Object.freeze({
      id: 'REPORT-THEOREM-BINDINGS-2026-06-27-01',
      kind: 'theorem-to-checker-binding-ledger',
      checkerId: 'audit-report-theorem-bindings0',
      path: 'report-bindings/REPORT_THEOREM_BINDINGS.json',
      ready: true,
      activatesPublicTheorem: false,
    }),
    Object.freeze({
      id: 'PNP-REPORT-SEAL-2026-06-27-01',
      kind: 'successor-public-review-boundary-seal',
      checkerId: 'CheckSuccessorPublicReviewReportSeal0',
      path: 'pcc-successor-report-seal0.mjs',
      ready: true,
      activatesPublicTheorem: false,
    }),
    Object.freeze({
      id: 'GLOBAL-PROOF-DAG0',
      kind: 'global-proof-dag-surface',
      checkerId: 'CheckGlobalProofDAG0',
      path: 'pcc-global-proof-dag0.mjs',
      ready: true,
      activatesPublicTheorem: false,
    }),
  ]),
  proofKernel: Object.freeze({
    primitiveRuleSource: 'pcc-kimpl0.mjs#KERNEL_RULES0',
    primitiveRules: KERNEL_RULES0,
    sigmaSource: 'pcc-kimpl0.mjs#SIGMA_REQUIRED_THEOREMS0',
    sigmaTheorems: SIGMA_REQUIRED_THEOREMS0,
    globalFinalSource: 'pcc-global-proof-dag0.mjs#GLOBAL_DAG_REQUIRED_FINALS0',
    quarantinedFinalNodeIds: GLOBAL_DAG_REQUIRED_FINALS0,
    requiredPackageTheoremSource: 'pcc-global-proof-dag0.mjs#GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0',
    requiredPackageTheoremIds: GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0,
  }),
  checkerSurface: MINIMAL_KERNEL_CHECKER_SURFACE0,
  proofSpine: MINIMAL_KERNEL_PROOF_SPINE0,
  quarantinedConclusions: GLOBAL_DAG_REQUIRED_FINALS0.map((id) => Object.freeze({
    id,
    status: 'quarantined-by-successor-public-review-boundary',
    notActive: true,
    publicTheoremEmissionAllowed: false,
  })),
  explicitNonClaims: Object.freeze([
    'This minimal kernel coordinate is an audit entrypoint, not a public theorem activation.',
    'It does not discharge Release.UnrestrictedFinalSoundness or ExternalReview.Acceptance.',
    'It does not mutate the historical sealed report or rewrite its theorem-emission wording.',
    'It does not assert that the trust base is empty; it makes the kernel surface easier to inspect.',
  ]),
  auditRequirements: Object.freeze([
    'Check primitive-rule and Sigma-rule soundness separately from this coordinate.',
    'Check every proof-spine checker id against the theorem-to-checker binding ledger.',
    'Check that locked NAND threshold and residual-band minimization use the same direct-wire semantics.',
    'Check no final theorem node is made active before the successor release gates permit public theorem emission.',
  ]),
});

export const PNP_MINIMAL_KERNEL_POLICY0 = Object.freeze({
  kind: 'PNPMinimalKernelPolicy0',
  version: CHECKER_VERSION,
  coordinate: PNP_MINIMAL_KERNEL_COORDINATE0,
  requiresExactCoordinate: true,
  requiresKernelJsonEntrypoint: true,
  requiresTheoremBindingLedgerPredecessor: true,
  requiresSuccessorBoundaryPredecessor: true,
  requiresPrimitiveRuleTable: true,
  requiresCheckerSurface: true,
  requiresProofSpine: true,
  requiresQuarantinedFinalNodeIds: true,
  publicTheoremEmissionAllowed: false,
  finalTheoremReady: false,
  activeFinalNodeIdsMustRemainEmpty: true,
  callerReadinessAssertionsForbidden: true,
  remainingBlockers: MINIMAL_KERNEL_REMAINING_BLOCKERS0,
});

export function makeMinimalKernelInput0({
  Kernel = PNP_MINIMAL_KERNEL0,
  Policy = PNP_MINIMAL_KERNEL_POLICY0,
} = {}) {
  return Object.freeze({
    kind: 'PNPMinimalKernelInput0',
    version: CHECKER_VERSION,
    Kernel,
    Policy,
  });
}

export async function CheckMinimalKernel0(input = makeMinimalKernelInput0()) {
  const checker = 'CheckMinimalKernel0';
  const inputShape = validateInputShape0(input);
  if (!inputShape.ok) return reject0(checker, `${checker}.input`, inputShape.path, inputShape.witness);

  const kernel = validateKernel0(input.Kernel);
  if (!kernel.ok) return reject0(checker, `${checker}.kernel`, kernel.path, kernel.witness);

  const nf = {
    kind: 'PNPMinimalKernel0NF',
    checker,
    version: CHECKER_VERSION,
    coordinate: input.Kernel.coordinate,
    minimalKernelReady: true,
    kernelDigest: digestCanonical0(input.Kernel),
    primitiveRuleCount: input.Kernel.proofKernel.primitiveRules.length,
    sigmaTheoremCount: input.Kernel.proofKernel.sigmaTheorems.length,
    packageTheoremCount: input.Kernel.proofKernel.requiredPackageTheoremIds.length,
    checkerSurfaceCount: input.Kernel.checkerSurface.length,
    proofSpineCount: input.Kernel.proofSpine.length,
    theoremBindingLedgerBound: true,
    successorBoundaryBound: true,
    publicTheoremEmissionAllowed: false,
    finalTheoremReady: false,
    activeFinalNodeIds: [],
    quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    remainingBlockers: [...MINIMAL_KERNEL_REMAINING_BLOCKERS0],
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
  if (!isPlainObject0(input)) return validationReject0([], 'minimal kernel input must be an object');
  if (input.kind !== 'PNPMinimalKernelInput0') return validationReject0(['kind'], 'minimal kernel input kind mismatch');
  if (input.version !== CHECKER_VERSION) return validationReject0(['version'], 'minimal kernel input version mismatch');
  const required = ['Kernel', 'Policy'];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) return validationReject0([field], 'minimal kernel input is missing a required field');
  }
  if (!sameCanonical0(input.Policy, PNP_MINIMAL_KERNEL_POLICY0)) return validationReject0(['Policy'], 'minimal kernel policy mismatch');
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return validationReject0([unexpected[0]], 'minimal kernel checker rejects caller-supplied readiness or truth assertions');
  return { ok: true };
}

function validateKernel0(kernel) {
  if (!isPlainObject0(kernel)) return validationReject0([], 'minimal kernel must be an object');
  const allowedTop = new Set([
    'kind',
    'version',
    'coordinate',
    'title',
    'purpose',
    'status',
    'createdForPrTrack',
    'claimBoundary',
    'entrypoints',
    'predecessors',
    'proofKernel',
    'checkerSurface',
    'proofSpine',
    'quarantinedConclusions',
    'explicitNonClaims',
    'auditRequirements',
  ]);
  for (const key of Object.keys(kernel)) {
    if (!allowedTop.has(key)) return validationReject0([key], 'minimal kernel contains an unsupported top-level field');
  }
  if (kernel.kind !== 'PNPMinimalKernel0') return validationReject0(['kind'], 'minimal kernel kind mismatch');
  if (kernel.version !== CHECKER_VERSION) return validationReject0(['version'], 'minimal kernel version mismatch');
  if (kernel.coordinate !== PNP_MINIMAL_KERNEL_COORDINATE0) return validationReject0(['coordinate'], 'minimal kernel coordinate mismatch');
  if (kernel.status !== 'minimal-kernel-coordinate-ready') return validationReject0(['status'], 'minimal kernel status mismatch');

  const boundary = validateClaimBoundary0(kernel.claimBoundary);
  if (!boundary.ok) return boundary;
  const entrypoints = validateEntrypoints0(kernel.entrypoints);
  if (!entrypoints.ok) return entrypoints;
  const predecessors = validatePredecessors0(kernel.predecessors);
  if (!predecessors.ok) return predecessors;
  const proofKernel = validateProofKernel0(kernel.proofKernel);
  if (!proofKernel.ok) return proofKernel;
  const checkerSurface = validateCheckerSurface0(kernel.checkerSurface);
  if (!checkerSurface.ok) return checkerSurface;
  const proofSpine = validateProofSpine0(kernel.proofSpine, kernel.checkerSurface, kernel.proofKernel);
  if (!proofSpine.ok) return proofSpine;
  const quarantined = validateQuarantinedConclusions0(kernel.quarantinedConclusions);
  if (!quarantined.ok) return quarantined;
  const nonClaims = validateStringArray0(kernel.explicitNonClaims, ['explicitNonClaims'], { nonEmpty: true });
  if (!nonClaims.ok) return nonClaims;
  const audit = validateStringArray0(kernel.auditRequirements, ['auditRequirements'], { nonEmpty: true });
  if (!audit.ok) return audit;

  const forbidden = findForbiddenActivationClaim0(kernel);
  if (forbidden) return validationReject0(forbidden.path, forbidden.reason);

  return { ok: true };
}

function validateClaimBoundary0(boundary) {
  if (!isPlainObject0(boundary)) return validationReject0(['claimBoundary'], 'claim boundary must be an object');
  if (boundary.publicTheoremEmissionAllowed !== false) return validationReject0(['claimBoundary', 'publicTheoremEmissionAllowed'], 'minimal kernel cannot allow public theorem emission');
  if (boundary.finalTheoremReady !== false) return validationReject0(['claimBoundary', 'finalTheoremReady'], 'minimal kernel cannot mark final theorem ready');
  if (!Array.isArray(boundary.activeFinalNodeIds) || boundary.activeFinalNodeIds.length !== 0) return validationReject0(['claimBoundary', 'activeFinalNodeIds'], 'active final node ids must remain empty');
  if (!sameStringArray0(boundary.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)) return validationReject0(['claimBoundary', 'quarantinedFinalNodeIds'], 'quarantined final node ids must match global final node ids');
  if (!sameStringArray0(boundary.remainingBlockers, MINIMAL_KERNEL_REMAINING_BLOCKERS0)) return validationReject0(['claimBoundary', 'remainingBlockers'], 'remaining blockers must remain exact');
  return { ok: true };
}

function validateEntrypoints0(entrypoints) {
  if (!isPlainObject0(entrypoints)) return validationReject0(['entrypoints'], 'entrypoints must be an object');
  const expected = PNP_MINIMAL_KERNEL0.entrypoints;
  for (const [key, value] of Object.entries(expected)) {
    if (entrypoints[key] !== value) return validationReject0(['entrypoints', key], 'minimal kernel entrypoint mismatch');
  }
  return { ok: true };
}

function validatePredecessors0(predecessors) {
  if (!Array.isArray(predecessors) || predecessors.length !== PNP_MINIMAL_KERNEL0.predecessors.length) return validationReject0(['predecessors'], 'minimal kernel predecessors must have exact length');
  const seen = new Set();
  for (let index = 0; index < predecessors.length; index += 1) {
    const predecessor = predecessors[index];
    if (!isPlainObject0(predecessor)) return validationReject0(['predecessors', index], 'predecessor must be an object');
    if (!isNonEmptyString0(predecessor.id)) return validationReject0(['predecessors', index, 'id'], 'predecessor id must be non-empty');
    if (seen.has(predecessor.id)) return validationReject0(['predecessors', index, 'id'], 'predecessor ids must be unique');
    seen.add(predecessor.id);
    if (predecessor.ready !== true) return validationReject0(['predecessors', index, 'ready'], 'minimal kernel predecessor must be marked ready');
    if (predecessor.activatesPublicTheorem !== false) return validationReject0(['predecessors', index, 'activatesPublicTheorem'], 'predecessor cannot activate public theorem emission');
    const expected = PNP_MINIMAL_KERNEL0.predecessors[index];
    if (!sameCanonical0(predecessor, expected)) return validationReject0(['predecessors', index], 'predecessor entry mismatch');
  }
  return { ok: true };
}

function validateProofKernel0(proofKernel) {
  if (!isPlainObject0(proofKernel)) return validationReject0(['proofKernel'], 'proofKernel must be an object');
  if (proofKernel.primitiveRuleSource !== 'pcc-kimpl0.mjs#KERNEL_RULES0') return validationReject0(['proofKernel', 'primitiveRuleSource'], 'primitive rule source mismatch');
  if (!sameStringArray0(proofKernel.primitiveRules, KERNEL_RULES0)) return validationReject0(['proofKernel', 'primitiveRules'], 'primitive rules must match KERNEL_RULES0');
  if (proofKernel.sigmaSource !== 'pcc-kimpl0.mjs#SIGMA_REQUIRED_THEOREMS0') return validationReject0(['proofKernel', 'sigmaSource'], 'sigma source mismatch');
  if (!sameStringArray0(proofKernel.sigmaTheorems, SIGMA_REQUIRED_THEOREMS0)) return validationReject0(['proofKernel', 'sigmaTheorems'], 'sigma theorem ids must match SIGMA_REQUIRED_THEOREMS0');
  if (!sameStringArray0(proofKernel.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)) return validationReject0(['proofKernel', 'quarantinedFinalNodeIds'], 'proof kernel final nodes must remain quarantined');
  if (!sameStringArray0(proofKernel.requiredPackageTheoremIds, GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0)) return validationReject0(['proofKernel', 'requiredPackageTheoremIds'], 'required package theorem ids must match GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0');
  return { ok: true };
}

function validateCheckerSurface0(checkerSurface) {
  if (!Array.isArray(checkerSurface)) return validationReject0(['checkerSurface'], 'checkerSurface must be an array');
  const expected = new Map(MINIMAL_KERNEL_CHECKER_SURFACE0.map((entry) => [entry.id, entry]));
  const seen = new Set();
  for (let index = 0; index < checkerSurface.length; index += 1) {
    const checker = checkerSurface[index];
    if (!isPlainObject0(checker)) return validationReject0(['checkerSurface', index], 'checker surface entry must be an object');
    if (!isNonEmptyString0(checker.id)) return validationReject0(['checkerSurface', index, 'id'], 'checker surface id must be non-empty');
    if (seen.has(checker.id)) return validationReject0(['checkerSurface', index, 'id'], 'checker surface ids must be unique');
    seen.add(checker.id);
    const expectedEntry = expected.get(checker.id);
    if (!expectedEntry) return validationReject0(['checkerSurface', index, 'id'], 'checker surface contains unknown checker id');
    if (!sameCanonical0(checker, expectedEntry)) return validationReject0(['checkerSurface', index], 'checker surface entry mismatch');
  }
  if (!sameStringArray0([...seen], MINIMAL_KERNEL_REQUIRED_CHECKERS0)) return validationReject0(['checkerSurface'], 'checker surface must contain the required checker ids');
  return { ok: true };
}

function validateProofSpine0(proofSpine, checkerSurface, proofKernel) {
  if (!Array.isArray(proofSpine)) return validationReject0(['proofSpine'], 'proofSpine must be an array');
  const checkerIds = new Set(checkerSurface.map((entry) => entry.id));
  const primitiveRules = new Set(proofKernel.primitiveRules);
  const packageTheoremIds = new Set(proofKernel.requiredPackageTheoremIds);
  const seen = new Set();
  for (let index = 0; index < proofSpine.length; index += 1) {
    const stage = proofSpine[index];
    if (!isPlainObject0(stage)) return validationReject0(['proofSpine', index], 'proof-spine stage must be an object');
    if (!isNonEmptyString0(stage.id)) return validationReject0(['proofSpine', index, 'id'], 'proof-spine id must be non-empty');
    if (seen.has(stage.id)) return validationReject0(['proofSpine', index, 'id'], 'proof-spine ids must be unique');
    seen.add(stage.id);
    for (const field of ['ruleFamilies', 'checkerIds', 'packageTheoremIds', 'reportBindingIds']) {
      const arr = validateStringArray0(stage[field], ['proofSpine', index, field], { nonEmpty: field !== 'packageTheoremIds' });
      if (!arr.ok) return arr;
    }
    for (const rule of stage.ruleFamilies) {
      if (!primitiveRules.has(rule)) return validationReject0(['proofSpine', index, 'ruleFamilies'], 'proof-spine stage references a primitive rule outside the kernel rule table');
    }
    for (const checkerId of stage.checkerIds) {
      if (!checkerIds.has(checkerId)) return validationReject0(['proofSpine', index, 'checkerIds'], 'proof-spine stage references checker outside checker surface');
    }
    for (const theoremId of stage.packageTheoremIds) {
      if (!packageTheoremIds.has(theoremId) && !GLOBAL_DAG_REQUIRED_FINALS0.includes(theoremId)) return validationReject0(['proofSpine', index, 'packageTheoremIds'], 'proof-spine stage references unknown package theorem id');
    }
  }
  if (!sameStringArray0([...seen], MINIMAL_KERNEL_REQUIRED_SPINE_IDS0)) return validationReject0(['proofSpine'], 'proof spine must contain the required stage ids');
  return { ok: true };
}

function validateQuarantinedConclusions0(conclusions) {
  if (!Array.isArray(conclusions) || conclusions.length !== GLOBAL_DAG_REQUIRED_FINALS0.length) return validationReject0(['quarantinedConclusions'], 'quarantined conclusions must match final node count');
  for (let index = 0; index < GLOBAL_DAG_REQUIRED_FINALS0.length; index += 1) {
    const entry = conclusions[index];
    if (!isPlainObject0(entry)) return validationReject0(['quarantinedConclusions', index], 'quarantined conclusion must be an object');
    if (entry.id !== GLOBAL_DAG_REQUIRED_FINALS0[index]) return validationReject0(['quarantinedConclusions', index, 'id'], 'quarantined final node id mismatch');
    if (entry.status !== 'quarantined-by-successor-public-review-boundary') return validationReject0(['quarantinedConclusions', index, 'status'], 'quarantined conclusion status mismatch');
    if (entry.notActive !== true) return validationReject0(['quarantinedConclusions', index, 'notActive'], 'quarantined conclusion must remain inactive');
    if (entry.publicTheoremEmissionAllowed !== false) return validationReject0(['quarantinedConclusions', index, 'publicTheoremEmissionAllowed'], 'quarantined conclusion cannot allow public theorem emission');
  }
  return { ok: true };
}

function validateStringArray0(value, path, { nonEmpty = false } = {}) {
  if (!Array.isArray(value)) return validationReject0(path, 'field must be an array of strings');
  if (nonEmpty && value.length === 0) return validationReject0(path, 'field must not be empty');
  for (let index = 0; index < value.length; index += 1) {
    if (!isNonEmptyString0(value[index])) return validationReject0([...path, index], 'array entry must be a non-empty string');
  }
  return { ok: true };
}

function findForbiddenActivationClaim0(value, path = []) {
  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const found = findForbiddenActivationClaim0(value[index], [...path, index]);
      if (found) return found;
    }
    return null;
  }
  if (!isPlainObject0(value)) return null;
  for (const [key, child] of Object.entries(value)) {
    const childPath = [...path, key];
    if ((key === 'activatesPublicTheorem' || key === 'dischargesPublicTheorem' || key === 'publicTheoremEmissionAllowed') && child !== false) {
      return { path: childPath, reason: 'minimal kernel contains a forbidden public-theorem activation claim' };
    }
    if ((key === 'finalTheoremReady') && child !== false) {
      return { path: childPath, reason: 'minimal kernel contains a forbidden final-theorem readiness claim' };
    }
    if ((key === 'activeFinalNodeIds') && (!Array.isArray(child) || child.length !== 0)) {
      return { path: childPath, reason: 'minimal kernel contains active final node ids' };
    }
    const found = findForbiddenActivationClaim0(child, childPath);
    if (found) return found;
  }
  return null;
}

function reject0(checker, coord, path, witness) {
  const nf = { kind: `${checker}RejectNF`, checker, version: CHECKER_VERSION, coord, path, witness };
  const digest = digestCanonical0(nf);
  return { tag: 'reject', kind: 'reject', checker, version: CHECKER_VERSION, Coord: coord, Path: path, Witness: witness, Digest: digest, coord, path, witness, digest };
}

function validationReject0(path, reason) { return { ok: false, path, witness: { reason } }; }
function sameCanonical0(left, right) { return stableStringify0(left) === stableStringify0(right); }
function sameStringArray0(left, right) { return Array.isArray(left) && Array.isArray(right) && left.length === right.length && left.every((value, index) => value === right[index]); }
function isPlainObject0(value) { return value !== null && typeof value === 'object' && !Array.isArray(value); }
function isNonEmptyString0(value) { return typeof value === 'string' && value.length > 0; }

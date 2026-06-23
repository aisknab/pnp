import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckConformance0,
  KERNEL_RULES0,
  makeKernelConformanceSuite0,
} from './pcc-kimpl0.mjs';

import {
  CheckKImplFiniteRelFinalTheoremReadiness0,
} from './pcc-kimpl-finiterel-successor0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
} from './pcc-kernel-finiterel-semantic0.mjs';

const CHECKER_VERSION = 0;

export const K0_SEMANTIC_CONFORMANCE_POLICY0 = Object.freeze({
  kind: 'K0SemanticConformancePolicy0',
  version: CHECKER_VERSION,
  requiresCompletePrimitiveSemanticKernel: true,
  requiresLegacyConformanceShapeAcceptance: true,
  requiresOneLocalSoundnessObligationPerPrimitiveRule: true,
  bindsEveryObligationToLegacyConformanceNodeDigest: true,
  bindsEveryObligationToExecutableCheckerBoundaryDigest: true,
  acceptedNormalFormContractRequired: true,
  staleStructuralOnlyConformanceRejected: true,
  callerSoundnessAssertionsForbidden: true,
  sigmaAndReflectionRemainSeparateSurfaces: true,
});

export const K0_SEMANTIC_RULE_CHECKER_BINDINGS0 = Object.freeze({
  Eq: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProof0',
    proofChecker: 'CheckSemanticKernelProof0',
    acceptedNFKind: 'SemanticKernelProof0NF',
    semanticLayer: 'core-equality',
  }),
  Subst: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProof0',
    proofChecker: 'CheckSemanticKernelProof0',
    acceptedNFKind: 'SemanticKernelProof0NF',
    semanticLayer: 'core-substitution',
  }),
  Record: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofRecord0',
    proofChecker: 'CheckSemanticKernelProofRecord0',
    acceptedNFKind: 'SemanticKernelProofRecord0NF',
    semanticLayer: 'record',
  }),
  DAGInd: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofDAGInd0',
    proofChecker: 'CheckSemanticKernelProofDAGInd0',
    acceptedNFKind: 'SemanticKernelProofDAGInd0NF',
    semanticLayer: 'dag-induction',
  }),
  LedgerInd: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofLedgerInd0',
    proofChecker: 'CheckSemanticKernelProofLedgerInd0',
    acceptedNFKind: 'SemanticKernelProofLedgerInd0NF',
    semanticLayer: 'ledger-induction',
  }),
  OblTopoInd: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofOblTopoInd0',
    proofChecker: 'CheckSemanticKernelProofOblTopoInd0',
    acceptedNFKind: 'SemanticKernelProofOblTopoInd0NF',
    semanticLayer: 'obligation-topology',
  }),
  TraceInd: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofTraceInd0',
    proofChecker: 'CheckSemanticKernelProofTraceInd0',
    acceptedNFKind: 'SemanticKernelProofTraceInd0NF',
    semanticLayer: 'trace-induction',
  }),
  FiniteExhaust: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofFiniteExhaust0',
    proofChecker: 'CheckSemanticKernelProofFiniteExhaust0',
    acceptedNFKind: 'SemanticKernelProofFiniteExhaust0NF',
    semanticLayer: 'finite-exhaustion',
  }),
  DPInd: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofDPInd0',
    proofChecker: 'CheckSemanticKernelProofDPInd0',
    acceptedNFKind: 'SemanticKernelProofDPInd0NF',
    semanticLayer: 'dynamic-programming-induction',
  }),
  Hall: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofHall0',
    proofChecker: 'CheckSemanticKernelProofHall0',
    acceptedNFKind: 'SemanticKernelProofHall0NF',
    semanticLayer: 'finite-hall',
  }),
  RankInd: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofRankInd0',
    proofChecker: 'CheckSemanticKernelProofRankInd0',
    acceptedNFKind: 'SemanticKernelProofRankInd0NF',
    semanticLayer: 'rank-induction',
  }),
  MinCounterexample: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofMinCounterexample0',
    proofChecker: 'CheckSemanticKernelProofMinCounterexample0',
    acceptedNFKind: 'SemanticKernelProofMinCounterexample0NF',
    semanticLayer: 'least-counterexample',
  }),
  IntArith: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofIntArith0',
    proofChecker: 'CheckSemanticKernelProofIntArith0',
    acceptedNFKind: 'SemanticKernelProofIntArith0NF',
    semanticLayer: 'integer-arithmetic',
  }),
  Transport: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofTransport0',
    proofChecker: 'CheckSemanticKernelProofTransport0',
    acceptedNFKind: 'SemanticKernelProofTransport0NF',
    semanticLayer: 'transport',
  }),
  TruthVec: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofTruthVec0',
    proofChecker: 'CheckSemanticKernelProofTruthVec0',
    acceptedNFKind: 'SemanticKernelProofTruthVec0NF',
    semanticLayer: 'truth-vector',
  }),
  FiniteRel: Object.freeze({
    primitiveChecker: 'CheckSemanticKernelProofFiniteRel0',
    proofChecker: 'CheckSemanticKernelProofFiniteRel0',
    acceptedNFKind: 'SemanticKernelProofFiniteRel0NF',
    semanticLayer: 'finite-relation',
  }),
});

export function makeSemanticK0ConformanceSuite0({
  K0 = makeKernelConformanceSuite0(),
} = {}) {
  const nodes = getConformanceNodes0(K0);
  const nodeByRule = makeConformanceNodeMap0(Array.isArray(nodes) ? nodes : []);
  return Object.freeze({
    kind: 'SemanticK0ConformanceSuite0',
    version: CHECKER_VERSION,
    suiteId: K0?.suiteId ?? K0?.id ?? 'K0.semantic.generated',
    obligations: Object.freeze(KERNEL_RULES0.map((ruleName, index) => (
      makeSemanticK0RuleConformance0({
        index,
        ruleName,
        conformanceNode: nodeByRule.get(ruleName) ?? null,
      })
    ))),
    Policy: { ...K0_SEMANTIC_CONFORMANCE_POLICY0 },
  });
}

export function makeSemanticK0ConformanceInput0({
  KImpl,
  K0 = makeKernelConformanceSuite0(),
  SemanticConformance = makeSemanticK0ConformanceSuite0({ K0 }),
} = {}) {
  return Object.freeze({
    kind: 'SemanticK0ConformanceInput0',
    version: CHECKER_VERSION,
    KImpl,
    K0,
    SemanticConformance,
    Policy: { ...K0_SEMANTIC_CONFORMANCE_POLICY0 },
  });
}

export async function CheckSemanticK0Conformance0(input) {
  const checker = 'CheckSemanticK0Conformance0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const ruleUniverse = validateRuleUniverse0();
  ledger.push(makeLedgerEntry0(
    'semanticRuleUniverse',
    ruleUniverse.ok,
    ruleUniverse.nf ?? ruleUniverse.witness,
  ));
  if (!ruleUniverse.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticRuleUniverse`,
      ruleUniverse,
      ledger,
    );
  }

  const kimplFinal = await callChecker0(
    'CheckKImplFiniteRelFinalTheoremReadiness0',
    () => CheckKImplFiniteRelFinalTheoremReadiness0({
      ...input.KImpl,
      Purpose: 'final-theorem',
    }),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKImplFiniteRelFinalTheoremReadiness0',
    kimplFinal.ok && isKImplFinalAccept0(kimplFinal.record),
    kimplFinal.ok ? kimplFinal.record : kimplFinal.witness,
  ));
  if (!kimplFinal.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImpl.exception`,
      path: ['KImpl'],
      witness: kimplFinal.witness,
      ledger,
    });
  }
  if (!isKImplFinalAccept0(kimplFinal.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImpl`,
      path: ['KImpl'],
      witness: {
        reason: 'semantic K0 conformance requires a complete final-ready primitive semantic KImpl',
        inner: compactRecord0(kimplFinal.record),
      },
      ledger,
    });
  }

  const baseKImpl = input.KImpl.KImpl ?? input.KImpl;
  const legacyConformance = await callChecker0(
    'CheckConformance0',
    () => CheckConformance0(baseKImpl, input.K0),
  );
  ledger.push(makeLedgerEntry0(
    'CheckConformance0',
    legacyConformance.ok && legacyConformance.record.tag === 'accept',
    legacyConformance.ok ? legacyConformance.record : legacyConformance.witness,
  ));
  if (!legacyConformance.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyConformance.exception`,
      path: ['K0'],
      witness: legacyConformance.witness,
      ledger,
    });
  }
  if (legacyConformance.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyConformance`,
      path: ['K0'],
      witness: {
        reason: 'legacy K0 conformance shape checker rejected before semantic upgrade',
        inner: compactRecord0(legacyConformance.record),
      },
      ledger,
    });
  }

  const suite = validateSemanticConformanceSuite0(
    input.SemanticConformance,
    input.K0,
  );
  ledger.push(makeLedgerEntry0(
    'semanticConformanceSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticConformanceSuite`,
      suite,
      ledger,
    );
  }

  const kimplNF = kimplFinal.record.NF ?? kimplFinal.record.nf ?? {};
  const legacyNF = legacyConformance.record.NF ?? legacyConformance.record.nf ?? {};
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticK0Conformance0NF',
      checker,
      version: CHECKER_VERSION,
      semanticK0ConformanceReady: true,
      semanticConformanceReady: true,
      semanticKImplFinalReady: true,
      semanticKImplFinalChecker: kimplFinal.record.checker,
      semanticKImplFinalDigest:
        kimplFinal.record.Digest ?? kimplFinal.record.digest,
      semanticKernelReady: kimplNF.semanticKernelReady === true,
      primitiveRuleCoverageComplete: true,
      supportedSemanticRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
      missingSemanticRules: [],

      legacyConformanceChecker: legacyConformance.record.checker,
      legacyConformanceDigest:
        legacyConformance.record.Digest ?? legacyConformance.record.digest,
      legacyConformanceAccepted: true,
      legacyConformanceSuiteId: legacyNF.suiteId ?? input.K0?.suiteId ?? null,
      legacyConformanceNodeCount: legacyNF.nodeCount ?? null,
      legacyStructuralOnlyBoundaryConsumed: true,

      semanticConformanceSuiteId: suite.nf.suiteId,
      semanticConformanceObligationCount: suite.nf.obligationCount,
      semanticConformanceCoveredRules: suite.nf.coveredRules,
      semanticConformanceObligationDigests: suite.nf.obligationDigests,
      executableBoundaryDigests: suite.nf.executableBoundaryDigests,
      acceptedNormalFormContracts: true,
      everyObligationBoundToLegacyConformanceNodeDigest: true,
      everyObligationBoundToExecutableCheckerBoundaryDigest: true,
      callerSoundnessAssertionsForbidden: true,
      sigmaReady: false,
      reflectionReady: false,
      sigmaAndReflectionRemainSeparateSurfaces: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeSemanticK0RuleConformance0({
  index,
  ruleName,
  conformanceNode,
}) {
  const binding = K0_SEMANTIC_RULE_CHECKER_BINDINGS0[ruleName];
  const conformanceNodeDigest = digestCanonical0(conformanceNode ?? null);
  const localSoundnessContract = Object.freeze({
    kind: 'K0LocalSemanticSoundnessContract0',
    version: CHECKER_VERSION,
    ruleName,
    semanticLayer: binding.semanticLayer,
    proofNodeMode: 'Full',
    primitiveChecker: binding.primitiveChecker,
    proofChecker: binding.proofChecker,
    finalProofChecker: 'CheckSemanticKernelProofFiniteRel0',
    kImplFinalReadinessChecker: 'CheckKImplFiniteRelFinalTheoremReadiness0',
    acceptedNormalFormKind: binding.acceptedNFKind,
    acceptsOnlyTotalAcceptRejectRecords: true,
    acceptedNormalFormDigestBound: true,
    failClosedUnsupportedInputs: true,
    noOpaqueProofObjects: true,
    noHiddenMinimizationOrOracle: true,
    callerSoundnessAssertionsForbidden: true,
  });
  const executableBoundary = Object.freeze({
    kind: 'K0ExecutableCheckerBoundary0',
    version: CHECKER_VERSION,
    ruleName,
    semanticLayer: binding.semanticLayer,
    primitiveChecker: binding.primitiveChecker,
    proofChecker: binding.proofChecker,
    finalProofChecker: 'CheckSemanticKernelProofFiniteRel0',
    kImplFinalReadinessChecker: 'CheckKImplFiniteRelFinalTheoremReadiness0',
    acceptedNormalFormKind: binding.acceptedNFKind,
    completeSupportedRuleSet: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
  });
  const obligation = Object.freeze({
    kind: 'SemanticK0RuleConformance0',
    version: CHECKER_VERSION,
    index,
    ruleName,
    conformanceNodeId: conformanceNode?.id ?? `conf.${ruleName}`,
    conformanceNodeDigest,
    primitiveChecker: binding.primitiveChecker,
    proofChecker: binding.proofChecker,
    finalProofChecker: 'CheckSemanticKernelProofFiniteRel0',
    kImplFinalReadinessChecker: 'CheckKImplFiniteRelFinalTheoremReadiness0',
    acceptedNFKind: binding.acceptedNFKind,
    localSoundnessContract,
    executableBoundaryDigest: digestCanonical0(executableBoundary),
  });
  return Object.freeze({
    ...obligation,
    obligationDigest: digestCanonical0(obligation),
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'semantic K0 conformance input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'SemanticK0ConformanceInput0') {
    return validationReject0(
      ['kind'],
      'semantic K0 conformance input kind must be SemanticK0ConformanceInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic K0 conformance input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of ['KImpl', 'K0', 'SemanticConformance', 'Policy']) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic K0 conformance input is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.KImpl)) {
    return validationReject0(
      ['KImpl'],
      'semantic K0 conformance input KImpl must be an object',
      { actual: typeof input.KImpl },
    );
  }
  if (!isPlainObject0(input.K0)) {
    return validationReject0(
      ['K0'],
      'semantic K0 conformance input K0 must be an object',
      { actual: typeof input.K0 },
    );
  }
  if (!isPlainObject0(input.SemanticConformance)) {
    return validationReject0(
      ['SemanticConformance'],
      'semantic K0 conformance input SemanticConformance must be an object',
      { actual: typeof input.SemanticConformance },
    );
  }
  if (!isPlainObject0(input.Policy)
      || !sameCanonical0(input.Policy, K0_SEMANTIC_CONFORMANCE_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic K0 conformance policy must match the fail-closed policy',
      {
        expected: K0_SEMANTIC_CONFORMANCE_POLICY0,
        actual: input.Policy,
      },
    );
  }

  const allowed = new Set([
    'kind',
    'version',
    'KImpl',
    'K0',
    'SemanticConformance',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic K0 conformance rejects caller-supplied readiness or soundness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'SemanticK0ConformanceInputShape0NF',
  });
}

function validateRuleUniverse0() {
  if (!sameCanonical0(KERNEL_RULES0, SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0)) {
    return validationReject0(
      ['RuleUniverse'],
      'semantic K0 conformance requires the complete FiniteRel semantic rule universe',
      {
        kernelRules: [...KERNEL_RULES0],
        semanticRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
      },
    );
  }
  return validationAccept0({
    kind: 'SemanticK0RuleUniverse0NF',
    ruleCount: KERNEL_RULES0.length,
    rules: [...KERNEL_RULES0],
  });
}

function validateSemanticConformanceSuite0(suite, K0) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SemanticConformance'],
      'semantic K0 conformance suite must be an object',
      { actual: typeof suite },
    );
  }
  const allowed = new Set([
    'kind', 'version', 'suiteId', 'obligations', 'Policy',
  ]);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['SemanticConformance', unexpected[0]],
      'semantic K0 conformance suite rejects undeclared soundness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (suite.kind !== 'SemanticK0ConformanceSuite0') {
    return validationReject0(
      ['SemanticConformance', 'kind'],
      'semantic K0 conformance suite kind must be SemanticK0ConformanceSuite0',
      { actual: suite.kind },
    );
  }
  if (suite.version !== CHECKER_VERSION) {
    return validationReject0(
      ['SemanticConformance', 'version'],
      `semantic K0 conformance suite version must be ${CHECKER_VERSION}`,
      { actual: suite.version },
    );
  }
  if (!isNonEmptyString0(suite.suiteId)) {
    return validationReject0(
      ['SemanticConformance', 'suiteId'],
      'semantic K0 conformance suiteId must be a non-empty string',
      { actual: suite.suiteId },
    );
  }
  if (!Array.isArray(suite.obligations)
      || suite.obligations.length !== KERNEL_RULES0.length) {
    return validationReject0(
      ['SemanticConformance', 'obligations'],
      'semantic K0 conformance suite must provide one obligation per primitive rule',
      { expected: KERNEL_RULES0.length, actual: suite.obligations?.length },
    );
  }
  if (!isPlainObject0(suite.Policy)
      || !sameCanonical0(suite.Policy, K0_SEMANTIC_CONFORMANCE_POLICY0)) {
    return validationReject0(
      ['SemanticConformance', 'Policy'],
      'semantic K0 conformance suite policy must match the fail-closed policy',
      {
        expected: K0_SEMANTIC_CONFORMANCE_POLICY0,
        actual: suite.Policy,
      },
    );
  }

  const nodes = getConformanceNodes0(K0);
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['K0', 'nodes'],
      'semantic K0 conformance requires K0 conformance nodes',
      { actual: typeof nodes },
    );
  }
  const nodeByRule = makeConformanceNodeMap0(nodes);
  const seen = new Set();
  const obligationDigests = [];
  const executableBoundaryDigests = [];
  for (let index = 0; index < KERNEL_RULES0.length; index += 1) {
    const ruleName = KERNEL_RULES0[index];
    const obligation = suite.obligations[index];
    const shape = validateObligationShape0(obligation, index);
    if (!shape.ok) return shape;
    if (seen.has(obligation.ruleName)) {
      return validationReject0(
        ['SemanticConformance', 'obligations', index, 'ruleName'],
        'semantic K0 conformance obligation rule names must be unique',
        { ruleName: obligation.ruleName },
      );
    }
    seen.add(obligation.ruleName);
    const node = nodeByRule.get(ruleName);
    if (node === undefined) {
      return validationReject0(
        ['K0', 'nodes', ruleName],
        'semantic K0 conformance obligation references a missing legacy conformance node',
        { ruleName },
      );
    }
    const expected = makeSemanticK0RuleConformance0({
      index,
      ruleName,
      conformanceNode: node,
    });
    if (!sameCanonical0(obligation, expected)) {
      return validationReject0(
        ['SemanticConformance', 'obligations', index],
        'semantic K0 conformance obligation must exactly match the computed local soundness binding',
        { expected, actual: obligation },
      );
    }
    obligationDigests.push(obligation.obligationDigest);
    executableBoundaryDigests.push(obligation.executableBoundaryDigest);
  }

  return validationAccept0({
    kind: 'SemanticK0ConformanceSuite0NF',
    suiteId: suite.suiteId,
    obligationCount: suite.obligations.length,
    coveredRules: [...KERNEL_RULES0],
    obligationDigests,
    executableBoundaryDigests,
    policyDigest: digestCanonical0(suite.Policy),
  });
}

function validateObligationShape0(obligation, index) {
  const path = ['SemanticConformance', 'obligations', index];
  if (!isPlainObject0(obligation)) {
    return validationReject0(path, 'semantic K0 conformance obligation must be an object', {
      actual: typeof obligation,
    });
  }
  const allowed = new Set([
    'kind',
    'version',
    'index',
    'ruleName',
    'conformanceNodeId',
    'conformanceNodeDigest',
    'primitiveChecker',
    'proofChecker',
    'finalProofChecker',
    'kImplFinalReadinessChecker',
    'acceptedNFKind',
    'localSoundnessContract',
    'executableBoundaryDigest',
    'obligationDigest',
  ]);
  const unexpected = Object.keys(obligation).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'semantic K0 conformance obligation rejects caller-supplied soundness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (obligation.kind !== 'SemanticK0RuleConformance0') {
    return validationReject0(
      [...path, 'kind'],
      'semantic K0 conformance obligation kind must be SemanticK0RuleConformance0',
      { actual: obligation.kind },
    );
  }
  if (obligation.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `semantic K0 conformance obligation version must be ${CHECKER_VERSION}`,
      { actual: obligation.version },
    );
  }
  if (obligation.index !== index) {
    return validationReject0(
      [...path, 'index'],
      'semantic K0 conformance obligation indices must be exact consecutive coordinates',
      { expected: index, actual: obligation.index },
    );
  }
  if (!KERNEL_RULES0.includes(obligation.ruleName)) {
    return validationReject0(
      [...path, 'ruleName'],
      'semantic K0 conformance obligation ruleName must be a primitive rule',
      { actual: obligation.ruleName },
    );
  }
  for (const digestField of [
    'conformanceNodeDigest',
    'executableBoundaryDigest',
    'obligationDigest',
  ]) {
    if (!isDigest0(obligation[digestField])) {
      return validationReject0(
        [...path, digestField],
        'semantic K0 conformance obligation digest must be canonical',
        { actual: obligation[digestField] },
      );
    }
  }
  if (!isPlainObject0(obligation.localSoundnessContract)) {
    return validationReject0(
      [...path, 'localSoundnessContract'],
      'semantic K0 conformance local soundness contract must be an object',
      { actual: typeof obligation.localSoundnessContract },
    );
  }
  return validationAccept0({
    kind: 'SemanticK0ConformanceObligationShape0NF',
    index,
    ruleName: obligation.ruleName,
  });
}

function getConformanceNodes0(suite) {
  return suite?.nodes ?? suite?.Nodes ?? suite?.proofNodes ?? suite?.ProofDAG;
}

function makeConformanceNodeMap0(nodes) {
  const out = new Map();
  for (const node of nodes) {
    const ruleName = String(node?.RuleName ?? node?.ruleName ?? node?.rule ?? '');
    if (!out.has(ruleName)) out.set(ruleName, node);
  }
  return out;
}

function isKImplFinalAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return (
    record?.tag === 'accept'
    && nf?.semanticKernelReady === true
    && nf?.finalTheoremReady === true
    && nf?.publicTheoremEmissionAllowed === true
    && Array.isArray(nf?.missingSemanticRules)
    && nf.missingSemanticRules.length === 0
  );
}

async function callChecker0(name, thunk) {
  try {
    const record = await thunk();
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) {
      return {
        ok: false,
        witness: {
          reason: `${name} did not return a total accept/reject record`,
          actual: record,
        },
      };
    }
    return { ok: true, record };
  } catch (error) {
    return {
      ok: false,
      witness: {
        reason: `${name} threw instead of returning a reject record`,
        errorName: error?.name ?? null,
        errorMessage: error?.message ?? String(error),
      },
    };
  }
}

function compactRecord0(record) {
  return {
    tag: record?.tag ?? null,
    checker: record?.checker ?? null,
    coord: record?.Coord ?? record?.coord ?? null,
    path: record?.Path ?? record?.path ?? null,
    witness: record?.Witness ?? record?.witness ?? null,
    digest: record?.Digest ?? record?.digest ?? null,
  };
}

function makeLedgerEntry0(phase, ok, material) {
  return {
    phase,
    status: ok ? 'pass' : 'fail',
    digest: digestCanonical0(material ?? null),
  };
}

function makeAcceptRecord0({ checker, nf, ledger }) {
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

function makeRejectFromValidation0(checker, coord, result, ledger) {
  return makeRejectRecord0({
    checker,
    coord,
    path: result.path,
    witness: result.witness,
    ledger,
  });
}

function makeRejectRecord0({ checker, coord, path, witness, ledger }) {
  const nf = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };
  const digest = digestCanonical0(nf);
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
  return { ok: true, nf };
}

function validationReject0(path, reason, details = {}) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      ...(details ?? {}),
    },
  };
}

function sameCanonical0(left, right) {
  return stableStringify0(left) === stableStringify0(right);
}

function isDigest0(value) {
  return isPlainObject0(value)
    && value.alg === 'SHA256'
    && typeof value.hex === 'string'
    && /^[0-9a-f]{64}$/.test(value.hex);
}

function isNonEmptyString0(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

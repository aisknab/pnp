import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  makeKernelConformanceSuite0,
  makeReflectionRegistry0,
  makeSigmaRegistry0,
  makeSyntheticKImpl0,
} from './pcc-kimpl0.mjs';

import {
  CheckKBundleFiniteRelSuccessor0,
  makeKBundleFiniteRelSuccessor0,
} from './pcc-kbundle-finiterel-successor0.mjs';

import {
  CheckKImplFiniteRelSuccessor0,
  makeKImplFiniteRelSuccessor0,
} from './pcc-kimpl-finiterel-successor0.mjs';

import {
  CheckSemanticK0Conformance0,
  makeSemanticK0ConformanceInput0,
  makeSemanticK0ConformanceSuite0,
} from './pcc-k0-semantic-conformance0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
} from './pcc-kernel-finiterel-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

export const KBUNDLE_K0CONFORMANCE_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const KBUNDLE_K0CONFORMANCE_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'KBundleSemanticK0ConformanceReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKImplInputMustRemainDevelopmentPurpose: true,
  predecessorKBundleMustRemainDevelopmentOnly: true,
  predecessorKBundleCannotImplyK0ConformanceReadiness: true,
  k0SemanticConformanceMustBeComputed: true,
  k0SemanticConformanceConsumesStructuralK0OnlyThroughChecker: true,
  finalTheoremRequiresSemanticKImplReadiness: true,
  finalTheoremRequiresSemanticConformance: true,
  finalTheoremRequiresSemanticSigmaDerivations: true,
  finalTheoremRequiresSemanticReflectionSoundness: true,
  publicTheoremEmissionRequiresBundleFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const KBUNDLE_K0CONFORMANCE_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'KBundleSemanticK0ConformanceCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorKBundleChecker: 'CheckKBundleFiniteRelSuccessor0',
  semanticKImplChecker: 'CheckKImplFiniteRelSuccessor0',
  semanticK0ConformanceChecker: 'CheckSemanticK0Conformance0',
});

export function makeKBundleK0ConformanceSuccessor0({
  KImpl = makeSyntheticKImpl0(),
  SemanticProofDAG = makeSemanticProofDAG0(),
  K0 = makeKernelConformanceSuite0(),
  K0SemanticConformance = makeSemanticK0ConformanceSuite0({ K0 }),
  PSigma = makeSigmaRegistry0(),
  ReflectionRegistry = makeReflectionRegistry0(),
  Purpose = 'development',
} = {}) {
  if (!KBUNDLE_K0CONFORMANCE_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeKBundleK0ConformanceSuccessor0 Purpose must be one of ${KBUNDLE_K0CONFORMANCE_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }

  return {
    kind: 'KBundleSemanticK0ConformanceSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    SemanticKImpl: makeKImplFiniteRelSuccessor0({
      KImpl,
      SemanticProofDAG,
      Purpose: 'development',
    }),
    K0,
    K0SemanticConformance,
    PSigma,
    ReflectionRegistry,
    Binding: { ...KBUNDLE_K0CONFORMANCE_SUCCESSOR_BINDING0 },
    Policy: { ...KBUNDLE_K0CONFORMANCE_SUCCESSOR_POLICY0 },
  };
}

export async function CheckKBundleK0ConformanceSuccessor0(input) {
  return checkKBundleInternal0(input, {
    checker: 'CheckKBundleK0ConformanceSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckKBundleK0ConformanceFinalTheoremReadiness0(input) {
  return checkKBundleInternal0(input, {
    checker: 'CheckKBundleK0ConformanceFinalTheoremReadiness0',
    requiredPurpose: 'final-theorem',
  });
}

async function checkKBundleInternal0(input, {
  checker,
  requiredPurpose,
}) {
  const ledger = [];

  const shape = validateShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  if (requiredPurpose !== null && input.Purpose !== requiredPurpose) {
    const witness = {
      reason: 'semantic K0 conformance KBundle final readiness requires a final-theorem purpose record',
      requiredPurpose,
      actualPurpose: input.Purpose,
    };
    ledger.push(makeLedgerEntry0('purpose', false, witness));
    return makeRejectRecord0({
      checker,
      coord: `${checker}.purpose`,
      path: ['Purpose'],
      witness,
      ledger,
    });
  }

  const purpose = requiredPurpose ?? input.Purpose;
  ledger.push(makeLedgerEntry0('purpose', true, {
    kind: 'KBundleK0ConformancePurpose0NF',
    purpose,
  }));

  const fullNodes = extractNodes0(input.SemanticKImpl.SemanticKernel?.ProofDAG);
  ledger.push(makeLedgerEntry0(
    'proofDAGShape',
    fullNodes.ok,
    fullNodes.nf ?? fullNodes.witness,
  ));
  if (!fullNodes.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.proofDAGShape`,
      fullNodes,
      ledger,
    );
  }

  const predecessorNodes = fullNodes.nodes.filter(
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0.includes(
      node?.RuleName,
    ),
  );
  const predecessorBundleInput = makeKBundleFiniteRelSuccessor0({
    KImpl: input.SemanticKImpl.KImpl,
    SemanticProofDAG: makeSemanticProofDAG0(predecessorNodes),
    K0: input.K0,
    PSigma: input.PSigma,
    ReflectionRegistry: input.ReflectionRegistry,
    Purpose: 'development',
  });

  const predecessorCall = await callChecker0(
    'CheckKBundleFiniteRelSuccessor0',
    () => CheckKBundleFiniteRelSuccessor0(predecessorBundleInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundleFiniteRelSuccessor0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));

  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorKBundle.exception`,
      path: ['PredecessorKBundle'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  const predecessorRecord = predecessorCall.record;
  if (predecessorRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorKBundle`,
      path: ['PredecessorKBundle'],
      witness: {
        reason: 'FiniteRel predecessor KBundle rejected the complete primitive semantic base',
        predecessorNodeIds: predecessorNodes.map((node) => node?.id ?? null),
        inner: compactRecord0(predecessorRecord),
      },
      ledger,
    });
  }
  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessorBundleBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'predecessorKBundleDevelopmentBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.predecessorKBundleDevelopmentBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const kimplCall = await callChecker0(
    'CheckKImplFiniteRelSuccessor0',
    () => CheckKImplFiniteRelSuccessor0({
      ...input.SemanticKImpl,
      Purpose: 'development',
    }),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKImplFiniteRelSuccessor0',
    kimplCall.ok && kimplCall.record.tag === 'accept',
    kimplCall.ok ? kimplCall.record : kimplCall.witness,
  ));
  if (!kimplCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImpl.exception`,
      path: ['SemanticKImpl'],
      witness: kimplCall.witness,
      ledger,
    });
  }
  const kimplRecord = kimplCall.record;
  if (kimplRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImpl`,
      path: ['SemanticKImpl'],
      witness: {
        reason: 'FiniteRel development semantic KImpl successor rejected',
        inner: compactRecord0(kimplRecord),
      },
      ledger,
    });
  }
  const kimplNF = kimplRecord.NF ?? kimplRecord.nf ?? {};
  const kimplBoundary = validateDevelopmentKImplBoundary0(kimplNF);
  ledger.push(makeLedgerEntry0(
    'semanticKImplDevelopmentBoundary',
    kimplBoundary.ok,
    kimplBoundary.nf ?? kimplBoundary.witness,
  ));
  if (!kimplBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticKImplDevelopmentBoundary`,
      kimplBoundary,
      ledger,
    );
  }

  const conformanceInput = makeSemanticK0ConformanceInput0({
    KImpl: input.SemanticKImpl,
    K0: input.K0,
    SemanticConformance: input.K0SemanticConformance,
  });
  const conformanceCall = await callChecker0(
    'CheckSemanticK0Conformance0',
    () => CheckSemanticK0Conformance0(conformanceInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckSemanticK0Conformance0',
    conformanceCall.ok && conformanceCall.record.tag === 'accept',
    conformanceCall.ok ? conformanceCall.record : conformanceCall.witness,
  ));
  if (!conformanceCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticConformance.exception`,
      path: ['K0SemanticConformance'],
      witness: conformanceCall.witness,
      ledger,
    });
  }
  const conformanceRecord = conformanceCall.record;
  if (conformanceRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticConformance`,
      path: ['K0SemanticConformance'],
      witness: {
        reason: 'semantic K0 conformance checker rejected the conformance surface',
        inner: compactRecord0(conformanceRecord),
      },
      ledger,
    });
  }
  const conformanceNF = conformanceRecord.NF ?? conformanceRecord.nf ?? {};

  const readiness = makeComputedReadiness0({
    semanticKImplFinalRecord: conformanceRecord,
    semanticKImplReady: conformanceNF.semanticKImplFinalReady === true,
    semanticConformanceReady: conformanceNF.semanticK0ConformanceReady === true,
  });
  ledger.push(makeLedgerEntry0(
    'computedSemanticReadiness',
    readiness.finalTheoremReady,
    readiness,
  ));

  if (purpose === 'final-theorem' && !readiness.finalTheoremReady) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticReadiness`,
      path: ['ComputedReadiness'],
      witness: {
        reason: 'semantic K0 conformance KBundle is not ready for final-theorem use',
        blockers: readiness.blockers,
        semanticConformanceProbe: compactRecord0(conformanceRecord),
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && readiness.finalTheoremReady;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'KBundleSemanticK0ConformanceSuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: finalTheoremReady ? 'final-theorem-ready' : 'development-only',

      predecessorKBundleAccepted: true,
      predecessorKBundleChecker: predecessorRecord.checker,
      predecessorKBundleDigest:
        predecessorRecord.Digest ?? predecessorRecord.digest,
      predecessorKBundleDevelopmentOnly: true,
      predecessorKBundlePublicTheoremEmissionAllowed: false,
      predecessorKBundleSupportedRules:
        predecessorNF.semanticKImplSupportedRules ?? [],
      predecessorKBundleMissingRules:
        predecessorNF.semanticKImplMissingRules ?? [],
      predecessorSemanticConformanceReady: false,

      semanticKImplDevelopmentAccepted: true,
      semanticKImplDevelopmentChecker: kimplRecord.checker,
      semanticKImplDevelopmentDigest: kimplRecord.Digest ?? kimplRecord.digest,
      semanticKImplDevelopmentOnly: true,
      semanticKImplPublicTheoremEmissionAllowed: false,
      semanticKImplSupportedRules: kimplNF.supportedSemanticRules ?? [],
      semanticKImplMissingRules: kimplNF.missingSemanticRules ?? [],
      semanticKImplKernelReady: kimplNF.semanticKernelReady === true,
      semanticFiniteRelNodeCount: kimplNF.semanticFiniteRelNodeCount ?? null,

      semanticConformanceChecker: conformanceRecord.checker,
      semanticConformanceDigest:
        conformanceRecord.Digest ?? conformanceRecord.digest,
      semanticConformanceReady: true,
      semanticK0ConformanceReady: true,
      semanticConformanceObligationCount:
        conformanceNF.semanticConformanceObligationCount ?? null,
      semanticConformanceCoveredRules:
        conformanceNF.semanticConformanceCoveredRules ?? [],
      semanticConformanceObligationDigests:
        conformanceNF.semanticConformanceObligationDigests ?? [],

      legacyBundleAccepted: predecessorNF.legacyBundleAccepted === true,
      legacyBundleDigest: predecessorNF.legacyBundleDigest ?? null,
      legacyKImplDigest: predecessorNF.legacyKImplDigest ?? null,
      legacyConformanceDigest:
        conformanceNF.legacyConformanceDigest
        ?? predecessorNF.legacyConformanceDigest
        ?? null,
      legacySigmaDigest: predecessorNF.legacySigmaDigest ?? null,
      legacyReflectionDigest: predecessorNF.legacyReflectionDigest ?? null,

      semanticSigmaReady: false,
      semanticReflectionReady: false,
      computedReadiness: readiness,
      computedReadinessDigest: digestCanonical0(readiness),
      developmentOnly: !finalTheoremReady,
      finalTheoremReady,
      publicTheoremEmissionAllowed: finalTheoremReady,
      finalTheoremRequiresAllSemanticSurfaces: true,
      bindingDigest: digestCanonical0(input.Binding),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeComputedReadiness0({
  semanticKImplFinalRecord,
  semanticKImplReady,
  semanticConformanceReady,
}) {
  const digest = semanticKImplFinalRecord.Digest
    ?? semanticKImplFinalRecord.digest
    ?? null;
  const blockers = [
    Object.freeze({
      coordinate: 'KImpl.SemanticRuleCoverage',
      ready: semanticKImplReady,
      checker: 'CheckSemanticK0Conformance0',
      reason: semanticKImplReady
        ? null
        : 'complete primitive semantic KImpl final readiness did not accept',
      digest,
    }),
    Object.freeze({
      coordinate: 'K0.SemanticConformance',
      ready: semanticConformanceReady,
      checker: 'CheckSemanticK0Conformance0',
      reason: semanticConformanceReady
        ? null
        : 'K0 local semantic conformance obligations did not accept',
      digest,
    }),
    Object.freeze({
      coordinate: 'Sigma.SemanticDerivations',
      ready: false,
      checker: null,
      reason: 'V53 and V54 remain registry entries rather than semantic-kernel derivations',
      digest: null,
    }),
    Object.freeze({
      coordinate: 'Reflection.SemanticSoundness',
      ready: false,
      checker: null,
      reason: 'reflection entries remain mappings rather than proof-producing checker refinements',
      digest: null,
    }),
  ];

  return Object.freeze({
    kind: 'KBundleComputedSemanticK0ConformanceReadiness0',
    version: CHECKER_VERSION,
    semanticKImplFinalReady: semanticKImplReady,
    semanticConformanceReady,
    semanticSigmaReady: false,
    semanticReflectionReady: false,
    blockers: Object.freeze(blockers),
    blockerCoordinates: Object.freeze(
      blockers.filter((entry) => !entry.ready).map((entry) => entry.coordinate),
    ),
    finalTheoremReady: blockers.every((entry) => entry.ready),
    publicTheoremEmissionAllowed: blockers.every((entry) => entry.ready),
  });
}

function validateShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'semantic K0 conformance KBundle input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'KBundleSemanticK0ConformanceSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic K0 conformance KBundle kind must be KBundleSemanticK0ConformanceSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic K0 conformance KBundle version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!KBUNDLE_K0CONFORMANCE_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic K0 conformance KBundle Purpose is unsupported',
      {
        actual: input.Purpose,
        supportedPurposes: [...KBUNDLE_K0CONFORMANCE_SUCCESSOR_PURPOSES0],
      },
    );
  }
  for (const field of [
    'SemanticKImpl',
    'K0',
    'K0SemanticConformance',
    'PSigma',
    'ReflectionRegistry',
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic K0 conformance KBundle is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.SemanticKImpl)) {
    return validationReject0(
      ['SemanticKImpl'],
      'semantic K0 conformance KBundle SemanticKImpl must be an object',
      { actual: typeof input.SemanticKImpl },
    );
  }
  if (input.SemanticKImpl.Purpose !== 'development') {
    return validationReject0(
      ['SemanticKImpl', 'Purpose'],
      'semantic K0 conformance KBundle input KImpl must remain development-purpose; final readiness is recomputed internally',
      { actual: input.SemanticKImpl.Purpose },
    );
  }
  if (!isPlainObject0(input.K0SemanticConformance)) {
    return validationReject0(
      ['K0SemanticConformance'],
      'semantic K0 conformance KBundle requires a semantic conformance suite object',
      { actual: typeof input.K0SemanticConformance },
    );
  }
  if (!isPlainObject0(input.Binding)
      || !sameCanonical0(input.Binding, KBUNDLE_K0CONFORMANCE_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'semantic K0 conformance KBundle checker binding must match the executable checker boundary',
      {
        expected: KBUNDLE_K0CONFORMANCE_SUCCESSOR_BINDING0,
        actual: input.Binding,
      },
    );
  }
  if (!isPlainObject0(input.Policy)
      || !sameCanonical0(input.Policy, KBUNDLE_K0CONFORMANCE_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic K0 conformance KBundle release policy must match the fail-closed policy',
      {
        expected: KBUNDLE_K0CONFORMANCE_SUCCESSOR_POLICY0,
        actual: input.Policy,
      },
    );
  }

  const allowed = new Set([
    'kind',
    'version',
    'Purpose',
    'SemanticKImpl',
    'K0',
    'K0SemanticConformance',
    'PSigma',
    'ReflectionRegistry',
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic K0 conformance KBundle rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  return validationAccept0({
    kind: 'KBundleSemanticK0ConformanceSuccessorShape0NF',
    purpose: input.Purpose,
  });
}

function validatePredecessorBundleBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    semanticKImplDevelopmentAccepted: true,
    semanticKImplFinalReady: true,
    semanticConformanceReady: false,
    legacyBundleAccepted: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorKBundle', 'NF', field],
        'FiniteRel predecessor KBundle did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(
    nf.semanticKImplSupportedRules,
    SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
  )) {
    return validationReject0(
      ['PredecessorKBundle', 'NF', 'semanticKImplSupportedRules'],
      'FiniteRel predecessor KBundle semantic rule set mismatch',
      {
        expected: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
        actual: nf.semanticKImplSupportedRules,
      },
    );
  }
  if (!sameCanonical0(nf.semanticKImplMissingRules, [])) {
    return validationReject0(
      ['PredecessorKBundle', 'NF', 'semanticKImplMissingRules'],
      'FiniteRel predecessor KBundle must expose an empty primitive missing-rule set',
      { expected: [], actual: nf.semanticKImplMissingRules },
    );
  }
  return validationAccept0({
    kind: 'KBundleK0ConformancePredecessorBoundary0NF',
    ...expected,
    semanticKImplSupportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
    semanticKImplMissingRules: [],
  });
}

function validateDevelopmentKImplBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    semanticProofAccepted: true,
    semanticKernelReady: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['SemanticKImpl', 'NF', field],
        'FiniteRel semantic KImpl did not preserve its development-purpose boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(
    nf.supportedSemanticRules,
    SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
  )) {
    return validationReject0(
      ['SemanticKImpl', 'NF', 'supportedSemanticRules'],
      'FiniteRel semantic KImpl supported-rule set mismatch',
      {
        expected: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
        actual: nf.supportedSemanticRules,
      },
    );
  }
  return validationAccept0({
    kind: 'KBundleK0ConformanceKImplDevelopmentBoundary0NF',
    ...expected,
    supportedSemanticRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
  });
}

function extractNodes0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0(
      {
        kind: 'KBundleK0ConformanceProofInput0NF',
        form: 'array',
        nodeCount: input.length,
      },
      { nodes: input },
    );
  }
  if (!isPlainObject0(input)) {
    return validationReject0(
      ['SemanticKImpl', 'SemanticKernel', 'ProofDAG'],
      'semantic proof DAG must be an array or object',
      { actual: typeof input },
    );
  }
  const nodes = input.nodes ?? input.ProofDAG ?? input.proofDAG;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['SemanticKImpl', 'SemanticKernel', 'ProofDAG', 'nodes'],
      'semantic proof DAG must provide a nodes array',
      { actual: typeof nodes },
    );
  }
  return validationAcceptWith0(
    {
      kind: 'KBundleK0ConformanceProofInput0NF',
      form: 'object',
      nodeCount: nodes.length,
    },
    { nodes },
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

function validationAcceptWith0(nf, extra) {
  return { ok: true, nf, ...extra };
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

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

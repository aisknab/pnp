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
  CheckKBundleTraceIndSuccessor0,
  makeKBundleTraceIndSuccessor0,
} from './pcc-kbundle-traceind-successor0.mjs';

import {
  CheckKImplFiniteExhaustFinalTheoremReadiness0,
  CheckKImplFiniteExhaustSuccessor0,
  makeKImplFiniteExhaustSuccessor0,
} from './pcc-kimpl-finiteexhaust-successor0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0,
} from './pcc-kernel-traceind-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

const PREDECESSOR_RULES0 = Object.freeze([
  'Eq',
  'Subst',
  'Record',
  'DAGInd',
  'LedgerInd',
  'OblTopoInd',
  'TraceInd',
]);

const FINITEEXHAUST_RULES0 = Object.freeze([
  ...PREDECESSOR_RULES0,
  'FiniteExhaust',
]);

export const KBUNDLE_FINITEEXHAUST_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const KBUNDLE_FINITEEXHAUST_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'KBundleSemanticFiniteExhaustReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKImplInputMustRemainDevelopmentPurpose: true,
  predecessorKBundleMustRemainDevelopmentOnly: true,
  predecessorKBundleCannotImplyFiniteExhaustReadiness: true,
  legacyConformanceIsStructuralOnly: true,
  legacySigmaRegistryIsStructuralOnly: true,
  legacyReflectionRegistryIsStructuralOnly: true,
  finalTheoremRequiresSemanticKImplReadiness: true,
  finalTheoremRequiresSemanticConformance: true,
  finalTheoremRequiresSemanticSigmaDerivations: true,
  finalTheoremRequiresSemanticReflectionSoundness: true,
  publicTheoremEmissionRequiresBundleFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const KBUNDLE_FINITEEXHAUST_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'KBundleSemanticFiniteExhaustCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorKBundleChecker: 'CheckKBundleTraceIndSuccessor0',
  semanticKImplChecker: 'CheckKImplFiniteExhaustSuccessor0',
  semanticKImplFinalChecker: 'CheckKImplFiniteExhaustFinalTheoremReadiness0',
});

export function makeKBundleFiniteExhaustSuccessor0({
  KImpl = makeSyntheticKImpl0(),
  SemanticProofDAG = makeSemanticProofDAG0(),
  K0 = makeKernelConformanceSuite0(),
  PSigma = makeSigmaRegistry0(),
  ReflectionRegistry = makeReflectionRegistry0(),
  Purpose = 'development',
} = {}) {
  if (!KBUNDLE_FINITEEXHAUST_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeKBundleFiniteExhaustSuccessor0 Purpose must be one of ${KBUNDLE_FINITEEXHAUST_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }

  return {
    kind: 'KBundleSemanticFiniteExhaustSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    SemanticKImpl: makeKImplFiniteExhaustSuccessor0({
      KImpl,
      SemanticProofDAG,
      Purpose: 'development',
    }),
    K0,
    PSigma,
    ReflectionRegistry,
    Binding: { ...KBUNDLE_FINITEEXHAUST_SUCCESSOR_BINDING0 },
    Policy: { ...KBUNDLE_FINITEEXHAUST_SUCCESSOR_POLICY0 },
  };
}

/**
 * Development-facing successor KBundle after FiniteExhaust. The TraceInd
 * KBundle is rerun on the filtered predecessor sub-DAG, then the complete
 * FiniteExhaust KImpl is checked independently. Legacy conformance, Sigma,
 * and reflection remain structural-only.
 */
export async function CheckKBundleFiniteExhaustSuccessor0(input) {
  return checkKBundleInternal0(input, {
    checker: 'CheckKBundleFiniteExhaustSuccessor0',
    requiredPurpose: null,
  });
}

/**
 * Explicit final-theorem gate. It rejects until primitive-rule coverage and
 * all remaining semantic KBundle surfaces are complete.
 */
export async function CheckKBundleFiniteExhaustFinalTheoremReadiness0(input) {
  return checkKBundleInternal0(input, {
    checker: 'CheckKBundleFiniteExhaustFinalTheoremReadiness0',
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
      reason: 'FiniteExhaust semantic KBundle final readiness requires a final-theorem purpose record',
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
    kind: 'KBundleFiniteExhaustPurpose0NF',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_TRACEIND0.includes(node?.RuleName),
  );
  const predecessorBundleInput = makeKBundleTraceIndSuccessor0({
    KImpl: input.SemanticKImpl.KImpl,
    SemanticProofDAG: makeSemanticProofDAG0(predecessorNodes),
    K0: input.K0,
    PSigma: input.PSigma,
    ReflectionRegistry: input.ReflectionRegistry,
    Purpose: 'development',
  });

  const predecessorCall = await callChecker0(
    'CheckKBundleTraceIndSuccessor0',
    () => CheckKBundleTraceIndSuccessor0(predecessorBundleInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundleTraceIndSuccessor0',
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
        reason: 'TraceInd predecessor KBundle rejected the seven-rule semantic base',
        predecessorNodeIds: predecessorNodes.map((node) => node?.id ?? null),
        inner: compactReject0(predecessorRecord),
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

  const developmentKImplInput = {
    ...input.SemanticKImpl,
    Purpose: 'development',
  };
  const developmentCall = await callChecker0(
    'CheckKImplFiniteExhaustSuccessor0',
    () => CheckKImplFiniteExhaustSuccessor0(developmentKImplInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKImplFiniteExhaustSuccessor0',
    developmentCall.ok && developmentCall.record.tag === 'accept',
    developmentCall.ok ? developmentCall.record : developmentCall.witness,
  ));

  if (!developmentCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImpl.exception`,
      path: ['SemanticKImpl'],
      witness: developmentCall.witness,
      ledger,
    });
  }

  const developmentRecord = developmentCall.record;
  if (developmentRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImpl`,
      path: ['SemanticKImpl'],
      witness: {
        reason: 'FiniteExhaust development semantic KImpl successor rejected',
        inner: compactReject0(developmentRecord),
      },
      ledger,
    });
  }

  const developmentNF = developmentRecord.NF ?? developmentRecord.nf ?? {};
  const developmentBoundary = validateDevelopmentKImplBoundary0(developmentNF);
  ledger.push(makeLedgerEntry0(
    'semanticKImplDevelopmentBoundary',
    developmentBoundary.ok,
    developmentBoundary.nf ?? developmentBoundary.witness,
  ));
  if (!developmentBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticKImplDevelopmentBoundary`,
      developmentBoundary,
      ledger,
    );
  }

  const finalKImplInput = {
    ...input.SemanticKImpl,
    Purpose: 'final-theorem',
  };
  const finalCall = await callChecker0(
    'CheckKImplFiniteExhaustFinalTheoremReadiness0',
    () => CheckKImplFiniteExhaustFinalTheoremReadiness0(finalKImplInput),
  );
  if (!finalCall.ok) {
    ledger.push(makeLedgerEntry0(
      'CheckKImplFiniteExhaustFinalTheoremReadiness0',
      false,
      finalCall.witness,
    ));
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImplFinal.exception`,
      path: ['SemanticKImpl'],
      witness: finalCall.witness,
      ledger,
    });
  }

  const finalRecord = finalCall.record;
  const semanticKImplFinalReady = isFinalReadyAccept0(finalRecord);
  ledger.push(makeLedgerEntry0(
    'CheckKImplFiniteExhaustFinalTheoremReadiness0',
    semanticKImplFinalReady,
    finalRecord,
  ));

  const readiness = makeComputedReadiness0({
    semanticKImplFinalReady,
    finalKImplRecord: finalRecord,
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
        reason: 'FiniteExhaust semantic KBundle is not ready for final-theorem use',
        blockers: readiness.blockers,
        semanticKImplFinalProbe: compactRecord0(finalRecord),
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && readiness.finalTheoremReady;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'KBundleSemanticFiniteExhaustSuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: finalTheoremReady ? 'final-theorem-ready' : 'development-only',

      predecessorKBundleAccepted: true,
      predecessorKBundleChecker: predecessorRecord.checker,
      predecessorKBundleDigest: predecessorRecord.Digest ?? predecessorRecord.digest,
      predecessorKBundleDevelopmentOnly: true,
      predecessorKBundlePublicTheoremEmissionAllowed: false,
      predecessorKBundleSupportedRules: predecessorNF.semanticKImplSupportedRules ?? [],
      predecessorKBundleMissingRules: predecessorNF.semanticKImplMissingRules ?? [],

      semanticKImplDevelopmentAccepted: true,
      semanticKImplDevelopmentChecker: developmentRecord.checker,
      semanticKImplDevelopmentDigest: developmentRecord.Digest ?? developmentRecord.digest,
      semanticKImplDevelopmentOnly: true,
      semanticKImplPublicTheoremEmissionAllowed: false,
      semanticKImplSupportedRules: developmentNF.supportedSemanticRules ?? [],
      semanticKImplMissingRules: developmentNF.missingSemanticRules ?? [],
      semanticFiniteExhaustNodeCount:
        developmentNF.semanticFiniteExhaustNodeCount ?? null,

      semanticKImplFinalChecker: finalRecord.checker,
      semanticKImplFinalProbeAccepted: finalRecord.tag === 'accept',
      semanticKImplFinalProbeDigest: finalRecord.Digest ?? finalRecord.digest,
      semanticKImplFinalReady,

      legacyBundleAccepted: predecessorNF.legacyBundleAccepted === true,
      legacyBundleDigest: predecessorNF.legacyBundleDigest ?? null,
      legacyKImplDigest: predecessorNF.legacyKImplDigest ?? null,
      legacyConformanceDigest: predecessorNF.legacyConformanceDigest ?? null,
      legacySigmaDigest: predecessorNF.legacySigmaDigest ?? null,
      legacyReflectionDigest: predecessorNF.legacyReflectionDigest ?? null,

      legacyConformanceAccepted: true,
      legacyConformanceSemanticStatus: 'structural-only',
      semanticConformanceReady: false,
      legacySigmaAccepted: true,
      legacySigmaSemanticStatus: 'registry-shape-only',
      semanticSigmaReady: false,
      legacyReflectionAccepted: true,
      legacyReflectionSemanticStatus: 'mapping-shape-only',
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
  semanticKImplFinalReady,
  finalKImplRecord,
}) {
  const blockers = [
    {
      coordinate: 'KImpl.SemanticRuleCoverage',
      ready: semanticKImplFinalReady,
      checker: 'CheckKImplFiniteExhaustFinalTheoremReadiness0',
      reason: semanticKImplFinalReady
        ? null
        : 'semantic primitive-rule coverage remains incomplete after FiniteExhaust',
      digest: finalKImplRecord.Digest ?? finalKImplRecord.digest ?? null,
    },
    {
      coordinate: 'K0.SemanticConformance',
      ready: false,
      checker: null,
      reason: 'the current conformance suite checks primitive names and shape, not semantic derivations',
      digest: null,
    },
    {
      coordinate: 'Sigma.SemanticDerivations',
      ready: false,
      checker: null,
      reason: 'V53 and V54 remain registry entries rather than semantic-kernel derivations',
      digest: null,
    },
    {
      coordinate: 'Reflection.SemanticSoundness',
      ready: false,
      checker: null,
      reason: 'reflection entries remain mappings rather than proof-producing checker refinements',
      digest: null,
    },
  ];

  return Object.freeze({
    kind: 'KBundleComputedSemanticFiniteExhaustReadiness0',
    version: CHECKER_VERSION,
    semanticKImplFinalReady,
    semanticConformanceReady: false,
    semanticSigmaReady: false,
    semanticReflectionReady: false,
    blockers: Object.freeze(blockers.map((entry) => Object.freeze(entry))),
    blockerCoordinates: Object.freeze(
      blockers.filter((entry) => !entry.ready).map((entry) => entry.coordinate),
    ),
    finalTheoremReady: blockers.every((entry) => entry.ready),
    publicTheoremEmissionAllowed: blockers.every((entry) => entry.ready),
  });
}

function validateShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'FiniteExhaust semantic KBundle input must be an object', {
      actual: typeof input,
    });
  }

  if (input.kind !== 'KBundleSemanticFiniteExhaustSuccessor0') {
    return validationReject0(
      ['kind'],
      'FiniteExhaust semantic KBundle kind must be KBundleSemanticFiniteExhaustSuccessor0',
      { actual: input.kind },
    );
  }

  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `FiniteExhaust semantic KBundle version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }

  if (!KBUNDLE_FINITEEXHAUST_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'FiniteExhaust semantic KBundle Purpose is unsupported',
      {
        actual: input.Purpose,
        supportedPurposes: [...KBUNDLE_FINITEEXHAUST_SUCCESSOR_PURPOSES0],
      },
    );
  }

  for (const field of [
    'SemanticKImpl',
    'K0',
    'PSigma',
    'ReflectionRegistry',
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'FiniteExhaust semantic KBundle is missing a required field',
        { field },
      );
    }
  }

  if (!isPlainObject0(input.SemanticKImpl)) {
    return validationReject0(
      ['SemanticKImpl'],
      'FiniteExhaust semantic KBundle SemanticKImpl must be an object',
      { actual: typeof input.SemanticKImpl },
    );
  }

  if (input.SemanticKImpl.Purpose !== 'development') {
    return validationReject0(
      ['SemanticKImpl', 'Purpose'],
      'FiniteExhaust semantic KBundle input KImpl must remain development-purpose; final readiness is recomputed internally',
      { actual: input.SemanticKImpl.Purpose },
    );
  }

  if (!isPlainObject0(input.Binding)
      || !sameCanonical0(input.Binding, KBUNDLE_FINITEEXHAUST_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'FiniteExhaust semantic KBundle checker binding must match the executable checker boundary',
      {
        expected: KBUNDLE_FINITEEXHAUST_SUCCESSOR_BINDING0,
        actual: input.Binding,
      },
    );
  }

  if (!isPlainObject0(input.Policy)
      || !sameCanonical0(input.Policy, KBUNDLE_FINITEEXHAUST_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'FiniteExhaust semantic KBundle release policy must match the fail-closed policy',
      {
        expected: KBUNDLE_FINITEEXHAUST_SUCCESSOR_POLICY0,
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
    'PSigma',
    'ReflectionRegistry',
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'FiniteExhaust semantic KBundle rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  return validationAccept0({
    kind: 'KBundleSemanticFiniteExhaustSuccessorShape0NF',
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
    legacyBundleAccepted: true,
  };

  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorKBundle', 'NF', field],
        'TraceInd predecessor KBundle did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }

  if (!sameCanonical0(nf.semanticKImplSupportedRules, PREDECESSOR_RULES0)) {
    return validationReject0(
      ['PredecessorKBundle', 'NF', 'semanticKImplSupportedRules'],
      'TraceInd predecessor KBundle semantic rule set mismatch',
      { expected: PREDECESSOR_RULES0, actual: nf.semanticKImplSupportedRules },
    );
  }

  return validationAccept0({
    kind: 'KBundleFiniteExhaustPredecessorBoundary0NF',
    ...expected,
    semanticKImplSupportedRules: [...PREDECESSOR_RULES0],
  });
}

function validateDevelopmentKImplBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    semanticProofAccepted: true,
  };

  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['SemanticKImpl', 'NF', field],
        'FiniteExhaust semantic KImpl did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }

  if (!sameCanonical0(nf.supportedSemanticRules, FINITEEXHAUST_RULES0)) {
    return validationReject0(
      ['SemanticKImpl', 'NF', 'supportedSemanticRules'],
      'FiniteExhaust semantic KImpl supported-rule set mismatch',
      { expected: FINITEEXHAUST_RULES0, actual: nf.supportedSemanticRules },
    );
  }

  return validationAccept0({
    kind: 'KBundleFiniteExhaustKImplDevelopmentBoundary0NF',
    ...expected,
    supportedSemanticRules: [...FINITEEXHAUST_RULES0],
  });
}

function extractNodes0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0(
      { kind: 'KBundleFiniteExhaustProofInput0NF', form: 'array', nodeCount: input.length },
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
    { kind: 'KBundleFiniteExhaustProofInput0NF', form: 'object', nodeCount: nodes.length },
    { nodes },
  );
}

function isFinalReadyAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return (
    record?.tag === 'accept'
    && nf?.finalTheoremReady === true
    && nf?.publicTheoremEmissionAllowed === true
    && nf?.semanticKernelReady === true
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

function compactReject0(record) {
  return {
    checker: record?.checker ?? null,
    coord: record?.Coord ?? record?.coord ?? null,
    path: record?.Path ?? record?.path ?? null,
    witness: record?.Witness ?? record?.witness ?? null,
    digest: record?.Digest ?? record?.digest ?? null,
  };
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

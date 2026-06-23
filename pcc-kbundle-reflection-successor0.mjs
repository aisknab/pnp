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
  CheckKBundleSigmaSuccessor0,
  makeKBundleSigmaSuccessor0,
} from './pcc-kbundle-sigma-successor0.mjs';

import {
  CheckKImplFiniteRelSuccessor0,
  makeKImplFiniteRelSuccessor0,
} from './pcc-kimpl-finiterel-successor0.mjs';

import {
  makeSemanticK0ConformanceSuite0,
} from './pcc-k0-semantic-conformance0.mjs';

import {
  makeSemanticSigmaSuite0,
} from './pcc-sigma-semantic0.mjs';

import {
  CheckSemanticReflection0,
  SEMANTIC_REFLECTION_REQUIRED_CHECKERS0,
  makeSemanticReflectionInput0,
  makeSemanticReflectionSuite0,
} from './pcc-reflection-semantic0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
} from './pcc-kernel-finiterel-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

export const KBUNDLE_REFLECTION_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const KBUNDLE_REFLECTION_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'KBundleSemanticReflectionReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKImplInputMustRemainDevelopmentPurpose: true,
  predecessorKBundleMustRemainDevelopmentOnly: true,
  predecessorKBundleCannotImplyReflectionReadiness: true,
  semanticK0ConformanceMustRemainReady: true,
  semanticSigmaDerivationsMustRemainReady: true,
  semanticReflectionRefinementsMustBeComputed: true,
  legacyReflectionRegistryConsumedOnlyThroughSemanticChecker: true,
  boundedExecutableReflectionRefinementsOnly: true,
  unrestrictedCheckerSoundnessNotClaimed: true,
  finalTheoremRequiresSemanticKImplReadiness: true,
  finalTheoremRequiresSemanticConformance: true,
  finalTheoremRequiresSemanticSigmaDerivations: true,
  finalTheoremRequiresSemanticReflectionSoundnessSurface: true,
  publicTheoremEmissionRequiresBundleFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const KBUNDLE_REFLECTION_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'KBundleSemanticReflectionCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorKBundleChecker: 'CheckKBundleSigmaSuccessor0',
  semanticKImplChecker: 'CheckKImplFiniteRelSuccessor0',
  semanticReflectionChecker: 'CheckSemanticReflection0',
});

export function makeKBundleReflectionSuccessor0({
  KImpl = makeSyntheticKImpl0(),
  SemanticProofDAG = makeSemanticProofDAG0(),
  K0 = makeKernelConformanceSuite0(),
  K0SemanticConformance = makeSemanticK0ConformanceSuite0({ K0 }),
  PSigma = makeSigmaRegistry0(),
  SigmaSemanticDerivations = makeSemanticSigmaSuite0({ PSigma }),
  ReflectionRegistry = makeReflectionRegistry0(),
  ReflectionSemanticRefinements = makeSemanticReflectionSuite0({
    ReflectionRegistry,
  }),
  Purpose = 'development',
} = {}) {
  if (!KBUNDLE_REFLECTION_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeKBundleReflectionSuccessor0 Purpose must be one of ${KBUNDLE_REFLECTION_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'KBundleSemanticReflectionSuccessor0',
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
    SigmaSemanticDerivations,
    ReflectionRegistry,
    ReflectionSemanticRefinements,
    Binding: { ...KBUNDLE_REFLECTION_SUCCESSOR_BINDING0 },
    Policy: { ...KBUNDLE_REFLECTION_SUCCESSOR_POLICY0 },
  };
}

export async function CheckKBundleReflectionSuccessor0(input) {
  return checkKBundleInternal0(input, {
    checker: 'CheckKBundleReflectionSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckKBundleReflectionFinalTheoremReadiness0(input) {
  return checkKBundleInternal0(input, {
    checker: 'CheckKBundleReflectionFinalTheoremReadiness0',
    requiredPurpose: 'final-theorem',
  });
}

async function checkKBundleInternal0(input, { checker, requiredPurpose }) {
  const ledger = [];
  const shape = validateShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  if (requiredPurpose !== null && input.Purpose !== requiredPurpose) {
    const witness = {
      reason: 'semantic reflection KBundle final readiness requires a final-theorem purpose record',
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
    kind: 'KBundleReflectionPurpose0NF',
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
  const predecessorInput = makeKBundleSigmaSuccessor0({
    KImpl: input.SemanticKImpl.KImpl,
    SemanticProofDAG: makeSemanticProofDAG0(predecessorNodes),
    K0: input.K0,
    K0SemanticConformance: input.K0SemanticConformance,
    PSigma: input.PSigma,
    SigmaSemanticDerivations: input.SigmaSemanticDerivations,
    ReflectionRegistry: input.ReflectionRegistry,
    Purpose: 'development',
  });
  const predecessorCall = await callChecker0(
    'CheckKBundleSigmaSuccessor0',
    () => CheckKBundleSigmaSuccessor0(predecessorInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundleSigmaSuccessor0',
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
        reason: 'semantic Sigma predecessor KBundle rejected before reflection upgrade',
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

  const reflectionCall = await callChecker0(
    'CheckSemanticReflection0',
    () => CheckSemanticReflection0(makeSemanticReflectionInput0({
      KImpl: input.SemanticKImpl,
      K0: input.K0,
      K0SemanticConformance: input.K0SemanticConformance,
      PSigma: input.PSigma,
      SigmaSemanticDerivations: input.SigmaSemanticDerivations,
      ReflectionRegistry: input.ReflectionRegistry,
      SemanticReflection: input.ReflectionSemanticRefinements,
    })),
  );
  ledger.push(makeLedgerEntry0(
    'CheckSemanticReflection0',
    reflectionCall.ok && reflectionCall.record.tag === 'accept',
    reflectionCall.ok ? reflectionCall.record : reflectionCall.witness,
  ));
  if (!reflectionCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticReflection.exception`,
      path: ['ReflectionSemanticRefinements'],
      witness: reflectionCall.witness,
      ledger,
    });
  }
  const reflectionRecord = reflectionCall.record;
  if (reflectionRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticReflection`,
      path: ['ReflectionSemanticRefinements'],
      witness: {
        reason: 'semantic reflection checker rejected the refinement surface',
        inner: compactRecord0(reflectionRecord),
      },
      ledger,
    });
  }
  const reflectionNF = reflectionRecord.NF ?? reflectionRecord.nf ?? {};
  const reflectionBoundary = validateSemanticReflectionBoundary0(reflectionNF);
  ledger.push(makeLedgerEntry0(
    'semanticReflectionBoundary',
    reflectionBoundary.ok,
    reflectionBoundary.nf ?? reflectionBoundary.witness,
  ));
  if (!reflectionBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticReflectionBoundary`,
      reflectionBoundary,
      ledger,
    );
  }

  const readiness = makeComputedReadiness0({
    reflectionRecord,
    reflectionNF,
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
        reason: 'semantic reflection KBundle is not ready for final-theorem use',
        blockers: readiness.blockers,
        semanticReflectionProbe: compactRecord0(reflectionRecord),
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && readiness.finalTheoremReady;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'KBundleSemanticReflectionSuccessor0NF',
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
      predecessorSemanticK0ConformanceReady: true,
      predecessorSemanticSigmaReady: true,
      predecessorSemanticReflectionReady: false,

      semanticKImplDevelopmentAccepted: true,
      semanticKImplDevelopmentChecker: kimplRecord.checker,
      semanticKImplDevelopmentDigest:
        kimplRecord.Digest ?? kimplRecord.digest,
      semanticKImplDevelopmentOnly: true,
      semanticKImplPublicTheoremEmissionAllowed: false,
      semanticKImplSupportedRules: kimplNF.supportedSemanticRules ?? [],
      semanticKImplMissingRules: kimplNF.missingSemanticRules ?? [],
      semanticKImplKernelReady: kimplNF.semanticKernelReady === true,
      semanticFiniteRelNodeCount: kimplNF.semanticFiniteRelNodeCount ?? null,

      semanticK0ConformanceReady: true,
      semanticK0ConformanceDigest:
        reflectionNF.semanticK0ConformanceDigest ?? null,
      semanticSigmaReady: true,
      semanticSigmaDigest: reflectionNF.semanticSigmaDigest ?? null,
      semanticSigmaTheorems: reflectionNF.semanticSigmaTheorems ?? [],
      semanticReflectionChecker: reflectionRecord.checker,
      semanticReflectionDigest:
        reflectionRecord.Digest ?? reflectionRecord.digest,
      semanticReflectionReady: true,
      semanticReflectionSoundnessSurfaceReady: true,
      semanticReflectionCheckers:
        reflectionNF.semanticReflectionCheckers ?? [],
      semanticReflectionCount:
        reflectionNF.semanticReflectionCount ?? null,
      semanticReflectionRefinementDigests:
        reflectionNF.semanticReflectionRefinementDigests ?? [],
      boundedExecutableReflectionRefinementsOnly: true,
      unrestrictedCheckerSoundnessNotClaimed: true,

      legacyBundleAccepted: predecessorNF.legacyBundleAccepted === true,
      legacyBundleDigest: predecessorNF.legacyBundleDigest ?? null,
      legacyKImplDigest: predecessorNF.legacyKImplDigest ?? null,
      legacyConformanceDigest: predecessorNF.legacyConformanceDigest ?? null,
      legacySigmaDigest: predecessorNF.legacySigmaDigest ?? null,
      legacyReflectionDigest:
        reflectionNF.legacyReflectionDigest
        ?? predecessorNF.legacyReflectionDigest
        ?? null,

      computedReadiness: readiness,
      computedReadinessDigest: digestCanonical0(readiness),
      developmentOnly: !finalTheoremReady,
      finalTheoremReady,
      publicTheoremEmissionAllowed: finalTheoremReady,
      finalTheoremRequiresAllSemanticBundleSurfaces: true,
      bindingDigest: digestCanonical0(input.Binding),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeComputedReadiness0({ reflectionRecord, reflectionNF }) {
  const reflectionDigest = reflectionRecord.Digest
    ?? reflectionRecord.digest
    ?? null;
  const blockers = [
    Object.freeze({
      coordinate: 'KImpl.SemanticRuleCoverage',
      ready: reflectionNF.semanticKImplFinalReady === true,
      checker: 'CheckSemanticReflection0',
      reason: reflectionNF.semanticKImplFinalReady === true
        ? null
        : 'complete primitive semantic KImpl final readiness did not remain accepted',
      digest: reflectionNF.semanticKImplFinalDigest ?? reflectionDigest,
    }),
    Object.freeze({
      coordinate: 'K0.SemanticConformance',
      ready: reflectionNF.semanticK0ConformanceReady === true,
      checker: 'CheckSemanticReflection0',
      reason: reflectionNF.semanticK0ConformanceReady === true
        ? null
        : 'semantic K0 conformance did not remain accepted',
      digest: reflectionNF.semanticK0ConformanceDigest ?? reflectionDigest,
    }),
    Object.freeze({
      coordinate: 'Sigma.SemanticDerivations',
      ready: reflectionNF.semanticSigmaReady === true,
      checker: 'CheckSemanticReflection0',
      reason: reflectionNF.semanticSigmaReady === true
        ? null
        : 'bounded semantic Sigma derivations did not remain accepted',
      digest: reflectionNF.semanticSigmaDigest ?? reflectionDigest,
    }),
    Object.freeze({
      coordinate: 'Reflection.SemanticSoundness',
      ready: reflectionNF.semanticReflectionSoundnessSurfaceReady === true,
      checker: 'CheckSemanticReflection0',
      reason: reflectionNF.semanticReflectionSoundnessSurfaceReady === true
        ? null
        : 'required bounded executable reflection refinements did not accept',
      digest: reflectionDigest,
      scope: 'bounded-executable-refinement-surface',
      unrestrictedCheckerSoundnessNotClaimed: true,
    }),
  ];
  return Object.freeze({
    kind: 'KBundleComputedSemanticReflectionReadiness0',
    version: CHECKER_VERSION,
    semanticKImplFinalReady: reflectionNF.semanticKImplFinalReady === true,
    semanticConformanceReady:
      reflectionNF.semanticK0ConformanceReady === true,
    semanticSigmaReady: reflectionNF.semanticSigmaReady === true,
    semanticReflectionReady:
      reflectionNF.semanticReflectionSoundnessSurfaceReady === true,
    boundedExecutableReflectionRefinementsOnly: true,
    unrestrictedCheckerSoundnessNotClaimed: true,
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
    return validationReject0([], 'semantic reflection KBundle input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'KBundleSemanticReflectionSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic reflection KBundle kind must be KBundleSemanticReflectionSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic reflection KBundle version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!KBUNDLE_REFLECTION_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic reflection KBundle Purpose is unsupported',
      { actual: input.Purpose },
    );
  }
  for (const field of [
    'SemanticKImpl',
    'K0',
    'K0SemanticConformance',
    'PSigma',
    'SigmaSemanticDerivations',
    'ReflectionRegistry',
    'ReflectionSemanticRefinements',
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic reflection KBundle is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.SemanticKImpl)) {
    return validationReject0(
      ['SemanticKImpl'],
      'semantic reflection KBundle SemanticKImpl must be an object',
      { actual: typeof input.SemanticKImpl },
    );
  }
  if (input.SemanticKImpl.Purpose !== 'development') {
    return validationReject0(
      ['SemanticKImpl', 'Purpose'],
      'semantic reflection KBundle input KImpl must remain development-purpose; final readiness is recomputed internally',
      { actual: input.SemanticKImpl.Purpose },
    );
  }
  if (!isPlainObject0(input.ReflectionSemanticRefinements)) {
    return validationReject0(
      ['ReflectionSemanticRefinements'],
      'semantic reflection KBundle requires a semantic reflection suite object',
      { actual: typeof input.ReflectionSemanticRefinements },
    );
  }
  if (!sameCanonical0(input.Binding, KBUNDLE_REFLECTION_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'semantic reflection KBundle checker binding must match the executable checker boundary',
      { expected: KBUNDLE_REFLECTION_SUCCESSOR_BINDING0, actual: input.Binding },
    );
  }
  if (!sameCanonical0(input.Policy, KBUNDLE_REFLECTION_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic reflection KBundle release policy must match the fail-closed policy',
      { expected: KBUNDLE_REFLECTION_SUCCESSOR_POLICY0, actual: input.Policy },
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
    'SigmaSemanticDerivations',
    'ReflectionRegistry',
    'ReflectionSemanticRefinements',
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic reflection KBundle rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'KBundleSemanticReflectionSuccessorShape0NF',
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
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticSigmaDerivationsReady: true,
    semanticReflectionReady: false,
    legacyBundleAccepted: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorKBundle', 'NF', field],
        'semantic Sigma predecessor KBundle did not preserve its development-only boundary',
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
      'semantic Sigma predecessor KBundle supported-rule set mismatch',
      { actual: nf.semanticKImplSupportedRules },
    );
  }
  if (!sameCanonical0(nf.semanticKImplMissingRules, [])) {
    return validationReject0(
      ['PredecessorKBundle', 'NF', 'semanticKImplMissingRules'],
      'semantic Sigma predecessor KBundle must expose an empty primitive missing-rule set',
      { actual: nf.semanticKImplMissingRules },
    );
  }
  if (!sameCanonical0(
    nf.computedReadiness?.blockerCoordinates,
    ['Reflection.SemanticSoundness'],
  )) {
    return validationReject0(
      ['PredecessorKBundle', 'NF', 'computedReadiness', 'blockerCoordinates'],
      'semantic Sigma predecessor KBundle blocker set mismatch',
      { actual: nf.computedReadiness?.blockerCoordinates },
    );
  }
  return validationAccept0({
    kind: 'KBundleReflectionPredecessorBoundary0NF',
    ...expected,
    semanticKImplSupportedRules:
      [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
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
      { actual: nf.supportedSemanticRules },
    );
  }
  return validationAccept0({
    kind: 'KBundleReflectionKImplDevelopmentBoundary0NF',
    ...expected,
    supportedSemanticRules:
      [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
  });
}

function validateSemanticReflectionBoundary0(nf) {
  const expected = {
    semanticReflectionReady: true,
    semanticReflectionContractReady: true,
    semanticReflectionSoundnessSurfaceReady: true,
    semanticKImplFinalReady: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    boundedExecutableRefinementsOnly: true,
    unrestrictedCheckerSoundnessNotClaimed: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['ReflectionSemanticRefinements', 'NF', field],
        'semantic reflection checker readiness boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(
    nf.semanticReflectionCheckers,
    SEMANTIC_REFLECTION_REQUIRED_CHECKERS0,
  )) {
    return validationReject0(
      ['ReflectionSemanticRefinements', 'NF', 'semanticReflectionCheckers'],
      'semantic reflection checker coverage mismatch',
      {
        expected: [...SEMANTIC_REFLECTION_REQUIRED_CHECKERS0],
        actual: nf.semanticReflectionCheckers,
      },
    );
  }
  if (nf.semanticReflectionCount !== SEMANTIC_REFLECTION_REQUIRED_CHECKERS0.length) {
    return validationReject0(
      ['ReflectionSemanticRefinements', 'NF', 'semanticReflectionCount'],
      'semantic reflection refinement count mismatch',
      {
        expected: SEMANTIC_REFLECTION_REQUIRED_CHECKERS0.length,
        actual: nf.semanticReflectionCount,
      },
    );
  }
  return validationAccept0({
    kind: 'KBundleReflectionSemanticBoundary0NF',
    ...expected,
    semanticReflectionCheckers:
      [...SEMANTIC_REFLECTION_REQUIRED_CHECKERS0],
  });
}

function extractNodes0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0({
      kind: 'KBundleReflectionProofInput0NF',
      form: 'array',
      nodeCount: input.length,
    }, { nodes: input });
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
  return validationAcceptWith0({
    kind: 'KBundleReflectionProofInput0NF',
    form: 'object',
    nodeCount: nodes.length,
  }, { nodes });
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
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

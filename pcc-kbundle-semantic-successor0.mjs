import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckKBundle0,
  makeKernelConformanceSuite0,
  makeReflectionRegistry0,
  makeSigmaRegistry0,
  makeSyntheticKImpl0,
} from './pcc-kimpl0.mjs';

import {
  CheckKImplDAGIndFinalTheoremReadiness0,
  CheckKImplDAGIndSuccessor0,
  makeKImplDAGIndSuccessor0,
} from './pcc-kimpl-dagind-successor0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

export const KBUNDLE_SEMANTIC_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const KBUNDLE_SEMANTIC_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'KBundleSemanticReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKImplInputMustRemainDevelopmentPurpose: true,
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

export const KBUNDLE_SEMANTIC_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'KBundleSemanticCheckerBinding0',
  version: CHECKER_VERSION,
  semanticKImplChecker: 'CheckKImplDAGIndSuccessor0',
  semanticKImplFinalChecker: 'CheckKImplDAGIndFinalTheoremReadiness0',
  legacyBundleChecker: 'CheckKBundle0',
});

export function makeKBundleSemanticSuccessor0({
  KImpl = makeSyntheticKImpl0(),
  SemanticProofDAG = makeSemanticProofDAG0(),
  K0 = makeKernelConformanceSuite0(),
  PSigma = makeSigmaRegistry0(),
  ReflectionRegistry = makeReflectionRegistry0(),
  Purpose = 'development',
} = {}) {
  if (!KBUNDLE_SEMANTIC_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeKBundleSemanticSuccessor0 Purpose must be one of ${KBUNDLE_SEMANTIC_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }

  return {
    kind: 'KBundleSemanticSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    SemanticKImpl: makeKImplDAGIndSuccessor0({
      KImpl,
      SemanticProofDAG,
      Purpose: 'development',
    }),
    K0,
    PSigma,
    ReflectionRegistry,
    Binding: { ...KBUNDLE_SEMANTIC_SUCCESSOR_BINDING0 },
    Policy: { ...KBUNDLE_SEMANTIC_SUCCESSOR_POLICY0 },
  };
}

/**
 * Development-facing KBundle checker. Legacy conformance, Sigma, and reflection
 * surfaces are still run, but their acceptance is explicitly classified as
 * structural-only. The computed readiness record is the only final gate input.
 */
export async function CheckKBundleSemanticSuccessor0(input) {
  return checkKBundleSemanticInternal0(input, {
    checker: 'CheckKBundleSemanticSuccessor0',
    requiredPurpose: null,
  });
}

/**
 * Explicit final-theorem KBundle gate. It cannot be enabled by booleans inside
 * the bundle and rejects until every computed semantic surface is ready.
 */
export async function CheckKBundleSemanticFinalTheoremReadiness0(input) {
  return checkKBundleSemanticInternal0(input, {
    checker: 'CheckKBundleSemanticFinalTheoremReadiness0',
    requiredPurpose: 'final-theorem',
  });
}

async function checkKBundleSemanticInternal0(input, {
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
      reason: 'semantic KBundle final readiness requires a final-theorem purpose record',
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
    kind: 'KBundleSemanticPurpose0NF',
    purpose,
  }));

  const developmentKImplInput = {
    ...input.SemanticKImpl,
    Purpose: 'development',
  };
  const developmentKImplCall = await callChecker0(
    'CheckKImplDAGIndSuccessor0',
    () => CheckKImplDAGIndSuccessor0(developmentKImplInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKImplDAGIndSuccessor0',
    developmentKImplCall.ok && developmentKImplCall.record.tag === 'accept',
    developmentKImplCall.ok
      ? developmentKImplCall.record
      : developmentKImplCall.witness,
  ));

  if (!developmentKImplCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImpl.exception`,
      path: ['SemanticKImpl'],
      witness: developmentKImplCall.witness,
      ledger,
    });
  }

  const developmentKImplRecord = developmentKImplCall.record;
  if (developmentKImplRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImpl`,
      path: ['SemanticKImpl'],
      witness: {
        reason: 'development semantic KImpl successor rejected',
        inner: compactReject0(developmentKImplRecord),
      },
      ledger,
    });
  }

  const developmentKImplNF = developmentKImplRecord.NF
    ?? developmentKImplRecord.nf
    ?? {};
  const developmentBoundary = validateDevelopmentKImplBoundary0(
    developmentKImplNF,
  );
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
  const finalKImplCall = await callChecker0(
    'CheckKImplDAGIndFinalTheoremReadiness0',
    () => CheckKImplDAGIndFinalTheoremReadiness0(finalKImplInput),
  );
  if (!finalKImplCall.ok) {
    ledger.push(makeLedgerEntry0(
      'CheckKImplDAGIndFinalTheoremReadiness0',
      false,
      finalKImplCall.witness,
    ));
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKImplFinal.exception`,
      path: ['SemanticKImpl'],
      witness: finalKImplCall.witness,
      ledger,
    });
  }

  const finalKImplRecord = finalKImplCall.record;
  const semanticKImplFinalReady = isFinalReadyAccept0(finalKImplRecord);
  ledger.push(makeLedgerEntry0(
    'CheckKImplDAGIndFinalTheoremReadiness0',
    semanticKImplFinalReady,
    finalKImplRecord,
  ));

  const legacyBundleInput = {
    KImpl: input.SemanticKImpl.KImpl,
    K0: input.K0,
    PSigma: input.PSigma,
    ReflectionRegistry: input.ReflectionRegistry,
  };
  const legacyBundleCall = await callChecker0(
    'CheckKBundle0',
    () => CheckKBundle0(legacyBundleInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundle0',
    legacyBundleCall.ok && legacyBundleCall.record.tag === 'accept',
    legacyBundleCall.ok ? legacyBundleCall.record : legacyBundleCall.witness,
  ));

  if (!legacyBundleCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyBundle.exception`,
      path: ['LegacyBundle'],
      witness: legacyBundleCall.witness,
      ledger,
    });
  }

  const legacyBundleRecord = legacyBundleCall.record;
  if (legacyBundleRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyBundle`,
      path: ['LegacyBundle'],
      witness: {
        reason: 'legacy KBundle structural checker rejected',
        inner: compactReject0(legacyBundleRecord),
      },
      ledger,
    });
  }

  const readiness = makeComputedReadiness0({
    semanticKImplFinalReady,
    finalKImplRecord,
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
        reason: 'semantic KBundle is not ready for final-theorem use',
        blockers: readiness.blockers,
        semanticKImplFinalProbe: compactRecord0(finalKImplRecord),
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && readiness.finalTheoremReady;
  const legacyBundleNF = legacyBundleRecord.NF
    ?? legacyBundleRecord.nf
    ?? {};

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'KBundleSemanticSuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: finalTheoremReady ? 'final-theorem-ready' : 'development-only',

      semanticKImplDevelopmentAccepted: true,
      semanticKImplDevelopmentChecker: developmentKImplRecord.checker,
      semanticKImplDevelopmentDigest: developmentKImplRecord.Digest
        ?? developmentKImplRecord.digest,
      semanticKImplDevelopmentOnly: true,
      semanticKImplPublicTheoremEmissionAllowed: false,
      semanticKImplSupportedRules: developmentKImplNF.supportedSemanticRules ?? [],
      semanticKImplMissingRules: developmentKImplNF.missingSemanticRules ?? [],

      semanticKImplFinalChecker: finalKImplRecord.checker,
      semanticKImplFinalProbeAccepted: finalKImplRecord.tag === 'accept',
      semanticKImplFinalProbeDigest: finalKImplRecord.Digest
        ?? finalKImplRecord.digest,
      semanticKImplFinalReady,

      legacyBundleAccepted: true,
      legacyBundleChecker: legacyBundleRecord.checker,
      legacyBundleDigest: legacyBundleRecord.Digest ?? legacyBundleRecord.digest,
      legacyKImplDigest: legacyBundleNF.kimplDigest ?? null,
      legacyConformanceDigest: legacyBundleNF.conformanceDigest ?? null,
      legacySigmaDigest: legacyBundleNF.sigmaDigest ?? null,
      legacyReflectionDigest: legacyBundleNF.reflectionDigest ?? null,

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
      checker: 'CheckKImplDAGIndFinalTheoremReadiness0',
      reason: semanticKImplFinalReady
        ? null
        : 'semantic primitive-rule coverage remains incomplete',
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
    kind: 'KBundleComputedSemanticReadiness0',
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
    return validationReject0([], 'semantic KBundle input must be an object', {
      actual: typeof input,
    });
  }

  if (input.kind !== 'KBundleSemanticSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic KBundle kind must be KBundleSemanticSuccessor0',
      { actual: input.kind },
    );
  }

  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic KBundle version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }

  if (!KBUNDLE_SEMANTIC_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic KBundle Purpose is unsupported',
      {
        actual: input.Purpose,
        supportedPurposes: [...KBUNDLE_SEMANTIC_SUCCESSOR_PURPOSES0],
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
        'semantic KBundle is missing a required field',
        { field },
      );
    }
  }

  if (!isPlainObject0(input.SemanticKImpl)) {
    return validationReject0(
      ['SemanticKImpl'],
      'semantic KBundle SemanticKImpl must be an object',
      { actual: typeof input.SemanticKImpl },
    );
  }

  if (input.SemanticKImpl.Purpose !== 'development') {
    return validationReject0(
      ['SemanticKImpl', 'Purpose'],
      'semantic KBundle input KImpl must remain development-purpose; final readiness is recomputed internally',
      { actual: input.SemanticKImpl.Purpose },
    );
  }

  if (!isPlainObject0(input.Binding)
      || !sameCanonical0(input.Binding, KBUNDLE_SEMANTIC_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'semantic KBundle checker binding must match the executable checker boundary',
      {
        expected: KBUNDLE_SEMANTIC_SUCCESSOR_BINDING0,
        actual: input.Binding,
      },
    );
  }

  if (!isPlainObject0(input.Policy)
      || !sameCanonical0(input.Policy, KBUNDLE_SEMANTIC_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic KBundle release policy must match the fail-closed policy',
      {
        expected: KBUNDLE_SEMANTIC_SUCCESSOR_POLICY0,
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
      'semantic KBundle rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  return validationAccept0({
    kind: 'KBundleSemanticSuccessorShape0NF',
    purpose: input.Purpose,
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
        'semantic KImpl did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }

  return validationAccept0({
    kind: 'KBundleSemanticKImplDevelopmentBoundary0NF',
    ...expected,
  });
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

function makeRejectRecord0({
  checker,
  coord,
  path,
  witness,
  ledger,
}) {
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

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckSigmaRegistry0,
  SIGMA_REQUIRED_THEOREMS0,
  makeSigmaRegistry0,
} from './pcc-kimpl0.mjs';

import {
  CheckSemanticK0Conformance0,
  makeSemanticK0ConformanceInput0,
} from './pcc-k0-semantic-conformance0.mjs';

const CHECKER_VERSION = 0;
const MAX_V53_ANCHORS = 12;
const MAX_V53_HYPEREDGES = 4_096;
const MAX_V54_ANCHORS = 16;
const MAX_V54_MINIMAL_CONSUMERS = 4_096;
const MAX_SIGMA_ENUMERATION_WORK = 8_388_608;
const MAX_SIGMA_INTEGER = 1_000_000_000;
const ID_PATTERN = /^[A-Za-z][A-Za-z0-9._-]{0,127}$/;

export const SEMANTIC_SIGMA_REQUIRED_THEOREMS0 = Object.freeze([
  ...SIGMA_REQUIRED_THEOREMS0,
]);

export const SEMANTIC_SIGMA_POLICY0 = Object.freeze({
  kind: 'SemanticSigmaDerivationPolicy0',
  version: CHECKER_VERSION,
  requiresSemanticK0Conformance: true,
  requiresLegacySigmaRegistryAcceptance: true,
  bindsEveryDerivationToRegistryEntryDigest: true,
  bindsEveryDerivationToExecutableCheckerContractDigest: true,
  explicitFiniteObjectsRequired: true,
  exactFiniteEnumerationRequired: true,
  nonnegativeIntegerHypergraphWeightsRequired: true,
  canonicalMinimalConsumerAntichainRequired: true,
  callerTheoremTruthAssertionsForbidden: true,
  boundedFiniteDerivationsOnly: true,
  unrestrictedUniversalSchemaNotClaimed: true,
  reflectionRemainsSeparateSurface: true,
});

export const SEMANTIC_SIGMA_V53_CHECKER_CONTRACT0 = Object.freeze({
  kind: 'SemanticSigmaV53CheckerContract0',
  version: CHECKER_VERSION,
  checker: 'CheckSemanticSigmaV53Derivation0',
  theorem: 'V53',
  theoremName: 'ConstantCutHypergraphRigidity',
  maxAnchors: MAX_V53_ANCHORS,
  sparsePositiveHyperedgesWithImplicitZero: true,
  nonnegativeIntegerWeightsRequired: true,
  positiveConstantProperCutValueRequired: true,
  exactProperCutEnumeration: true,
  pairTripleAndFullSpanConsequencesComputed: true,
  mixedThreeAnchorCaseComputed: true,
  callerTheoremTruthAssertionsForbidden: true,
});

export const SEMANTIC_SIGMA_V54_CHECKER_CONTRACT0 = Object.freeze({
  kind: 'SemanticSigmaV54CheckerContract0',
  version: CHECKER_VERSION,
  checker: 'CheckSemanticSigmaV54Derivation0',
  theorem: 'V54',
  theoremName: 'ConsumerAntichainNormalForm',
  maxAnchors: MAX_V54_ANCHORS,
  canonicalMinimalConsumerAntichainRequired: true,
  monotonePredicateDefinedByUpwardClosure: true,
  exactActivationEnumeration: true,
  disjointPairEquivalenceComputed: true,
  singletonCutIndicatorNormalFormComputed: true,
  callerTheoremTruthAssertionsForbidden: true,
});

export function makeSemanticSigmaV53Hyperedge0({
  index,
  anchors = [],
  weight,
} = {}) {
  requireIndex0(index, 'makeSemanticSigmaV53Hyperedge0 index');
  if (!Array.isArray(anchors)) {
    throw new TypeError('makeSemanticSigmaV53Hyperedge0 anchors must be an array');
  }
  for (const anchor of anchors) {
    requireIdentifier0(anchor, 'makeSemanticSigmaV53Hyperedge0 anchor');
  }
  requirePositiveInteger0(weight, 'makeSemanticSigmaV53Hyperedge0 weight');
  return Object.freeze({
    kind: 'SemanticSigmaV53Hyperedge0',
    version: CHECKER_VERSION,
    index,
    anchors: Object.freeze([...anchors]),
    weight,
  });
}

export function makeSemanticSigmaV53Spec0({
  derivationId,
  anchors = [],
  hyperedges = [],
  cutValue,
} = {}) {
  requireIdentifier0(derivationId, 'makeSemanticSigmaV53Spec0 derivationId');
  if (!Array.isArray(anchors)) {
    throw new TypeError('makeSemanticSigmaV53Spec0 anchors must be an array');
  }
  if (!Array.isArray(hyperedges)) {
    throw new TypeError('makeSemanticSigmaV53Spec0 hyperedges must be an array');
  }
  requirePositiveInteger0(cutValue, 'makeSemanticSigmaV53Spec0 cutValue');
  const spec = Object.freeze({
    kind: 'SemanticSigmaV53Spec0',
    version: CHECKER_VERSION,
    derivationId,
    anchors: Object.freeze([...anchors]),
    hyperedges: Object.freeze([...hyperedges]),
    cutValue,
  });
  const checked = validateV53Spec0(spec, ['spec']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return spec;
}

export function makeSemanticSigmaV54MinimalConsumer0({
  index,
  anchors = [],
} = {}) {
  requireIndex0(index, 'makeSemanticSigmaV54MinimalConsumer0 index');
  if (!Array.isArray(anchors)) {
    throw new TypeError(
      'makeSemanticSigmaV54MinimalConsumer0 anchors must be an array',
    );
  }
  for (const anchor of anchors) {
    requireIdentifier0(anchor, 'makeSemanticSigmaV54MinimalConsumer0 anchor');
  }
  return Object.freeze({
    kind: 'SemanticSigmaV54MinimalConsumer0',
    version: CHECKER_VERSION,
    index,
    anchors: Object.freeze([...anchors]),
  });
}

export function makeSemanticSigmaV54Spec0({
  derivationId,
  anchors = [],
  minimalConsumers = [],
} = {}) {
  requireIdentifier0(derivationId, 'makeSemanticSigmaV54Spec0 derivationId');
  if (!Array.isArray(anchors)) {
    throw new TypeError('makeSemanticSigmaV54Spec0 anchors must be an array');
  }
  if (!Array.isArray(minimalConsumers)) {
    throw new TypeError(
      'makeSemanticSigmaV54Spec0 minimalConsumers must be an array',
    );
  }
  const spec = Object.freeze({
    kind: 'SemanticSigmaV54Spec0',
    version: CHECKER_VERSION,
    derivationId,
    anchors: Object.freeze([...anchors]),
    minimalConsumers: Object.freeze([...minimalConsumers]),
  });
  const checked = validateV54Spec0(spec, ['spec']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  return spec;
}

export function deriveSemanticSigmaV53Conclusion0({ spec } = {}) {
  const checked = validateV53Spec0(spec, ['spec']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  const derived = deriveV53Conclusion0(checked, ['spec']);
  if (!derived.ok) throw new TypeError(derived.witness.reason);
  return derived.conclusion;
}

export function deriveSemanticSigmaV54Conclusion0({ spec } = {}) {
  const checked = validateV54Spec0(spec, ['spec']);
  if (!checked.ok) throw new TypeError(checked.witness.reason);
  const derived = deriveV54Conclusion0(checked, ['spec']);
  if (!derived.ok) throw new TypeError(derived.witness.reason);
  return derived.conclusion;
}

export function makeSemanticSigmaSuite0({
  PSigma = makeSigmaRegistry0(),
} = {}) {
  const registryEntries = getSigmaEntries0(PSigma);
  if (!Array.isArray(registryEntries)) {
    throw new TypeError('makeSemanticSigmaSuite0 PSigma must expose theorem entries');
  }
  const v53Registry = findRegistryEntry0(registryEntries, 'V53');
  const v54Registry = findRegistryEntry0(registryEntries, 'V54');
  if (v53Registry === null || v54Registry === null) {
    throw new TypeError(
      'makeSemanticSigmaSuite0 requires legacy V53 and V54 registry entries',
    );
  }

  const v53Spec = makeSemanticSigmaV53Spec0({
    derivationId: 'Sigma.V53.canonical.mixed-triple',
    anchors: ['a', 'b', 'c'],
    hyperedges: [
      makeSemanticSigmaV53Hyperedge0({
        index: 0,
        anchors: ['a', 'b'],
        weight: 1,
      }),
      makeSemanticSigmaV53Hyperedge0({
        index: 1,
        anchors: ['a', 'c'],
        weight: 1,
      }),
      makeSemanticSigmaV53Hyperedge0({
        index: 2,
        anchors: ['b', 'c'],
        weight: 1,
      }),
      makeSemanticSigmaV53Hyperedge0({
        index: 3,
        anchors: ['a', 'b', 'c'],
        weight: 1,
      }),
    ],
    cutValue: 3,
  });

  const v54Spec = makeSemanticSigmaV54Spec0({
    derivationId: 'Sigma.V54.canonical.singleton-cut',
    anchors: ['a', 'b', 'c'],
    minimalConsumers: [
      makeSemanticSigmaV54MinimalConsumer0({
        index: 0,
        anchors: ['a'],
      }),
      makeSemanticSigmaV54MinimalConsumer0({
        index: 1,
        anchors: ['b'],
      }),
    ],
  });

  const suite = Object.freeze({
    kind: 'SemanticSigmaSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Sigma.semantic.V53V54.bounded0',
    derivations: Object.freeze([
      makeDerivationEntry0({
        index: 0,
        theorem: 'V53',
        registryEntry: v53Registry,
        checkerContract: SEMANTIC_SIGMA_V53_CHECKER_CONTRACT0,
        spec: v53Spec,
        conclusion: deriveSemanticSigmaV53Conclusion0({ spec: v53Spec }),
      }),
      makeDerivationEntry0({
        index: 1,
        theorem: 'V54',
        registryEntry: v54Registry,
        checkerContract: SEMANTIC_SIGMA_V54_CHECKER_CONTRACT0,
        spec: v54Spec,
        conclusion: deriveSemanticSigmaV54Conclusion0({ spec: v54Spec }),
      }),
    ]),
    Policy: { ...SEMANTIC_SIGMA_POLICY0 },
  });
  return suite;
}

export function makeSemanticSigmaInput0({
  KImpl,
  K0,
  K0SemanticConformance,
  PSigma = makeSigmaRegistry0(),
  SemanticSigma = makeSemanticSigmaSuite0({ PSigma }),
} = {}) {
  return Object.freeze({
    kind: 'SemanticSigmaInput0',
    version: CHECKER_VERSION,
    KImpl,
    K0,
    K0SemanticConformance,
    PSigma,
    SemanticSigma,
    Policy: { ...SEMANTIC_SIGMA_POLICY0 },
  });
}

export function CheckSemanticSigmaV53Derivation0(input) {
  return checkDerivationEntry0(input, {
    checker: 'CheckSemanticSigmaV53Derivation0',
    theorem: 'V53',
    contract: SEMANTIC_SIGMA_V53_CHECKER_CONTRACT0,
    validateSpec: validateV53Spec0,
    derive: deriveV53Conclusion0,
  });
}

export function CheckSemanticSigmaV54Derivation0(input) {
  return checkDerivationEntry0(input, {
    checker: 'CheckSemanticSigmaV54Derivation0',
    theorem: 'V54',
    contract: SEMANTIC_SIGMA_V54_CHECKER_CONTRACT0,
    validateSpec: validateV54Spec0,
    derive: deriveV54Conclusion0,
  });
}

export async function CheckSemanticSigma0(input) {
  const checker = 'CheckSemanticSigma0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const conformanceCall = await callChecker0(
    'CheckSemanticK0Conformance0',
    () => CheckSemanticK0Conformance0(makeSemanticK0ConformanceInput0({
      KImpl: input.KImpl,
      K0: input.K0,
      SemanticConformance: input.K0SemanticConformance,
    })),
  );
  ledger.push(makeLedgerEntry0(
    'CheckSemanticK0Conformance0',
    conformanceCall.ok && isSemanticConformanceAccept0(conformanceCall.record),
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
  if (!isSemanticConformanceAccept0(conformanceCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticConformance`,
      path: ['K0SemanticConformance'],
      witness: {
        reason: 'semantic Sigma derivations require accepted semantic K0 conformance',
        inner: compactRecord0(conformanceCall.record),
      },
      ledger,
    });
  }

  const registryCall = await callChecker0(
    'CheckSigmaRegistry0',
    () => CheckSigmaRegistry0(input.PSigma),
  );
  ledger.push(makeLedgerEntry0(
    'CheckSigmaRegistry0',
    registryCall.ok && registryCall.record.tag === 'accept',
    registryCall.ok ? registryCall.record : registryCall.witness,
  ));
  if (!registryCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacySigma.exception`,
      path: ['PSigma'],
      witness: registryCall.witness,
      ledger,
    });
  }
  if (registryCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacySigma`,
      path: ['PSigma'],
      witness: {
        reason: 'legacy Sigma registry rejected before semantic derivation upgrade',
        inner: compactRecord0(registryCall.record),
      },
      ledger,
    });
  }

  const suite = validateSemanticSigmaSuiteShape0(input.SemanticSigma);
  ledger.push(makeLedgerEntry0(
    'semanticSigmaSuiteShape',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticSigmaSuite`,
      suite,
      ledger,
    );
  }

  const registryEntries = getSigmaEntries0(input.PSigma);
  const registryByTheorem = new Map(
    SEMANTIC_SIGMA_REQUIRED_THEOREMS0.map((theorem) => [
      theorem,
      findRegistryEntry0(registryEntries, theorem),
    ]),
  );

  const acceptedDerivations = [];
  for (let index = 0;
    index < SEMANTIC_SIGMA_REQUIRED_THEOREMS0.length;
    index += 1) {
    const theorem = SEMANTIC_SIGMA_REQUIRED_THEOREMS0[index];
    const entry = input.SemanticSigma.derivations[index];
    if (entry.index !== index || entry.theorem !== theorem) {
      return makeRejectRecord0({
        checker,
        coord: `${checker}.semanticSigmaSuite.order`,
        path: ['SemanticSigma', 'derivations', index],
        witness: {
          reason: 'semantic Sigma derivations must appear in exact required theorem order',
          expected: { index, theorem },
          actual: { index: entry.index, theorem: entry.theorem },
        },
        ledger,
      });
    }
    const registryEntry = registryByTheorem.get(theorem);
    if (registryEntry === null) {
      return makeRejectRecord0({
        checker,
        coord: `${checker}.semanticSigmaSuite.registry`,
        path: ['PSigma', 'theorems', theorem],
        witness: {
          reason: 'semantic Sigma derivation has no matching legacy registry entry',
          theorem,
        },
        ledger,
      });
    }
    const expectedRegistryId = getRegistryEntryId0(registryEntry);
    const expectedRegistryDigest = digestCanonical0(registryEntry);
    if (entry.registryEntryId !== expectedRegistryId
        || !sameCanonical0(entry.registryEntryDigest, expectedRegistryDigest)) {
      return makeRejectRecord0({
        checker,
        coord: `${checker}.semanticSigmaSuite.registryBinding`,
        path: ['SemanticSigma', 'derivations', index, 'registryEntryDigest'],
        witness: {
          reason: 'semantic Sigma derivation must bind the exact legacy registry entry digest',
          theorem,
          expectedRegistryId,
          expectedRegistryDigest,
          actualRegistryId: entry.registryEntryId,
          actualRegistryDigest: entry.registryEntryDigest,
        },
        ledger,
      });
    }

    const derivationCall = theorem === 'V53'
      ? CheckSemanticSigmaV53Derivation0(entry)
      : CheckSemanticSigmaV54Derivation0(entry);
    ledger.push(makeLedgerEntry0(
      `semanticSigma.${theorem}`,
      derivationCall.tag === 'accept',
      derivationCall,
    ));
    if (derivationCall.tag !== 'accept') {
      return makeRejectRecord0({
        checker,
        coord: `${checker}.semanticSigma.${theorem}`,
        path: ['SemanticSigma', 'derivations', index],
        witness: {
          reason: `semantic Sigma ${theorem} derivation rejected`,
          inner: compactRecord0(derivationCall),
        },
        ledger,
      });
    }
    acceptedDerivations.push(derivationCall);
  }

  const conformanceNF = conformanceCall.record.NF
    ?? conformanceCall.record.nf
    ?? {};
  const registryNF = registryCall.record.NF ?? registryCall.record.nf ?? {};
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticSigma0NF',
      checker,
      version: CHECKER_VERSION,
      semanticSigmaReady: true,
      semanticDerivationsReady: true,
      semanticKImplFinalReady: conformanceNF.semanticKImplFinalReady === true,
      semanticKImplFinalDigest: conformanceNF.semanticKImplFinalDigest ?? null,
      semanticK0ConformanceReady:
        conformanceNF.semanticK0ConformanceReady === true,
      semanticK0ConformanceDigest:
        conformanceCall.record.Digest ?? conformanceCall.record.digest,
      legacySigmaAccepted: true,
      legacySigmaChecker: registryCall.record.checker,
      legacySigmaDigest: registryCall.record.Digest ?? registryCall.record.digest,
      legacySigmaTheoremIds: registryNF.theoremIds ?? [],
      semanticSigmaSuiteId: input.SemanticSigma.suiteId,
      semanticSigmaDerivationCount: acceptedDerivations.length,
      semanticSigmaTheorems: [...SEMANTIC_SIGMA_REQUIRED_THEOREMS0],
      semanticSigmaDerivationDigests: acceptedDerivations.map((record) => ({
        theorem: record.NF.theorem,
        digest: record.Digest,
        conclusionDigest: record.NF.conclusionDigest,
        checkerContractDigest: record.NF.checkerContractDigest,
        registryEntryDigest: record.NF.registryEntryDigest,
      })),
      v53Ready: true,
      v54Ready: true,
      boundedFiniteDerivationsOnly: true,
      unrestrictedUniversalSchemaNotClaimed: true,
      callerTheoremTruthAssertionsForbidden: true,
      reflectionReady: false,
      reflectionRemainsSeparateSurface: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeDerivationEntry0({
  index,
  theorem,
  registryEntry,
  checkerContract,
  spec,
  conclusion,
}) {
  const checker = checkerContract.checker;
  const base = Object.freeze({
    kind: 'SemanticSigmaDerivation0',
    version: CHECKER_VERSION,
    index,
    theorem,
    registryEntryId: getRegistryEntryId0(registryEntry),
    registryEntryDigest: digestCanonical0(registryEntry),
    checker,
    checkerContractDigest: digestCanonical0(checkerContract),
    spec,
    conclusion,
  });
  return Object.freeze({
    ...base,
    derivationDigest: digestCanonical0(base),
  });
}

function checkDerivationEntry0(input, {
  checker,
  theorem,
  contract,
  validateSpec,
  derive,
}) {
  const ledger = [];
  const shape = validateDerivationEntryShape0(input, theorem, checker);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const expectedContractDigest = digestCanonical0(contract);
  const contractOk = sameCanonical0(
    input.checkerContractDigest,
    expectedContractDigest,
  );
  ledger.push(makeLedgerEntry0('checkerContract', contractOk, {
    expected: expectedContractDigest,
    actual: input.checkerContractDigest,
  }));
  if (!contractOk) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.checkerContract`,
      path: ['checkerContractDigest'],
      witness: {
        reason: 'semantic Sigma derivation checker contract digest is stale or mismatched',
        expected: expectedContractDigest,
        actual: input.checkerContractDigest,
      },
      ledger,
    });
  }

  const specCheck = validateSpec(input.spec, ['spec']);
  ledger.push(makeLedgerEntry0(
    'spec',
    specCheck.ok,
    specCheck.nf ?? specCheck.witness,
  ));
  if (!specCheck.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.spec`,
      specCheck,
      ledger,
    );
  }

  const derived = derive(specCheck, ['spec']);
  ledger.push(makeLedgerEntry0(
    'derive',
    derived.ok,
    derived.nf ?? derived.witness,
  ));
  if (!derived.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.derive`,
      derived,
      ledger,
    );
  }

  if (!sameCanonical0(input.conclusion, derived.conclusion)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.conclusion`,
      path: ['conclusion'],
      witness: {
        reason: 'semantic Sigma conclusion must exactly equal the independently computed finite derivation',
        expected: derived.conclusion,
        actual: input.conclusion,
      },
      ledger,
    });
  }

  const base = {
    kind: input.kind,
    version: input.version,
    index: input.index,
    theorem: input.theorem,
    registryEntryId: input.registryEntryId,
    registryEntryDigest: input.registryEntryDigest,
    checker: input.checker,
    checkerContractDigest: input.checkerContractDigest,
    spec: input.spec,
    conclusion: input.conclusion,
  };
  const expectedDerivationDigest = digestCanonical0(base);
  if (!sameCanonical0(input.derivationDigest, expectedDerivationDigest)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.derivationDigest`,
      path: ['derivationDigest'],
      witness: {
        reason: 'semantic Sigma derivation digest must bind the exact checked record',
        expected: expectedDerivationDigest,
        actual: input.derivationDigest,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticSigmaDerivation0NF',
      checker,
      version: CHECKER_VERSION,
      theorem,
      derivationId: input.spec.derivationId,
      registryEntryId: input.registryEntryId,
      registryEntryDigest: input.registryEntryDigest,
      checkerContractDigest: input.checkerContractDigest,
      derivationDigest: input.derivationDigest,
      conclusionDigest: digestCanonical0(derived.conclusion),
      boundedFiniteDerivation: true,
      callerTheoremTruthAssertionsForbidden: true,
    },
    ledger,
  });
}

function validateV53Spec0(spec, path) {
  if (!isPlainObject0(spec)) {
    return validationReject0(path, 'V53 specification must be an object', {
      actual: typeof spec,
    });
  }
  const allowed = new Set([
    'kind', 'version', 'derivationId', 'anchors', 'hyperedges', 'cutValue',
  ]);
  const unexpected = Object.keys(spec).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'V53 specification rejects caller-supplied theorem truth, classification, proof, solver, search, optimization, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (spec.kind !== 'SemanticSigmaV53Spec0') {
    return validationReject0(
      [...path, 'kind'],
      'V53 specification kind must be SemanticSigmaV53Spec0',
      { actual: spec.kind },
    );
  }
  if (spec.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `V53 specification version must be ${CHECKER_VERSION}`,
      { actual: spec.version },
    );
  }
  if (!isIdentifier0(spec.derivationId)) {
    return validationReject0(
      [...path, 'derivationId'],
      'V53 derivationId must be a canonical identifier',
      { actual: spec.derivationId },
    );
  }
  const anchorsCheck = validateAnchorUniverse0(
    spec.anchors,
    [...path, 'anchors'],
    2,
    MAX_V53_ANCHORS,
    'V53',
  );
  if (!anchorsCheck.ok) return anchorsCheck;
  if (!Array.isArray(spec.hyperedges)
      || spec.hyperedges.length > MAX_V53_HYPEREDGES) {
    return validationReject0(
      [...path, 'hyperedges'],
      'V53 hyperedges must be a bounded array',
      {
        maxHyperedges: MAX_V53_HYPEREDGES,
        actual: Array.isArray(spec.hyperedges)
          ? spec.hyperedges.length
          : typeof spec.hyperedges,
      },
    );
  }
  if (!isPositiveInteger0(spec.cutValue)) {
    return validationReject0(
      [...path, 'cutValue'],
      'V53 cutValue must be a positive bounded safe integer',
      { actual: spec.cutValue },
    );
  }

  const edgeByMask = new Map();
  const edges = [];
  let previousMask = -1;
  let totalWeight = 0;
  for (let index = 0; index < spec.hyperedges.length; index += 1) {
    const edge = spec.hyperedges[index];
    const edgePath = [...path, 'hyperedges', index];
    if (!isPlainObject0(edge)) {
      return validationReject0(edgePath, 'V53 hyperedge must be an object', {
        actual: typeof edge,
      });
    }
    const edgeAllowed = new Set(['kind', 'version', 'index', 'anchors', 'weight']);
    const edgeUnexpected = Object.keys(edge)
      .filter((key) => !edgeAllowed.has(key));
    if (edgeUnexpected.length !== 0) {
      return validationReject0(
        [...edgePath, edgeUnexpected[0]],
        'V53 hyperedge rejects undeclared theorem truth or derived classification fields',
        { unexpectedFields: edgeUnexpected.sort() },
      );
    }
    if (edge.kind !== 'SemanticSigmaV53Hyperedge0') {
      return validationReject0(
        [...edgePath, 'kind'],
        'V53 hyperedge kind must be SemanticSigmaV53Hyperedge0',
        { actual: edge.kind },
      );
    }
    if (edge.version !== CHECKER_VERSION) {
      return validationReject0(
        [...edgePath, 'version'],
        `V53 hyperedge version must be ${CHECKER_VERSION}`,
        { actual: edge.version },
      );
    }
    if (edge.index !== index) {
      return validationReject0(
        [...edgePath, 'index'],
        'V53 hyperedge indices must be exact consecutive coordinates',
        { expected: index, actual: edge.index },
      );
    }
    if (!Array.isArray(edge.anchors) || edge.anchors.length < 2) {
      return validationReject0(
        [...edgePath, 'anchors'],
        'V53 hyperedge must contain at least two anchors',
        { actual: edge.anchors },
      );
    }
    let mask = 0;
    let previousAnchorIndex = -1;
    for (let anchorIndex = 0; anchorIndex < edge.anchors.length; anchorIndex += 1) {
      const anchor = edge.anchors[anchorIndex];
      const universeIndex = anchorsCheck.anchorIndex.get(anchor);
      if (universeIndex === undefined) {
        return validationReject0(
          [...edgePath, 'anchors', anchorIndex],
          'V53 hyperedge anchor must belong to the declared anchor universe',
          { actual: anchor },
        );
      }
      if (universeIndex <= previousAnchorIndex) {
        return validationReject0(
          [...edgePath, 'anchors', anchorIndex],
          'V53 hyperedge anchors must be unique and in canonical universe order',
          { actual: edge.anchors },
        );
      }
      previousAnchorIndex = universeIndex;
      mask |= 2 ** universeIndex;
    }
    if (mask <= previousMask) {
      return validationReject0(
        [...edgePath, 'anchors'],
        'V53 hyperedges must be unique and in canonical subset order',
        { previousMask, actualMask: mask },
      );
    }
    if (!isPositiveInteger0(edge.weight)) {
      return validationReject0(
        [...edgePath, 'weight'],
        'V53 sparse hyperedge weight must be a positive bounded safe integer',
        { actual: edge.weight },
      );
    }
    totalWeight += edge.weight;
    if (!Number.isSafeInteger(totalWeight)
        || totalWeight > MAX_SIGMA_INTEGER) {
      return validationReject0(
        [...edgePath, 'weight'],
        'V53 total hypergraph weight exceeds the bounded integer limit',
        { max: MAX_SIGMA_INTEGER, actual: totalWeight },
      );
    }
    previousMask = mask;
    edgeByMask.set(mask, edge.weight);
    edges.push({ mask, weight: edge.weight, anchors: [...edge.anchors] });
  }

  const cutCount = (2 ** spec.anchors.length) - 2;
  const work = cutCount * Math.max(1, edges.length);
  if (work > MAX_SIGMA_ENUMERATION_WORK) {
    return validationReject0(
      path,
      'V53 exact cut enumeration exceeds the bounded work limit',
      { maxWork: MAX_SIGMA_ENUMERATION_WORK, actualWork: work },
    );
  }

  return validationAcceptWith0({
    kind: 'SemanticSigmaV53Spec0NF',
    derivationId: spec.derivationId,
    anchorCount: spec.anchors.length,
    hyperedgeCount: edges.length,
    cutCount,
    cutValue: spec.cutValue,
    totalWeight,
    exactCutEnumeration: true,
  }, {
    spec,
    anchors: [...spec.anchors],
    anchorIndex: anchorsCheck.anchorIndex,
    edges,
    edgeByMask,
  });
}

function deriveV53Conclusion0(specCheck, path) {
  const q = specCheck.anchors.length;
  const fullMask = (2 ** q) - 1;
  for (let cutMask = 1; cutMask < fullMask; cutMask += 1) {
    let total = 0;
    for (const edge of specCheck.edges) {
      const left = edge.mask & cutMask;
      const right = edge.mask & (fullMask ^ cutMask);
      if (left !== 0 && right !== 0) total += edge.weight;
    }
    if (total !== specCheck.spec.cutValue) {
      return validationReject0(
        [...path, 'cutValue'],
        'V53 constant-cut premise does not hold on every nonempty proper cut',
        {
          cutAnchors: anchorsFromMask0(cutMask, specCheck.anchors),
          expected: specCheck.spec.cutValue,
          actual: total,
        },
      );
    }
  }

  const D = specCheck.spec.cutValue;
  const fullWeight = specCheck.edgeByMask.get(fullMask) ?? 0;
  let classification;
  let pairWeight = 0;
  let allPairWeightsEqual = true;
  let everyProperHyperedgeWeightZero = false;
  let mixedTripleCase = false;

  if (q === 2) {
    classification = 'pair';
    pairWeight = fullWeight;
    if (fullWeight !== D) {
      return validationReject0(
        path,
        'V53 two-anchor rigidity consequence failed after exact premise checking',
        { expectedFullWeight: D, actualFullWeight: fullWeight },
      );
    }
  } else if (q === 3) {
    classification = 'triple';
    const pairMasks = [3, 5, 6];
    const pairWeights = pairMasks.map(
      (mask) => specCheck.edgeByMask.get(mask) ?? 0,
    );
    allPairWeightsEqual = pairWeights.every(
      (weight) => weight === pairWeights[0],
    );
    pairWeight = pairWeights[0];
    if (!allPairWeightsEqual || fullWeight !== D - (2 * pairWeight)) {
      return validationReject0(
        path,
        'V53 three-anchor rigidity consequence failed after exact premise checking',
        {
          pairWeights,
          cutValue: D,
          expectedFullWeight: D - (2 * pairWeight),
          actualFullWeight: fullWeight,
        },
      );
    }
    mixedTripleCase = pairWeight > 0 && fullWeight > 0;
  } else {
    classification = 'full-span';
    const nonzeroProper = specCheck.edges.filter(
      (edge) => edge.mask !== fullMask,
    );
    everyProperHyperedgeWeightZero = nonzeroProper.length === 0;
    if (!everyProperHyperedgeWeightZero || fullWeight !== D) {
      return validationReject0(
        path,
        'V53 four-or-more-anchor rigidity consequence failed after exact premise checking',
        {
          nonzeroProperHyperedges: nonzeroProper,
          expectedFullWeight: D,
          actualFullWeight: fullWeight,
        },
      );
    }
  }

  const conclusion = Object.freeze({
    kind: 'SemanticSigmaV53Conclusion0',
    version: CHECKER_VERSION,
    theorem: 'V53',
    derivationId: specCheck.spec.derivationId,
    anchorCount: q,
    cutValue: D,
    classification,
    pairWeight,
    fullSpanWeight: fullWeight,
    allPairWeightsEqual,
    everyProperHyperedgeWeightZero:
      q >= 4 ? everyProperHyperedgeWeightZero : null,
    mixedTripleCase,
    constantProperCutValueVerified: true,
    nonnegativeIntegerWeightsVerified: true,
    pairTripleAndFullSpanExhaustiveForCheckedInstance: true,
    theoremConsequenceVerified: true,
    boundedFiniteDerivation: true,
    hypergraphDigest: digestCanonical0(specCheck.spec),
  });
  return validationAcceptWith0({
    kind: 'SemanticSigmaV53Derivation0NF',
    derivationId: specCheck.spec.derivationId,
    anchorCount: q,
    classification,
    cutValue: D,
  }, { conclusion });
}

function validateV54Spec0(spec, path) {
  if (!isPlainObject0(spec)) {
    return validationReject0(path, 'V54 specification must be an object', {
      actual: typeof spec,
    });
  }
  const allowed = new Set([
    'kind', 'version', 'derivationId', 'anchors', 'minimalConsumers',
  ]);
  const unexpected = Object.keys(spec).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [...path, unexpected[0]],
      'V54 specification rejects caller-supplied theorem truth, activation, normal-form, proof, solver, search, optimization, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (spec.kind !== 'SemanticSigmaV54Spec0') {
    return validationReject0(
      [...path, 'kind'],
      'V54 specification kind must be SemanticSigmaV54Spec0',
      { actual: spec.kind },
    );
  }
  if (spec.version !== CHECKER_VERSION) {
    return validationReject0(
      [...path, 'version'],
      `V54 specification version must be ${CHECKER_VERSION}`,
      { actual: spec.version },
    );
  }
  if (!isIdentifier0(spec.derivationId)) {
    return validationReject0(
      [...path, 'derivationId'],
      'V54 derivationId must be a canonical identifier',
      { actual: spec.derivationId },
    );
  }
  const anchorsCheck = validateAnchorUniverse0(
    spec.anchors,
    [...path, 'anchors'],
    1,
    MAX_V54_ANCHORS,
    'V54',
  );
  if (!anchorsCheck.ok) return anchorsCheck;
  if (!Array.isArray(spec.minimalConsumers)
      || spec.minimalConsumers.length > MAX_V54_MINIMAL_CONSUMERS) {
    return validationReject0(
      [...path, 'minimalConsumers'],
      'V54 minimalConsumers must be a bounded array',
      {
        maxMinimalConsumers: MAX_V54_MINIMAL_CONSUMERS,
        actual: Array.isArray(spec.minimalConsumers)
          ? spec.minimalConsumers.length
          : typeof spec.minimalConsumers,
      },
    );
  }

  const masks = [];
  let previousMask = -1;
  for (let index = 0; index < spec.minimalConsumers.length; index += 1) {
    const consumer = spec.minimalConsumers[index];
    const consumerPath = [...path, 'minimalConsumers', index];
    if (!isPlainObject0(consumer)) {
      return validationReject0(
        consumerPath,
        'V54 minimal consumer must be an object',
        { actual: typeof consumer },
      );
    }
    const consumerAllowed = new Set(['kind', 'version', 'index', 'anchors']);
    const consumerUnexpected = Object.keys(consumer)
      .filter((key) => !consumerAllowed.has(key));
    if (consumerUnexpected.length !== 0) {
      return validationReject0(
        [...consumerPath, consumerUnexpected[0]],
        'V54 minimal consumer rejects undeclared theorem truth or activation fields',
        { unexpectedFields: consumerUnexpected.sort() },
      );
    }
    if (consumer.kind !== 'SemanticSigmaV54MinimalConsumer0') {
      return validationReject0(
        [...consumerPath, 'kind'],
        'V54 minimal consumer kind must be SemanticSigmaV54MinimalConsumer0',
        { actual: consumer.kind },
      );
    }
    if (consumer.version !== CHECKER_VERSION) {
      return validationReject0(
        [...consumerPath, 'version'],
        `V54 minimal consumer version must be ${CHECKER_VERSION}`,
        { actual: consumer.version },
      );
    }
    if (consumer.index !== index) {
      return validationReject0(
        [...consumerPath, 'index'],
        'V54 minimal consumer indices must be exact consecutive coordinates',
        { expected: index, actual: consumer.index },
      );
    }
    if (!Array.isArray(consumer.anchors) || consumer.anchors.length === 0) {
      return validationReject0(
        [...consumerPath, 'anchors'],
        'V54 minimal consumer must be a nonempty anchor subset',
        { actual: consumer.anchors },
      );
    }
    let mask = 0;
    let previousAnchorIndex = -1;
    for (let anchorIndex = 0;
      anchorIndex < consumer.anchors.length;
      anchorIndex += 1) {
      const anchor = consumer.anchors[anchorIndex];
      const universeIndex = anchorsCheck.anchorIndex.get(anchor);
      if (universeIndex === undefined) {
        return validationReject0(
          [...consumerPath, 'anchors', anchorIndex],
          'V54 minimal consumer anchor must belong to the declared anchor universe',
          { actual: anchor },
        );
      }
      if (universeIndex <= previousAnchorIndex) {
        return validationReject0(
          [...consumerPath, 'anchors', anchorIndex],
          'V54 minimal consumer anchors must be unique and in canonical universe order',
          { actual: consumer.anchors },
        );
      }
      previousAnchorIndex = universeIndex;
      mask |= 2 ** universeIndex;
    }
    if (mask <= previousMask) {
      return validationReject0(
        [...consumerPath, 'anchors'],
        'V54 minimal consumers must be unique and in canonical subset order',
        { previousMask, actualMask: mask },
      );
    }
    previousMask = mask;
    masks.push(mask);
  }

  for (let left = 0; left < masks.length; left += 1) {
    for (let right = left + 1; right < masks.length; right += 1) {
      if ((masks[left] & masks[right]) === masks[left]
          || (masks[left] & masks[right]) === masks[right]) {
        return validationReject0(
          [...path, 'minimalConsumers', right],
          'V54 minimalConsumers must form an inclusion antichain',
          {
            left: anchorsFromMask0(masks[left], spec.anchors),
            right: anchorsFromMask0(masks[right], spec.anchors),
          },
        );
      }
    }
  }

  const subsetCount = 2 ** spec.anchors.length;
  const work = subsetCount * Math.max(1, masks.length);
  if (work > MAX_SIGMA_ENUMERATION_WORK) {
    return validationReject0(
      path,
      'V54 exact activation enumeration exceeds the bounded work limit',
      { maxWork: MAX_SIGMA_ENUMERATION_WORK, actualWork: work },
    );
  }

  return validationAcceptWith0({
    kind: 'SemanticSigmaV54Spec0NF',
    derivationId: spec.derivationId,
    anchorCount: spec.anchors.length,
    minimalConsumerCount: masks.length,
    subsetCount,
    exactActivationEnumeration: true,
  }, {
    spec,
    anchors: [...spec.anchors],
    masks,
  });
}

function deriveV54Conclusion0(specCheck, path) {
  const q = specCheck.anchors.length;
  const fullMask = (2 ** q) - 1;
  const disjointPairs = [];
  for (let left = 0; left < specCheck.masks.length; left += 1) {
    for (let right = left + 1; right < specCheck.masks.length; right += 1) {
      if ((specCheck.masks[left] & specCheck.masks[right]) === 0) {
        disjointPairs.push([specCheck.masks[left], specCheck.masks[right]]);
      }
    }
  }
  const hasDisjointPair = disjointPairs.length > 0;
  const allDisjointPairsSingletons = disjointPairs.every(
    ([left, right]) => popcount0(left) === 1 && popcount0(right) === 1,
  );
  let singletonFootprintMask = 0;
  for (const mask of specCheck.masks) {
    if (popcount0(mask) === 1) singletonFootprintMask |= mask;
  }

  let activationNonzero = false;
  let cutIndicatorMatches = true;
  for (let subset = 0; subset <= fullMask; subset += 1) {
    const complement = fullMask ^ subset;
    const left = predicateFromAntichain0(subset, specCheck.masks);
    const right = predicateFromAntichain0(complement, specCheck.masks);
    const activation = left && right;
    if (activation) activationNonzero = true;
    if (allDisjointPairsSingletons) {
      const cutIndicator = (singletonFootprintMask & subset) !== 0
        && (singletonFootprintMask & complement) !== 0;
      if (activation !== cutIndicator) {
        cutIndicatorMatches = false;
        return validationReject0(
          path,
          'V54 singleton consumer cut-indicator consequence failed after exact activation enumeration',
          {
            subset: anchorsFromMask0(subset, specCheck.anchors),
            activation,
            cutIndicator,
            singletonFootprint: anchorsFromMask0(
              singletonFootprintMask,
              specCheck.anchors,
            ),
          },
        );
      }
    }
  }

  if (activationNonzero !== hasDisjointPair) {
    return validationReject0(
      path,
      'V54 activation/disjoint-pair equivalence failed after exact enumeration',
      { activationNonzero, hasDisjointPair },
    );
  }

  const conclusion = Object.freeze({
    kind: 'SemanticSigmaV54Conclusion0',
    version: CHECKER_VERSION,
    theorem: 'V54',
    derivationId: specCheck.spec.derivationId,
    anchorCount: q,
    minimalConsumerCount: specCheck.masks.length,
    activationNonzero,
    hasDisjointPair,
    activationIffDisjointPair: true,
    disjointPairCount: disjointPairs.length,
    allDisjointPairsSingletons,
    singletonNormalFormApplicable: allDisjointPairsSingletons,
    singletonFootprint: Object.freeze(
      anchorsFromMask0(singletonFootprintMask, specCheck.anchors),
    ),
    cutIndicatorMatches: allDisjointPairsSingletons
      ? cutIndicatorMatches
      : null,
    monotonePredicateDefinedByUpwardClosure: true,
    exactActivationEnumeration: true,
    theoremConsequenceVerified: true,
    boundedFiniteDerivation: true,
    antichainDigest: digestCanonical0(specCheck.spec),
  });
  return validationAcceptWith0({
    kind: 'SemanticSigmaV54Derivation0NF',
    derivationId: specCheck.spec.derivationId,
    anchorCount: q,
    minimalConsumerCount: specCheck.masks.length,
    activationNonzero,
    singletonNormalFormApplicable: allDisjointPairsSingletons,
  }, { conclusion });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'semantic Sigma input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'SemanticSigmaInput0') {
    return validationReject0(
      ['kind'],
      'semantic Sigma input kind must be SemanticSigmaInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic Sigma input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of [
    'KImpl',
    'K0',
    'K0SemanticConformance',
    'PSigma',
    'SemanticSigma',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic Sigma input is missing a required field',
        { field },
      );
    }
  }
  for (const field of [
    'KImpl', 'K0', 'K0SemanticConformance', 'PSigma', 'SemanticSigma', 'Policy',
  ]) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        `semantic Sigma input ${field} must be an object`,
        { actual: typeof input[field] },
      );
    }
  }
  if (!sameCanonical0(input.Policy, SEMANTIC_SIGMA_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic Sigma policy must match the fail-closed policy',
      { expected: SEMANTIC_SIGMA_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'KImpl',
    'K0',
    'K0SemanticConformance',
    'PSigma',
    'SemanticSigma',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic Sigma input rejects caller-supplied readiness or theorem truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'SemanticSigmaInputShape0NF' });
}

function validateSemanticSigmaSuiteShape0(suite) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SemanticSigma'],
      'semantic Sigma suite must be an object',
      { actual: typeof suite },
    );
  }
  const allowed = new Set([
    'kind', 'version', 'suiteId', 'derivations', 'Policy',
  ]);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['SemanticSigma', unexpected[0]],
      'semantic Sigma suite rejects caller-supplied readiness or theorem truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (suite.kind !== 'SemanticSigmaSuite0') {
    return validationReject0(
      ['SemanticSigma', 'kind'],
      'semantic Sigma suite kind must be SemanticSigmaSuite0',
      { actual: suite.kind },
    );
  }
  if (suite.version !== CHECKER_VERSION) {
    return validationReject0(
      ['SemanticSigma', 'version'],
      `semantic Sigma suite version must be ${CHECKER_VERSION}`,
      { actual: suite.version },
    );
  }
  if (!isIdentifier0(suite.suiteId)) {
    return validationReject0(
      ['SemanticSigma', 'suiteId'],
      'semantic Sigma suiteId must be a canonical identifier',
      { actual: suite.suiteId },
    );
  }
  if (!Array.isArray(suite.derivations)
      || suite.derivations.length !== SEMANTIC_SIGMA_REQUIRED_THEOREMS0.length) {
    return validationReject0(
      ['SemanticSigma', 'derivations'],
      'semantic Sigma suite must provide exactly one derivation per required theorem',
      {
        expected: SEMANTIC_SIGMA_REQUIRED_THEOREMS0.length,
        actual: suite.derivations?.length,
      },
    );
  }
  if (!isPlainObject0(suite.Policy)
      || !sameCanonical0(suite.Policy, SEMANTIC_SIGMA_POLICY0)) {
    return validationReject0(
      ['SemanticSigma', 'Policy'],
      'semantic Sigma suite policy must match the fail-closed policy',
      { expected: SEMANTIC_SIGMA_POLICY0, actual: suite.Policy },
    );
  }
  return validationAccept0({
    kind: 'SemanticSigmaSuiteShape0NF',
    suiteId: suite.suiteId,
    derivationCount: suite.derivations.length,
  });
}

function validateDerivationEntryShape0(input, theorem, checker) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'semantic Sigma derivation must be an object', {
      actual: typeof input,
    });
  }
  const allowed = new Set([
    'kind',
    'version',
    'index',
    'theorem',
    'registryEntryId',
    'registryEntryDigest',
    'checker',
    'checkerContractDigest',
    'spec',
    'conclusion',
    'derivationDigest',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic Sigma derivation rejects caller-supplied theorem truth, soundness, completeness, solver, search, optimization, or oracle assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (input.kind !== 'SemanticSigmaDerivation0') {
    return validationReject0(
      ['kind'],
      'semantic Sigma derivation kind must be SemanticSigmaDerivation0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic Sigma derivation version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!Number.isSafeInteger(input.index) || input.index < 0) {
    return validationReject0(
      ['index'],
      'semantic Sigma derivation index must be a nonnegative safe integer',
      { actual: input.index },
    );
  }
  if (input.theorem !== theorem) {
    return validationReject0(
      ['theorem'],
      `semantic Sigma derivation theorem must be ${theorem}`,
      { actual: input.theorem },
    );
  }
  if (!isIdentifier0(input.registryEntryId)) {
    return validationReject0(
      ['registryEntryId'],
      'semantic Sigma derivation registryEntryId must be a canonical identifier',
      { actual: input.registryEntryId },
    );
  }
  if (input.checker !== checker) {
    return validationReject0(
      ['checker'],
      `semantic Sigma derivation checker must be ${checker}`,
      { actual: input.checker },
    );
  }
  for (const field of [
    'registryEntryDigest', 'checkerContractDigest', 'derivationDigest',
  ]) {
    if (!isDigest0(input[field])) {
      return validationReject0(
        [field],
        'semantic Sigma derivation digest must be canonical',
        { actual: input[field] },
      );
    }
  }
  if (!isPlainObject0(input.spec)) {
    return validationReject0(
      ['spec'],
      'semantic Sigma derivation spec must be an object',
      { actual: typeof input.spec },
    );
  }
  if (!isPlainObject0(input.conclusion)) {
    return validationReject0(
      ['conclusion'],
      'semantic Sigma derivation conclusion must be an object',
      { actual: typeof input.conclusion },
    );
  }
  return validationAccept0({
    kind: 'SemanticSigmaDerivationShape0NF',
    theorem,
    checker,
  });
}

function validateAnchorUniverse0(anchors, path, min, max, theorem) {
  if (!Array.isArray(anchors)
      || anchors.length < min
      || anchors.length > max) {
    return validationReject0(
      path,
      `${theorem} anchors must be a bounded array with valid cardinality`,
      { minAnchors: min, maxAnchors: max, actual: anchors?.length },
    );
  }
  const anchorIndex = new Map();
  for (let index = 0; index < anchors.length; index += 1) {
    const anchor = anchors[index];
    if (!isIdentifier0(anchor)) {
      return validationReject0(
        [...path, index],
        `${theorem} anchor must be a canonical identifier`,
        { actual: anchor },
      );
    }
    if (anchorIndex.has(anchor)) {
      return validationReject0(
        [...path, index],
        `${theorem} anchors must be unique`,
        { anchor },
      );
    }
    if (index > 0 && compareText0(anchors[index - 1], anchor) >= 0) {
      return validationReject0(
        [...path, index],
        `${theorem} anchors must be in canonical lexical order`,
        { previous: anchors[index - 1], actual: anchor },
      );
    }
    anchorIndex.set(anchor, index);
  }
  return validationAcceptWith0({
    kind: 'SemanticSigmaAnchorUniverse0NF',
    theorem,
    anchorCount: anchors.length,
    anchors: [...anchors],
  }, { anchorIndex });
}

function predicateFromAntichain0(subsetMask, minimalMasks) {
  return minimalMasks.some((mask) => (mask & subsetMask) === mask);
}

function popcount0(mask) {
  let value = mask;
  let count = 0;
  while (value !== 0) {
    count += value & 1;
    value = Math.floor(value / 2);
  }
  return count;
}

function anchorsFromMask0(mask, anchors) {
  const out = [];
  for (let index = 0; index < anchors.length; index += 1) {
    if ((mask & (2 ** index)) !== 0) out.push(anchors[index]);
  }
  return out;
}

function getSigmaEntries0(registry) {
  return registry?.theorems
    ?? registry?.Theorems
    ?? registry?.entries
    ?? registry?.Entries;
}

function findRegistryEntry0(entries, theorem) {
  if (!Array.isArray(entries)) return null;
  const matches = entries.filter((entry) => {
    const values = [entry?.id, entry?.theorem, entry?.name]
      .filter((value) => typeof value === 'string');
    return values.some((value) => (
      value === theorem
      || value === `Sigma.${theorem}`
      || value.startsWith(`${theorem}.`)
      || value.includes(`.${theorem}.`)
      || value.includes(`Sigma.${theorem}`)
    ));
  });
  return matches.length === 1 ? matches[0] : null;
}

function getRegistryEntryId0(entry) {
  return String(entry?.id ?? entry?.theorem ?? entry?.name ?? '');
}

function isSemanticConformanceAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.semanticK0ConformanceReady === true
    && nf?.semanticConformanceReady === true
    && nf?.semanticKImplFinalReady === true;
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

function compareText0(left, right) {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
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

function isIdentifier0(value) {
  return typeof value === 'string' && ID_PATTERN.test(value);
}

function requireIdentifier0(value, label) {
  if (!isIdentifier0(value)) {
    throw new TypeError(`${label} must be a canonical identifier`);
  }
}

function requireIndex0(value, label) {
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new TypeError(`${label} must be a nonnegative safe integer`);
  }
}

function isPositiveInteger0(value) {
  return Number.isSafeInteger(value)
    && value > 0
    && value <= MAX_SIGMA_INTEGER;
}

function requirePositiveInteger0(value, label) {
  if (!isPositiveInteger0(value)) {
    throw new TypeError(`${label} must be a positive bounded safe integer`);
  }
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

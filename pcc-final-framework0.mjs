import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckGPack0,
  computeLockedNANDBaseline0,
  makeSyntheticGPack0,
} from './pcc-gpack0.mjs';

import {
  CheckGlobalProofDAG0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

const CHECKER_VERSION = 0;

export const FINAL_FRAMEWORK_REQUIRED_FIELDS0 = Object.freeze([
  'PO',
  'PG',
  'SyntaxMap',
  'ChargeMap',
  'CarrierMap',
  'OutputMap',
  'MinMap',
  'NormBridge',
  'SlackMap',
]);

export const SAT_DECISION_REQUIRED_FIELDS0 = Object.freeze([
  'InputKind',
  'NandConversion',
  'LockedWord',
  'Baseline',
  'DecisionRule',
  'Cases',
]);

export const SAT_BOUNDS_REQUIRED_FIELDS0 = Object.freeze([
  'Converter',
  'LockedBuilder',
  'Minimizer',
  'DecisionProcedure',
  'Bounds',
]);

export const FINAL_INTEGRATION_PHASES0 = Object.freeze([
  'CheckGPack0',
  'CheckGlobalProofDAG0',
  'CheckFinalFrameworkMatch0',
  'CheckSATDecision0',
  'CheckSATBounds0',
]);

export const FINAL_FRAMEWORK_FORBIDDEN_IMPORT_EDGES0 = Object.freeze([
  Object.freeze(['O', 'G']),
  Object.freeze(['G', 'O']),
]);

export const FINAL_FRAMEWORK_FORBIDDEN_EXEC_SYMBOLS0 = Object.freeze([
  'µ',
  'µ*',
  'µ#',
  'Can',
  'argmin',
  'maxG',
  'minimumEquivalent',
  'optimalCircuit',
  'exactMinSearch',
  'canonicalMinimizer',
  'maximizeGain',
]);

export const FINAL_CANONICAL_NAND_SYNTAX0 = Object.freeze({
  wordKind: 'direct-wire-nand',
  gate: 'NAND',
  arity: 2,
  sourceOrder: 'ordered',
  outputTuple: 'ordered',
  constants: 'locked-macro-only',
});

const EXECUTABLE_KEYS0 = new Set([
  'exec',
  'execs',
  'execCall',
  'execCalls',
  'call',
  'calls',
  'callee',
  'operator',
  'operation',
  'program',
  'body',
  'macroBody',
  'templateBody',
  'generatedBody',
]);

export function makeSyntheticPackageO0(overrides = {}) {
  return {
    kind: 'PackageO0',
    version: CHECKER_VERSION,
    packageId: 'PO',
    theorem: 'O.ZeroSlackOracle',
    imports: [
      'HB',
    ],
    doesNotImport: [
      'G',
    ],
    syntax: {
      ...FINAL_CANONICAL_NAND_SYNTAX0,
    },
    outputConvention: {
      kind: 'single-locked-output',
      outputName: 'Fphi',
      ordered: true,
    },
    chargeConvention: {
      kind: 'weighted-nand-charge',
      ordinaryNandWeight: 1,
      materializersCharged: true,
      uniqueOwners: true,
    },
    carrierConvention: {
      kind: 'locked-carrier',
      constants: 'macro-enforced',
      slotFamilies: [
        'X',
        'T',
        'O',
        'R',
        'L',
        'z',
      ],
    },
    minimumNotion: {
      kind: 'direct-wire-open-minimum',
      sameFrontier: true,
      exact: true,
    },
    residualSlack: {
      definition: 'Lambda(C)=|C|-mu(C)',
      sameAsG: true,
    },
    ...overrides,
  };
}

export function makeSyntheticPackageG0(gpack = makeSyntheticGPack0(), overrides = {}) {
  const baseline = baselineFromGPack0(gpack);

  return {
    kind: 'PackageG0',
    version: CHECKER_VERSION,
    packageId: 'PG',
    theorem: 'G.LockedNANDThreshold',
    imports: [
      'Packet',
    ],
    doesNotImport: [
      'O',
    ],
    syntax: {
      ...FINAL_CANONICAL_NAND_SYNTAX0,
    },
    outputConvention: {
      kind: 'single-locked-output',
      outputName: 'Fphi',
      finalLock: 'z',
      ordered: true,
    },
    chargeConvention: {
      kind: 'weighted-nand-charge',
      ordinaryNandWeight: 1,
      materializersCharged: true,
      uniqueOwners: true,
    },
    carrierConvention: {
      kind: 'locked-carrier',
      constants: 'macro-enforced',
      slotFamilies: [
        'X',
        'T',
        'O',
        'R',
        'L',
        'z',
      ],
    },
    minimumNotion: {
      kind: 'direct-wire-open-minimum',
      sameFrontier: true,
      exact: true,
    },
    residualSlack: {
      definition: 'Lambda(C)=|C|-mu(C)',
      residualSlackMax: 4,
    },
    lockedThreshold: {
      baseline,
      fullWordSize: baseline + 4,
      satIffMinAboveBaseline: true,
      unsatMinEqualsBaseline: true,
    },
    gpackDigest: digestCanonical0(gpack),
    ...overrides,
  };
}

export function makeSyntheticFinalFrameworkMatch0({
  gpack = makeSyntheticGPack0(),
  overrides = {},
} = {}) {
  const baseline = baselineFromGPack0(gpack);

  const match = {
    kind: 'FinalFrameworkMatch0',
    version: CHECKER_VERSION,

    PO: makeSyntheticPackageO0(),
    PG: makeSyntheticPackageG0(gpack),

    SyntaxMap: {
      kind: 'SyntaxMap0',
      sameNANDSyntax: true,
      canonical: {
        ...FINAL_CANONICAL_NAND_SYNTAX0,
      },
      poSyntaxDigest: digestCanonical0(makeSyntheticPackageO0().syntax),
      pgSyntaxDigest: digestCanonical0(makeSyntheticPackageG0(gpack).syntax),
    },

    ChargeMap: {
      kind: 'ChargeMap0',
      sameChargeConvention: true,
      ordinaryNandWeight: 1,
      materializersCharged: true,
      uniqueOwners: true,
      baseline,
      fullWordSize: baseline + 4,
    },

    CarrierMap: {
      kind: 'CarrierMap0',
      sameCarrierConvention: true,
      slotFamilies: [
        'X',
        'T',
        'O',
        'R',
        'L',
        'z',
      ],
      carrierConstants: 'macro-enforced',
      lockedCarrierCompatible: true,
    },

    OutputMap: {
      kind: 'OutputMap0',
      sameOutputConvention: true,
      outputName: 'Fphi',
      finalLock: 'z',
      oneOutput: true,
      satDecisionUsesOutput: true,
    },

    MinMap: {
      kind: 'MinMap0',
      sameMinimumNotion: true,
      exactMinimum: true,
      sameFrontierMinimum: true,
      minimizer: 'PCCMin',
      decisionComparator: 'minSize>baseline',
    },

    NormBridge: {
      kind: 'NormBridge0',
      normalizationPreservesSemantics: true,
      normalizationPreservesMinimum: true,
      normalizationPreservesResidualSlack: true,
      transportProofs: true,
    },

    SlackMap: {
      kind: 'SlackMap0',
      sameResidualSlackDefinition: true,
      definition: 'Lambda(C)=|C|-mu(C)',
      lockedResidualSlackMax: 4,
      gpackResidualSlackMax: 4,
      baseline,
      fullWordSize: baseline + 4,
    },

    ImportMap: {
      kind: 'FinalImportMap0',
      forbiddenEdges: FINAL_FRAMEWORK_FORBIDDEN_IMPORT_EDGES0,
      edges: [
        {
          from: 'O',
          to: 'HB',
        },
        {
          from: 'G',
          to: 'Packet',
        },
      ],
    },

    PiMatch: {
      kind: 'PiMatch0',
      version: CHECKER_VERSION,
      note: 'synthetic final framework match proof marker',
    },
  };

  return {
    ...match,
    ...overrides,
  };
}

export function makeSyntheticSATDecision0({
  gpack = makeSyntheticGPack0(),
  overrides = {},
} = {}) {
  const baseline = baselineFromGPack0(gpack);
  const sourceCounts = sourceCountsFromGPack0(gpack);
  const gateCount = gpack.PreNAND.gates.length;

  const decision = {
    kind: 'SATDecision0',
    version: CHECKER_VERSION,

    InputKind: 'BooleanCircuit',

    NandConversion: {
      kind: 'NandConversion0',
      deterministic: true,
      polynomial: true,
      preservesSatisfiability: true,
      preservesBooleanSemantics: true,
      outputCircuitKind: 'NAND',
    },

    LockedWord: {
      kind: 'LockedNANDWord0',
      baseline,
      fullWordSize: baseline + 4,
      residualSlackMax: 4,
      gpackDigest: digestCanonical0(gpack),
    },

    Baseline: {
      kind: 'LockedNANDBaseline0',
      formula: '18m+10wEq+3w0+2w1+2(3m-1)',
      gateCount,
      equalityOccurrences: sourceCounts.equalityOccurrences,
      constZeroOccurrences: sourceCounts.constZeroOccurrences,
      constOneOccurrences: sourceCounts.constOneOccurrences,
      value: baseline,
    },

    DecisionRule: {
      kind: 'SATDecisionRule0',
      comparator: 'minSize>baseline',
      satWhen: 'minSizeAboveBaseline',
      unsatWhen: 'minSizeEqualsBaseline',
      usesExactMinimum: true,
      rejectsApproximateMinimum: true,
    },

    Cases: [
      {
        id: 'sat.synthetic',
        satisfiable: true,
        baseline,
        minSize: baseline + 1,
        residualSlackMax: 4,
        decision: 'SAT',
      },
      {
        id: 'unsat.synthetic',
        satisfiable: false,
        baseline,
        minSize: baseline,
        residualSlackMax: 4,
        decision: 'UNSAT',
      },
    ],

    PiSATDecision: {
      kind: 'PiSATDecision0',
      version: CHECKER_VERSION,
      note: 'synthetic SAT decision proof marker',
    },
  };

  return {
    ...decision,
    ...overrides,
  };
}

export function makeSyntheticSATBounds0(overrides = {}) {
  return {
    kind: 'SATBounds0',
    version: CHECKER_VERSION,

    Converter: {
      kind: 'SATToNANDBounds0',
      deterministic: true,
      polynomial: true,
      preservesSatisfiability: true,
      exponent: 2,
    },

    LockedBuilder: {
      kind: 'LockedBuilderBounds0',
      deterministic: true,
      polynomial: true,
      residualSlackMax: 4,
      fullWordOverhead: 4,
      usesPublicSchedule: true,
    },

    Minimizer: {
      kind: 'ResidualBandMinimizerBounds0',
      exact: true,
      polynomialWhenResidualSlackBounded: true,
      residualSlackBound: 4,
      exponent: 36,
    },

    DecisionProcedure: {
      kind: 'SATDecisionBounds0',
      deterministic: true,
      polynomial: true,
      comparator: 'minSize>baseline',
      returnsBoolean: true,
    },

    Bounds: {
      kind: 'FinalSATPolynomialBounds0',
      finite: true,
      polynomial: true,
      noPrivateSchedule: true,
      inputVariable: 'n',
      exponent: 42,
    },

    PiSATBounds: {
      kind: 'PiSATBounds0',
      version: CHECKER_VERSION,
      note: 'synthetic SAT polynomial bounds proof marker',
    },

    ...overrides,
  };
}

export function makeSyntheticFinalIntegration0({
  gpack = makeSyntheticGPack0(),
  overrides = {},
} = {}) {
  const integration = {
    kind: 'FinalIntegration0',
    version: CHECKER_VERSION,
    GPack: gpack,
    GlobalProofDAG: makeSyntheticGlobalProofDAG0(),
    FinalMatch: makeSyntheticFinalFrameworkMatch0({
      gpack,
    }),
    SATDecision: makeSyntheticSATDecision0({
      gpack,
    }),
    SATBounds: makeSyntheticSATBounds0(),
    PhaseOrder: FINAL_INTEGRATION_PHASES0,
    PiFinalIntegration: {
      kind: 'PiFinalIntegration0',
      version: CHECKER_VERSION,
      note: 'synthetic final integration proof marker',
    },
  };

  return {
    ...integration,
    ...overrides,
  };
}

export async function CheckFinalFrameworkMatch0(match) {
  const checker = 'CheckFinalFrameworkMatch0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateFinalMatchShape0(match)],
    ['syntax', `${checker}.syntax`, () => validateSyntaxMap0(match)],
    ['charge', `${checker}.charge`, () => validateChargeMap0(match)],
    ['carrier', `${checker}.carrier`, () => validateCarrierMap0(match)],
    ['output', `${checker}.output`, () => validateOutputMap0(match)],
    ['minimum', `${checker}.minimum`, () => validateMinMap0(match)],
    ['norm', `${checker}.norm`, () => validateNormBridge0(match)],
    ['slack', `${checker}.slack`, () => validateSlackMap0(match)],
    ['imports', `${checker}.imports`, () => validateFrameworkImports0(match)],
    ['noHiddenMin', `${checker}.noHiddenMin`, () => validateNoHiddenExecutableMin0(match, ['FinalFrameworkMatch0'])],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(match, ['FinalFrameworkMatch0'])],
  ];

  for (const [phase, coord, run] of phases) {
    const result = run();

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: digestCanonical0(result.nf ?? result.witness ?? null),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'FinalFrameworkMatch0NF',
    checker,
    version: CHECKER_VERSION,
    baseline: match.ChargeMap.baseline,
    fullWordSize: match.ChargeMap.fullWordSize,
    syntaxDigest: digestCanonical0(match.SyntaxMap),
    chargeDigest: digestCanonical0(match.ChargeMap),
    carrierDigest: digestCanonical0(match.CarrierMap),
    outputDigest: digestCanonical0(match.OutputMap),
    minDigest: digestCanonical0(match.MinMap),
    slackDigest: digestCanonical0(match.SlackMap),
    piMatchDigest: digestCanonical0(getPiMatch0(match)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckSATDecision0(decision) {
  const checker = 'CheckSATDecision0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateSATDecisionShape0(decision)],
    ['conversion', `${checker}.conversion`, () => validateSATConversion0(decision)],
    ['baseline', `${checker}.baseline`, () => validateSATBaseline0(decision)],
    ['decisionRule', `${checker}.decisionRule`, () => validateSATDecisionRule0(decision)],
    ['cases', `${checker}.cases`, () => validateSATDecisionCases0(decision)],
    ['noHiddenMin', `${checker}.noHiddenMin`, () => validateNoHiddenExecutableMin0(decision, ['SATDecision0'])],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(decision, ['SATDecision0'])],
  ];

  for (const [phase, coord, run] of phases) {
    const result = run();

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: digestCanonical0(result.nf ?? result.witness ?? null),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'SATDecision0NF',
    checker,
    version: CHECKER_VERSION,
    baseline: decision.Baseline.value,
    fullWordSize: decision.LockedWord.fullWordSize,
    caseCount: decision.Cases.length,
    comparator: decision.DecisionRule.comparator,
    piSATDecisionDigest: digestCanonical0(getPiSATDecision0(decision)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckSATBounds0(bounds) {
  const checker = 'CheckSATBounds0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateSATBoundsShape0(bounds)],
    ['converter', `${checker}.converter`, () => validateSATBoundsConverter0(bounds)],
    ['lockedBuilder', `${checker}.lockedBuilder`, () => validateSATBoundsLockedBuilder0(bounds)],
    ['minimizer', `${checker}.minimizer`, () => validateSATBoundsMinimizer0(bounds)],
    ['decision', `${checker}.decision`, () => validateSATBoundsDecision0(bounds)],
    ['bounds', `${checker}.bounds`, () => validateSATBoundsGlobal0(bounds)],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(bounds, ['SATBounds0'])],
  ];

  for (const [phase, coord, run] of phases) {
    const result = run();

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: digestCanonical0(result.nf ?? result.witness ?? null),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'SATBounds0NF',
    checker,
    version: CHECKER_VERSION,
    converterExponent: bounds.Converter.exponent,
    minimizerExponent: bounds.Minimizer.exponent,
    finalExponent: bounds.Bounds.exponent,
    residualSlackBound: bounds.Minimizer.residualSlackBound,
    piSATBoundsDigest: digestCanonical0(getPiSATBounds0(bounds)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckFinalIntegration0(integration) {
  const checker = 'CheckFinalIntegration0';
  const ledger = [];

  const shape = validateFinalIntegrationShape0(integration);

  ledger.push({
    phase: 'shape',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  const phases = [
    ['CheckGPack0', `${checker}.GPack`, ['GPack'], await CheckGPack0(integration.GPack)],
    ['CheckGlobalProofDAG0', `${checker}.GlobalProofDAG`, ['GlobalProofDAG'], await CheckGlobalProofDAG0(integration.GlobalProofDAG)],
    ['CheckFinalFrameworkMatch0', `${checker}.FinalMatch`, ['FinalMatch'], await CheckFinalFrameworkMatch0(integration.FinalMatch)],
    ['CheckSATDecision0', `${checker}.SATDecision`, ['SATDecision'], await CheckSATDecision0(integration.SATDecision)],
    ['CheckSATBounds0', `${checker}.SATBounds`, ['SATBounds'], await CheckSATBounds0(integration.SATBounds)],
  ];

  for (const [phase, coord, path, record] of phases) {
    const result = recordToValidation0(record, path);

    ledger.push({
      phase,
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const globalGLinkage = validateFinalIntegrationGlobalGLinkage0(integration);

  ledger.push({
    phase: 'globalGLinkage',
    status: globalGLinkage.ok ? 'pass' : 'fail',
    digest: digestCanonical0(globalGLinkage.nf ?? globalGLinkage.witness ?? null),
  });

  if (!globalGLinkage.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.globalGLinkage`,
      path: globalGLinkage.path,
      witness: globalGLinkage.witness,
      ledger,
    });
  }

  const noOpaque = validateNoOpaqueProof0(integration, ['FinalIntegration0']);

  ledger.push({
    phase: 'opaque',
    status: noOpaque.ok ? 'pass' : 'fail',
    digest: digestCanonical0(noOpaque.nf ?? noOpaque.witness ?? null),
  });

  if (!noOpaque.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.opaqueProof`,
      path: noOpaque.path,
      witness: noOpaque.witness,
      ledger,
    });
  }

  const nf = {
    kind: 'FinalIntegration0NF',
    checker,
    version: CHECKER_VERSION,
    phases: FINAL_INTEGRATION_PHASES0,
    gpackDigest: digestCanonical0(integration.GPack),
    globalProofDAGDigest: digestCanonical0(integration.GlobalProofDAG),
    finalMatchDigest: digestCanonical0(integration.FinalMatch),
    satDecisionDigest: digestCanonical0(integration.SATDecision),
    satBoundsDigest: digestCanonical0(integration.SATBounds),
    piFinalIntegrationDigest: digestCanonical0(getPiFinalIntegration0(integration)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateFinalIntegrationGlobalGLinkage0(integration) {
  if (!isPlainObject(integration.GlobalProofDAG)) {
    return validationReject0(['GlobalProofDAG'], 'FinalIntegration0 must include GlobalProofDAG', {
      actual: typeof integration.GlobalProofDAG,
    });
  }

  const gpackDigest = digestCanonical0(integration.GPack);
  const expectedGProofId = 'G.ThresholdCert.proof';

  const gProofRef = integration.GPack?.ThresholdCert?.derivation?.proofRef;

  if (
    !isPlainObject(gProofRef) ||
    gProofRef.kind !== 'ProofRef0' ||
    gProofRef.refKind !== 'KPrimitive' ||
    gProofRef.id !== expectedGProofId
  ) {
    return validationReject0(['GPack', 'ThresholdCert', 'derivation', 'proofRef'], 'FinalIntegration0 requires GPack threshold derivation proofRef G.ThresholdCert.proof', {
      actual: gProofRef,
    });
  }

  const nodeById = new Map();

  for (const node of integration.GlobalProofDAG.Nodes ?? []) {
    if (isPlainObject(node) && typeof node.id === 'string') {
      nodeById.set(node.id, node);
    }
  }

  const thresholdNode = nodeById.get(expectedGProofId);

  if (!isPlainObject(thresholdNode)) {
    return validationReject0(['GlobalProofDAG', 'Nodes', expectedGProofId], 'GlobalProofDAG must contain G.ThresholdCert.proof', null);
  }

  const proofRef = thresholdNode.conclusion?.proofRef;

  if (
    !isPlainObject(proofRef) ||
    proofRef.kind !== 'ProofRef0' ||
    proofRef.refKind !== 'KPrimitive' ||
    proofRef.id !== expectedGProofId
  ) {
    return validationReject0(['GlobalProofDAG', 'Nodes', expectedGProofId, 'conclusion', 'proofRef'], 'GlobalProofDAG G threshold proofRef mismatch', {
      actual: proofRef,
    });
  }

  for (const [field, expected] of Object.entries({
    package: 'G',
    rule: 'LockedNANDThreshold0',
    derivationKind: 'ThresholdDerivation0',
    residualSlackMax: 4,
    satIffMinAboveBaseline: true,
    unsatMinEqualsBaseline: true,
    finalOutputGates: 4,
    baselineDerivation: 'G.BaselineCert.proof',
    traceDerivation: 'G.TraceCert.proof',
    transparentProof: true,
  })) {
    if (thresholdNode.payload?.[field] !== expected) {
      return validationReject0(['GlobalProofDAG', 'Nodes', expectedGProofId, 'payload', field], 'GlobalProofDAG G threshold payload mismatch', {
        expected,
        actual: thresholdNode.payload?.[field],
      });
    }
  }

  const packageNode = nodeById.get('Package.G.LockedNANDThreshold');

  if (!isPlainObject(packageNode) || !Array.isArray(packageNode.premises)) {
    return validationReject0(['GlobalProofDAG', 'Nodes', 'Package.G.LockedNANDThreshold'], 'GlobalProofDAG must contain Package.G.LockedNANDThreshold', null);
  }

  if (!packageNode.premises.includes(expectedGProofId)) {
    return validationReject0(['GlobalProofDAG', 'Nodes', 'Package.G.LockedNANDThreshold', 'premises'], 'Package.G.LockedNANDThreshold must depend on G.ThresholdCert.proof', {
      actual: packageNode.premises,
    });
  }

  const finalNode = nodeById.get('Final.AcceptedPackageImpliesSATinP');

  if (!isPlainObject(finalNode) || !Array.isArray(finalNode.premises) || !finalNode.premises.includes('Package.G.LockedNANDThreshold')) {
    return validationReject0(['GlobalProofDAG', 'Nodes', 'Final.AcceptedPackageImpliesSATinP', 'premises'], 'Final SAT-in-P theorem must depend on Package.G.LockedNANDThreshold', {
      actual: finalNode?.premises,
    });
  }

  const lockedWordDigest = integration.SATDecision?.LockedWord?.gpackDigest;
  const finalMatchDigest = integration.FinalMatch?.PG?.gpackDigest;

  for (const [path, actual] of [
    [['SATDecision', 'LockedWord', 'gpackDigest'], lockedWordDigest],
    [['FinalMatch', 'PG', 'gpackDigest'], finalMatchDigest],
  ]) {
    if (!isPlainObject(actual) || actual.hex !== gpackDigest.hex || actual.alg !== gpackDigest.alg) {
      return validationReject0(path, 'FinalIntegration0 must bind SATDecision and FinalMatch to the accepted GPack digest', {
        expected: gpackDigest,
        actual,
      });
    }
  }

  return validationAccept0({
    kind: 'FinalIntegrationGlobalGLinkage0NF',
    gpackDigest,
    thresholdProofRef: expectedGProofId,
  });
}


function validateFinalMatchShape0(match) {
  if (!isPlainObject(match)) {
    return validationReject0([], 'FinalFrameworkMatch0 must be an object', {
      actual: typeof match,
    });
  }

  if (match.kind !== undefined && match.kind !== 'FinalFrameworkMatch0') {
    return validationReject0(['kind'], 'FinalFrameworkMatch0 kind must be FinalFrameworkMatch0 when present', {
      actual: match.kind,
    });
  }

  if (match.version !== undefined && match.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalFrameworkMatch0 version must be ${CHECKER_VERSION} when present`, {
      actual: match.version,
    });
  }

  for (const field of FINAL_FRAMEWORK_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(match, field)) {
      return validationReject0([field], 'FinalFrameworkMatch0 is missing a required field', {
        field,
      });
    }
  }

  if (getPiMatch0(match) === undefined) {
    return validationReject0(['PiMatch'], 'FinalFrameworkMatch0 is missing PiMatch or Πmatch', null);
  }

  return validationAccept0({
    kind: 'FinalFrameworkMatchShape0NF',
  });
}

function validateSyntaxMap0(match) {
  if (!isPlainObject(match.SyntaxMap)) {
    return validationReject0(['SyntaxMap'], 'SyntaxMap must be an object', {
      actual: typeof match.SyntaxMap,
    });
  }

  if (match.SyntaxMap.sameNANDSyntax !== true) {
    return validationReject0(['SyntaxMap', 'sameNANDSyntax'], 'SyntaxMap must certify identical NAND syntax', {
      actual: match.SyntaxMap.sameNANDSyntax,
    });
  }

  const canonical = match.SyntaxMap.canonical;

  if (!sameSyntax0(canonical, FINAL_CANONICAL_NAND_SYNTAX0)) {
    return validationReject0(['SyntaxMap', 'canonical'], 'SyntaxMap canonical NAND syntax mismatch', {
      expected: FINAL_CANONICAL_NAND_SYNTAX0,
      actual: canonical,
    });
  }

  if (!sameSyntax0(match.PO.syntax, FINAL_CANONICAL_NAND_SYNTAX0)) {
    return validationReject0(['PO', 'syntax'], 'Package O syntax does not match canonical NAND syntax', {
      actual: match.PO.syntax,
    });
  }

  if (!sameSyntax0(match.PG.syntax, FINAL_CANONICAL_NAND_SYNTAX0)) {
    return validationReject0(['PG', 'syntax'], 'Package G syntax does not match canonical NAND syntax', {
      actual: match.PG.syntax,
    });
  }

  return validationAccept0({
    kind: 'SyntaxMap0NF',
  });
}

function validateChargeMap0(match) {
  const map = match.ChargeMap;

  if (!isPlainObject(map)) {
    return validationReject0(['ChargeMap'], 'ChargeMap must be an object', {
      actual: typeof map,
    });
  }

  for (const field of [
    'sameChargeConvention',
    'materializersCharged',
    'uniqueOwners',
  ]) {
    if (map[field] !== true) {
      return validationReject0(['ChargeMap', field], `ChargeMap must certify ${field}`, {
        actual: map[field],
      });
    }
  }

  if (map.ordinaryNandWeight !== 1) {
    return validationReject0(['ChargeMap', 'ordinaryNandWeight'], 'ordinary NAND weight must be one', {
      actual: map.ordinaryNandWeight,
    });
  }

  if (!Number.isInteger(map.baseline) || map.baseline <= 0) {
    return validationReject0(['ChargeMap', 'baseline'], 'ChargeMap baseline must be a positive integer', {
      actual: map.baseline,
    });
  }

  if (map.fullWordSize !== map.baseline + 4) {
    return validationReject0(['ChargeMap', 'fullWordSize'], 'ChargeMap fullWordSize must equal baseline plus four', {
      expected: map.baseline + 4,
      actual: map.fullWordSize,
    });
  }

  if (match.PO.chargeConvention?.ordinaryNandWeight !== 1 || match.PG.chargeConvention?.ordinaryNandWeight !== 1) {
    return validationReject0(['ChargeMap'], 'Package O and Package G must use unit NAND charge', {
      po: match.PO.chargeConvention,
      pg: match.PG.chargeConvention,
    });
  }

  return validationAccept0({
    kind: 'ChargeMap0NF',
    baseline: map.baseline,
  });
}

function validateCarrierMap0(match) {
  const map = match.CarrierMap;

  if (!isPlainObject(map)) {
    return validationReject0(['CarrierMap'], 'CarrierMap must be an object', {
      actual: typeof map,
    });
  }

  if (map.sameCarrierConvention !== true) {
    return validationReject0(['CarrierMap', 'sameCarrierConvention'], 'CarrierMap must certify same carrier convention', {
      actual: map.sameCarrierConvention,
    });
  }

  if (map.lockedCarrierCompatible !== true) {
    return validationReject0(['CarrierMap', 'lockedCarrierCompatible'], 'CarrierMap must certify locked carrier compatibility', {
      actual: map.lockedCarrierCompatible,
    });
  }

  if (!arrayContainsAll0(map.slotFamilies, ['X', 'T', 'O', 'R', 'L', 'z'])) {
    return validationReject0(['CarrierMap', 'slotFamilies'], 'CarrierMap is missing locked NAND slot families', {
      actual: map.slotFamilies,
    });
  }

  if (map.carrierConstants !== 'macro-enforced') {
    return validationReject0(['CarrierMap', 'carrierConstants'], 'carrier constants must be macro-enforced', {
      actual: map.carrierConstants,
    });
  }

  return validationAccept0({
    kind: 'CarrierMap0NF',
  });
}

function validateOutputMap0(match) {
  const map = match.OutputMap;

  if (!isPlainObject(map)) {
    return validationReject0(['OutputMap'], 'OutputMap must be an object', {
      actual: typeof map,
    });
  }

  if (map.sameOutputConvention !== true) {
    return validationReject0(['OutputMap', 'sameOutputConvention'], 'OutputMap must certify same output convention', {
      actual: map.sameOutputConvention,
    });
  }

  if (map.oneOutput !== true) {
    return validationReject0(['OutputMap', 'oneOutput'], 'OutputMap must certify a single final locked output', {
      actual: map.oneOutput,
    });
  }

  if (map.outputName !== 'Fphi') {
    return validationReject0(['OutputMap', 'outputName'], 'OutputMap outputName must be Fphi', {
      actual: map.outputName,
    });
  }

  if (map.finalLock !== 'z') {
    return validationReject0(['OutputMap', 'finalLock'], 'OutputMap finalLock must be z', {
      actual: map.finalLock,
    });
  }

  if (map.satDecisionUsesOutput !== true) {
    return validationReject0(['OutputMap', 'satDecisionUsesOutput'], 'SAT decision must use the final locked output', {
      actual: map.satDecisionUsesOutput,
    });
  }

  return validationAccept0({
    kind: 'OutputMap0NF',
  });
}

function validateMinMap0(match) {
  const map = match.MinMap;

  if (!isPlainObject(map)) {
    return validationReject0(['MinMap'], 'MinMap must be an object', {
      actual: typeof map,
    });
  }

  for (const field of [
    'sameMinimumNotion',
    'exactMinimum',
    'sameFrontierMinimum',
  ]) {
    if (map[field] !== true) {
      return validationReject0(['MinMap', field], `MinMap must certify ${field}`, {
        actual: map[field],
      });
    }
  }

  if (map.minimizer !== 'PCCMin') {
    return validationReject0(['MinMap', 'minimizer'], 'MinMap minimizer must be PCCMin', {
      actual: map.minimizer,
    });
  }

  if (map.decisionComparator !== 'minSize>baseline') {
    return validationReject0(['MinMap', 'decisionComparator'], 'MinMap comparator must be minSize>baseline', {
      actual: map.decisionComparator,
    });
  }

  return validationAccept0({
    kind: 'MinMap0NF',
  });
}

function validateNormBridge0(match) {
  const bridge = match.NormBridge;

  if (!isPlainObject(bridge)) {
    return validationReject0(['NormBridge'], 'NormBridge must be an object', {
      actual: typeof bridge,
    });
  }

  for (const field of [
    'normalizationPreservesSemantics',
    'normalizationPreservesMinimum',
    'normalizationPreservesResidualSlack',
    'transportProofs',
  ]) {
    if (bridge[field] !== true) {
      return validationReject0(['NormBridge', field], `NormBridge must certify ${field}`, {
        actual: bridge[field],
      });
    }
  }

  return validationAccept0({
    kind: 'NormBridge0NF',
  });
}

function validateSlackMap0(match) {
  const map = match.SlackMap;

  if (!isPlainObject(map)) {
    return validationReject0(['SlackMap'], 'SlackMap must be an object', {
      actual: typeof map,
    });
  }

  if (map.sameResidualSlackDefinition !== true) {
    return validationReject0(['SlackMap', 'sameResidualSlackDefinition'], 'SlackMap must certify same residual slack definition', {
      actual: map.sameResidualSlackDefinition,
    });
  }

  if (map.definition !== 'Lambda(C)=|C|-mu(C)') {
    return validationReject0(['SlackMap', 'definition'], 'SlackMap residual slack definition mismatch', {
      actual: map.definition,
    });
  }

  if (!Number.isInteger(map.lockedResidualSlackMax) || map.lockedResidualSlackMax > 4 || map.lockedResidualSlackMax < 0) {
    return validationReject0(['SlackMap', 'lockedResidualSlackMax'], 'locked residual slack must be an integer at most four', {
      actual: map.lockedResidualSlackMax,
    });
  }

  if (!Number.isInteger(map.gpackResidualSlackMax) || map.gpackResidualSlackMax > 4 || map.gpackResidualSlackMax < 0) {
    return validationReject0(['SlackMap', 'gpackResidualSlackMax'], 'GPack residual slack must be an integer at most four', {
      actual: map.gpackResidualSlackMax,
    });
  }

  if (map.fullWordSize !== map.baseline + 4) {
    return validationReject0(['SlackMap', 'fullWordSize'], 'SlackMap fullWordSize must equal baseline plus four', {
      expected: map.baseline + 4,
      actual: map.fullWordSize,
    });
  }

  return validationAccept0({
    kind: 'SlackMap0NF',
  });
}

function validateFrameworkImports0(match) {
  const poImports = normalizeList0(match.PO.imports);
  const pgImports = normalizeList0(match.PG.imports);

  for (let index = 0; index < poImports.length; index += 1) {
    if (poImports[index] === 'G' || poImports[index] === 'PG') {
      return validationReject0(['PO', 'imports', index], 'Package O must not import Package G', {
        import: poImports[index],
      });
    }
  }

  for (let index = 0; index < pgImports.length; index += 1) {
    if (pgImports[index] === 'O' || pgImports[index] === 'PO') {
      return validationReject0(['PG', 'imports', index], 'Package G must not import Package O', {
        import: pgImports[index],
      });
    }
  }

  const edges = match.ImportMap?.edges ?? [];
  const forbidden = new Set(FINAL_FRAMEWORK_FORBIDDEN_IMPORT_EDGES0.map((edge) => edgeKey0(edge)));

  if (!Array.isArray(edges)) {
    return validationReject0(['ImportMap', 'edges'], 'ImportMap edges must be an array when present', {
      actual: typeof edges,
    });
  }

  for (let index = 0; index < edges.length; index += 1) {
    const edge = normalizeEdge0(edges[index]);

    if (edge === null) {
      return validationReject0(['ImportMap', 'edges', index], 'ImportMap edge must have from and to endpoints', {
        edge: edges[index],
      });
    }

    if (forbidden.has(edgeKey0(edge))) {
      return validationReject0(['ImportMap', 'edges', index], 'Final framework contains a forbidden O/G import edge', {
        edge,
      });
    }
  }

  return validationAccept0({
    kind: 'FinalFrameworkImports0NF',
  });
}

function validateSATDecisionShape0(decision) {
  if (!isPlainObject(decision)) {
    return validationReject0([], 'SATDecision0 must be an object', {
      actual: typeof decision,
    });
  }

  if (decision.kind !== undefined && decision.kind !== 'SATDecision0') {
    return validationReject0(['kind'], 'SATDecision0 kind must be SATDecision0 when present', {
      actual: decision.kind,
    });
  }

  if (decision.version !== undefined && decision.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `SATDecision0 version must be ${CHECKER_VERSION} when present`, {
      actual: decision.version,
    });
  }

  for (const field of SAT_DECISION_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(decision, field)) {
      return validationReject0([field], 'SATDecision0 is missing a required field', {
        field,
      });
    }
  }

  if (!Array.isArray(decision.Cases)) {
    return validationReject0(['Cases'], 'SATDecision0 Cases must be an array', {
      actual: typeof decision.Cases,
    });
  }

  if (getPiSATDecision0(decision) === undefined) {
    return validationReject0(['PiSATDecision'], 'SATDecision0 is missing PiSATDecision or Πsat', null);
  }

  return validationAccept0({
    kind: 'SATDecisionShape0NF',
  });
}

function validateSATConversion0(decision) {
  const conversion = decision.NandConversion;

  if (!isPlainObject(conversion)) {
    return validationReject0(['NandConversion'], 'NandConversion must be an object', {
      actual: typeof conversion,
    });
  }

  for (const field of [
    'deterministic',
    'polynomial',
    'preservesSatisfiability',
    'preservesBooleanSemantics',
  ]) {
    if (conversion[field] !== true) {
      return validationReject0(['NandConversion', field], `NandConversion must certify ${field}`, {
        actual: conversion[field],
      });
    }
  }

  if (conversion.outputCircuitKind !== 'NAND') {
    return validationReject0(['NandConversion', 'outputCircuitKind'], 'NandConversion outputCircuitKind must be NAND', {
      actual: conversion.outputCircuitKind,
    });
  }

  return validationAccept0({
    kind: 'SATConversion0NF',
  });
}

function validateSATBaseline0(decision) {
  if (!isPlainObject(decision.Baseline)) {
    return validationReject0(['Baseline'], 'Baseline must be an object', {
      actual: typeof decision.Baseline,
    });
  }

  const b = decision.Baseline;

  for (const field of [
    'gateCount',
    'equalityOccurrences',
    'constZeroOccurrences',
    'constOneOccurrences',
    'value',
  ]) {
    if (!Number.isInteger(b[field]) || b[field] < 0) {
      return validationReject0(['Baseline', field], 'Baseline numeric fields must be non-negative integers', {
        field,
        actual: b[field],
      });
    }
  }

  if (b.gateCount <= 0 || b.value <= 0) {
    return validationReject0(['Baseline'], 'Baseline must have positive gateCount and value', {
      gateCount: b.gateCount,
      value: b.value,
    });
  }

  const expected = computeLockedNANDBaseline0({
    gateCount: b.gateCount,
    equalityOccurrences: b.equalityOccurrences,
    constZeroOccurrences: b.constZeroOccurrences,
    constOneOccurrences: b.constOneOccurrences,
  });

  if (b.value !== expected) {
    return validationReject0(['Baseline', 'value'], 'SATDecision baseline formula mismatch', {
      expected,
      actual: b.value,
    });
  }

  if (!isPlainObject(decision.LockedWord)) {
    return validationReject0(['LockedWord'], 'LockedWord must be an object', {
      actual: typeof decision.LockedWord,
    });
  }

  if (decision.LockedWord.baseline !== b.value) {
    return validationReject0(['LockedWord', 'baseline'], 'LockedWord baseline must match Baseline.value', {
      expected: b.value,
      actual: decision.LockedWord.baseline,
    });
  }

  if (decision.LockedWord.fullWordSize !== b.value + 4) {
    return validationReject0(['LockedWord', 'fullWordSize'], 'LockedWord fullWordSize must be baseline plus four', {
      expected: b.value + 4,
      actual: decision.LockedWord.fullWordSize,
    });
  }

  if (!Number.isInteger(decision.LockedWord.residualSlackMax) || decision.LockedWord.residualSlackMax > 4 || decision.LockedWord.residualSlackMax < 0) {
    return validationReject0(['LockedWord', 'residualSlackMax'], 'LockedWord residual slack must be an integer at most four', {
      actual: decision.LockedWord.residualSlackMax,
    });
  }

  return validationAccept0({
    kind: 'SATBaseline0NF',
    baseline: b.value,
  });
}

function validateSATDecisionRule0(decision) {
  const rule = decision.DecisionRule;

  if (!isPlainObject(rule)) {
    return validationReject0(['DecisionRule'], 'DecisionRule must be an object', {
      actual: typeof rule,
    });
  }

  if (rule.comparator !== 'minSize>baseline') {
    return validationReject0(['DecisionRule', 'comparator'], 'SAT decision comparator must be minSize>baseline', {
      actual: rule.comparator,
    });
  }

  if (rule.satWhen !== 'minSizeAboveBaseline') {
    return validationReject0(['DecisionRule', 'satWhen'], 'SAT decision satWhen must be minSizeAboveBaseline', {
      actual: rule.satWhen,
    });
  }

  if (rule.unsatWhen !== 'minSizeEqualsBaseline') {
    return validationReject0(['DecisionRule', 'unsatWhen'], 'SAT decision unsatWhen must be minSizeEqualsBaseline', {
      actual: rule.unsatWhen,
    });
  }

  if (rule.usesExactMinimum !== true) {
    return validationReject0(['DecisionRule', 'usesExactMinimum'], 'SAT decision must use an exact minimum', {
      actual: rule.usesExactMinimum,
    });
  }

  if (rule.rejectsApproximateMinimum !== true) {
    return validationReject0(['DecisionRule', 'rejectsApproximateMinimum'], 'SAT decision must reject approximate minima', {
      actual: rule.rejectsApproximateMinimum,
    });
  }

  return validationAccept0({
    kind: 'SATDecisionRule0NF',
  });
}

function validateSATDecisionCases0(decision) {
  const baseline = decision.Baseline.value;

  for (let index = 0; index < decision.Cases.length; index += 1) {
    const entry = decision.Cases[index];

    if (!isPlainObject(entry)) {
      return validationReject0(['Cases', index], 'SAT decision case must be an object', {
        actual: typeof entry,
      });
    }

    if (!isNonEmptyString(entry.id)) {
      return validationReject0(['Cases', index, 'id'], 'SAT decision case must have a non-empty id', {
        actual: entry.id,
      });
    }

    if (entry.baseline !== baseline) {
      return validationReject0(['Cases', index, 'baseline'], 'SAT decision case baseline mismatch', {
        expected: baseline,
        actual: entry.baseline,
      });
    }

    if (!Number.isInteger(entry.minSize) || entry.minSize < baseline) {
      return validationReject0(['Cases', index, 'minSize'], 'SAT decision case minSize must be an integer at least baseline', {
        baseline,
        actual: entry.minSize,
      });
    }

    const expectedDecision = entry.minSize > baseline ? 'SAT' : 'UNSAT';

    if (entry.decision !== expectedDecision) {
      return validationReject0(['Cases', index, 'decision'], 'SAT decision case does not match minSize>baseline rule', {
        expected: expectedDecision,
        actual: entry.decision,
      });
    }

    if (entry.satisfiable === true && (entry.minSize <= baseline || entry.minSize > baseline + 4)) {
      return validationReject0(['Cases', index, 'minSize'], 'satisfiable locked NAND case must have minimum between baseline plus one and baseline plus four', {
        baseline,
        minSize: entry.minSize,
      });
    }

    if (entry.satisfiable === false && entry.minSize !== baseline) {
      return validationReject0(['Cases', index, 'minSize'], 'unsatisfiable locked NAND case must have minimum equal to baseline', {
        baseline,
        minSize: entry.minSize,
      });
    }

    if (!Number.isInteger(entry.residualSlackMax) || entry.residualSlackMax > 4 || entry.residualSlackMax < 0) {
      return validationReject0(['Cases', index, 'residualSlackMax'], 'SAT decision case residual slack must be an integer at most four', {
        actual: entry.residualSlackMax,
      });
    }
  }

  return validationAccept0({
    kind: 'SATDecisionCases0NF',
    caseCount: decision.Cases.length,
  });
}

function validateSATBoundsShape0(bounds) {
  if (!isPlainObject(bounds)) {
    return validationReject0([], 'SATBounds0 must be an object', {
      actual: typeof bounds,
    });
  }

  if (bounds.kind !== undefined && bounds.kind !== 'SATBounds0') {
    return validationReject0(['kind'], 'SATBounds0 kind must be SATBounds0 when present', {
      actual: bounds.kind,
    });
  }

  if (bounds.version !== undefined && bounds.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `SATBounds0 version must be ${CHECKER_VERSION} when present`, {
      actual: bounds.version,
    });
  }

  for (const field of SAT_BOUNDS_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(bounds, field)) {
      return validationReject0([field], 'SATBounds0 is missing a required field', {
        field,
      });
    }
  }

  if (getPiSATBounds0(bounds) === undefined) {
    return validationReject0(['PiSATBounds'], 'SATBounds0 is missing PiSATBounds or Πsatbounds', null);
  }

  return validationAccept0({
    kind: 'SATBoundsShape0NF',
  });
}

function validateSATBoundsConverter0(bounds) {
  const converter = bounds.Converter;

  if (!isPlainObject(converter)) {
    return validationReject0(['Converter'], 'Converter bounds must be an object', {
      actual: typeof converter,
    });
  }

  for (const field of [
    'deterministic',
    'polynomial',
    'preservesSatisfiability',
  ]) {
    if (converter[field] !== true) {
      return validationReject0(['Converter', field], `Converter must certify ${field}`, {
        actual: converter[field],
      });
    }
  }

  if (!Number.isInteger(converter.exponent) || converter.exponent <= 0) {
    return validationReject0(['Converter', 'exponent'], 'Converter exponent must be positive', {
      actual: converter.exponent,
    });
  }

  return validationAccept0({
    kind: 'SATBoundsConverter0NF',
  });
}

function validateSATBoundsLockedBuilder0(bounds) {
  const builder = bounds.LockedBuilder;

  if (!isPlainObject(builder)) {
    return validationReject0(['LockedBuilder'], 'LockedBuilder bounds must be an object', {
      actual: typeof builder,
    });
  }

  for (const field of [
    'deterministic',
    'polynomial',
    'usesPublicSchedule',
  ]) {
    if (builder[field] !== true) {
      return validationReject0(['LockedBuilder', field], `LockedBuilder must certify ${field}`, {
        actual: builder[field],
      });
    }
  }

  if (!Number.isInteger(builder.residualSlackMax) || builder.residualSlackMax > 4 || builder.residualSlackMax < 0) {
    return validationReject0(['LockedBuilder', 'residualSlackMax'], 'LockedBuilder residualSlackMax must be an integer at most four', {
      actual: builder.residualSlackMax,
    });
  }

  if (builder.fullWordOverhead !== 4) {
    return validationReject0(['LockedBuilder', 'fullWordOverhead'], 'LockedBuilder fullWordOverhead must be four', {
      actual: builder.fullWordOverhead,
    });
  }

  return validationAccept0({
    kind: 'SATBoundsLockedBuilder0NF',
  });
}

function validateSATBoundsMinimizer0(bounds) {
  const minimizer = bounds.Minimizer;

  if (!isPlainObject(minimizer)) {
    return validationReject0(['Minimizer'], 'Minimizer bounds must be an object', {
      actual: typeof minimizer,
    });
  }

  if (minimizer.exact !== true) {
    return validationReject0(['Minimizer', 'exact'], 'Minimizer must be exact', {
      actual: minimizer.exact,
    });
  }

  if (minimizer.polynomialWhenResidualSlackBounded !== true) {
    return validationReject0(['Minimizer', 'polynomialWhenResidualSlackBounded'], 'Minimizer must be polynomial for bounded residual slack', {
      actual: minimizer.polynomialWhenResidualSlackBounded,
    });
  }

  if (!Number.isInteger(minimizer.residualSlackBound) || minimizer.residualSlackBound > 4 || minimizer.residualSlackBound < 0) {
    return validationReject0(['Minimizer', 'residualSlackBound'], 'Minimizer residualSlackBound must be an integer at most four', {
      actual: minimizer.residualSlackBound,
    });
  }

  if (!Number.isInteger(minimizer.exponent) || minimizer.exponent <= 0) {
    return validationReject0(['Minimizer', 'exponent'], 'Minimizer exponent must be positive', {
      actual: minimizer.exponent,
    });
  }

  return validationAccept0({
    kind: 'SATBoundsMinimizer0NF',
  });
}

function validateSATBoundsDecision0(bounds) {
  const decision = bounds.DecisionProcedure;

  if (!isPlainObject(decision)) {
    return validationReject0(['DecisionProcedure'], 'DecisionProcedure bounds must be an object', {
      actual: typeof decision,
    });
  }

  for (const field of [
    'deterministic',
    'polynomial',
    'returnsBoolean',
  ]) {
    if (decision[field] !== true) {
      return validationReject0(['DecisionProcedure', field], `DecisionProcedure must certify ${field}`, {
        actual: decision[field],
      });
    }
  }

  if (decision.comparator !== 'minSize>baseline') {
    return validationReject0(['DecisionProcedure', 'comparator'], 'DecisionProcedure comparator must be minSize>baseline', {
      actual: decision.comparator,
    });
  }

  return validationAccept0({
    kind: 'SATBoundsDecision0NF',
  });
}

function validateSATBoundsGlobal0(bounds) {
  const global = bounds.Bounds;

  if (!isPlainObject(global)) {
    return validationReject0(['Bounds'], 'SATBounds global Bounds must be an object', {
      actual: typeof global,
    });
  }

  for (const field of [
    'finite',
    'polynomial',
    'noPrivateSchedule',
  ]) {
    if (global[field] !== true) {
      return validationReject0(['Bounds', field], `SATBounds global Bounds must certify ${field}`, {
        actual: global[field],
      });
    }
  }

  if (!Number.isInteger(global.exponent) || global.exponent <= 0) {
    return validationReject0(['Bounds', 'exponent'], 'SATBounds global exponent must be positive', {
      actual: global.exponent,
    });
  }

  return validationAccept0({
    kind: 'SATBoundsGlobal0NF',
  });
}

function validateFinalIntegrationShape0(integration) {
  if (!isPlainObject(integration)) {
    return validationReject0([], 'FinalIntegration0 must be an object', {
      actual: typeof integration,
    });
  }

  if (integration.kind !== undefined && integration.kind !== 'FinalIntegration0') {
    return validationReject0(['kind'], 'FinalIntegration0 kind must be FinalIntegration0 when present', {
      actual: integration.kind,
    });
  }

  if (integration.version !== undefined && integration.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalIntegration0 version must be ${CHECKER_VERSION} when present`, {
      actual: integration.version,
    });
  }

  for (const field of [
    'GPack',
    'FinalMatch',
    'SATDecision',
    'SATBounds',
    'PhaseOrder',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(integration, field)) {
      return validationReject0([field], 'FinalIntegration0 is missing a required field', {
        field,
      });
    }
  }

  if (!Array.isArray(integration.PhaseOrder)) {
    return validationReject0(['PhaseOrder'], 'FinalIntegration0 PhaseOrder must be an array', null);
  }

  for (let index = 0; index < FINAL_INTEGRATION_PHASES0.length; index += 1) {
    if (integration.PhaseOrder[index] !== FINAL_INTEGRATION_PHASES0[index]) {
      return validationReject0(['PhaseOrder', index], 'FinalIntegration0 PhaseOrder mismatch', {
        expected: FINAL_INTEGRATION_PHASES0[index],
        actual: integration.PhaseOrder[index],
      });
    }
  }

  if (getPiFinalIntegration0(integration) === undefined) {
    return validationReject0(['PiFinalIntegration'], 'FinalIntegration0 is missing PiFinalIntegration or Πfinalint', null);
  }

  return validationAccept0({
    kind: 'FinalIntegrationShape0NF',
  });
}

function validateNoHiddenExecutableMin0(value, path) {
  const hit = findForbiddenExecutableUse0(value, path, false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'FinalNoHiddenExecutableMin0NF',
  });
}

function validateNoOpaqueProof0(value, path) {
  const hit = findOpaqueProof0(value, path);

  if (hit !== null) {
    return validationReject0(hit.path, 'opaque proof material is not allowed in final integration', hit);
  }

  return validationAccept0({
    kind: 'FinalNoOpaqueProof0NF',
  });
}

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && FINAL_FRAMEWORK_FORBIDDEN_EXEC_SYMBOLS0.includes(value)) {
      return {
        symbol: value,
        path,
      };
    }

    return null;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findForbiddenExecutableUse0(value[index], [...path, index], inExecutablePosition);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const key of Object.keys(value)) {
    const nextExecutablePosition =
      inExecutablePosition ||
      EXECUTABLE_KEYS0.has(key) ||
      /exec|call|program|body|operator|operation/i.test(key);

    const hit = findForbiddenExecutableUse0(value[key], [...path, key], nextExecutablePosition);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function findOpaqueProof0(value, path = []) {
  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      const hit = findOpaqueProof0(value[index], [...path, index]);

      if (hit !== null) {
        return hit;
      }
    }

    return null;
  }

  if (!isPlainObject(value)) {
    return null;
  }

  for (const key of Object.keys(value)) {
    if (/opaque|proofblob|trustedblob|assumeproof/i.test(key)) {
      return {
        key,
        path: [...path, key],
        value: value[key],
      };
    }

    const hit = findOpaqueProof0(value[key], [...path, key]);

    if (hit !== null) {
      return hit;
    }
  }

  return null;
}

function baselineFromGPack0(gpack) {
  if (Number.isInteger(gpack?.BaselineCert?.baseline)) {
    return gpack.BaselineCert.baseline;
  }

  return computeLockedNANDBaseline0({
    gateCount: gpack.PreNAND.gates.length,
    ...sourceCountsFromGPack0(gpack),
  });
}

function sourceCountsFromGPack0(gpack) {
  const sourceOccurrences = gpack.PreNAND?.sourceOccurrences ?? {};

  return {
    equalityOccurrences:
      sourceOccurrences.equality ??
      sourceOccurrences.equalityOccurrences ??
      sourceOccurrences.wEq ??
      0,
    constZeroOccurrences:
      sourceOccurrences.const0 ??
      sourceOccurrences.constZero ??
      sourceOccurrences.constZeroOccurrences ??
      sourceOccurrences.w0 ??
      0,
    constOneOccurrences:
      sourceOccurrences.const1 ??
      sourceOccurrences.constOne ??
      sourceOccurrences.constOneOccurrences ??
      sourceOccurrences.w1 ??
      0,
  };
}

function sameSyntax0(actual, expected) {
  if (!isPlainObject(actual) || !isPlainObject(expected)) {
    return false;
  }

  for (const [key, value] of Object.entries(expected)) {
    if (actual[key] !== value) {
      return false;
    }
  }

  return true;
}

function normalizeList0(value) {
  if (!Array.isArray(value)) {
    return [];
  }

  return value.map((entry) => String(entry));
}

function normalizeEdge0(edge) {
  if (Array.isArray(edge) && edge.length >= 2) {
    return {
      from: String(edge[0]),
      to: String(edge[1]),
    };
  }

  if (isPlainObject(edge)) {
    const from = edge.from ?? edge.src;
    const to = edge.to ?? edge.dst;

    if (from !== undefined && to !== undefined) {
      return {
        from: String(from),
        to: String(to),
      };
    }
  }

  return null;
}

function edgeKey0(edge) {
  if (Array.isArray(edge)) {
    return `${String(edge[0])}->${String(edge[1])}`;
  }

  return `${String(edge.from)}->${String(edge.to)}`;
}

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
}

function getPiMatch0(match) {
  return match.PiMatch ?? match['Πmatch'] ?? match.piMatch;
}

function getPiSATDecision0(decision) {
  return decision.PiSATDecision ?? decision['Πsat'] ?? decision.piSATDecision;
}

function getPiSATBounds0(bounds) {
  return bounds.PiSATBounds ?? bounds['Πsatbounds'] ?? bounds.piSATBounds;
}

function getPiFinalIntegration0(integration) {
  return integration.PiFinalIntegration ?? integration['Πfinalint'] ?? integration.piFinalIntegration;
}

function makeAcceptRecord({
  checker,
  nf,
  ledger,
}) {
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

function makeRejectRecord({
  checker,
  coord,
  path,
  witness,
  ledger,
}) {
  const rejectNF = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };

  const digest = digestCanonical0(rejectNF);

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
  return {
    ok: true,
    nf,
  };
}

function validationReject0(path, reason, detail) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      detail,
    },
  };
}

function isRejectRecord0(value) {
  return classifyRecord0(value) === 'reject';
}

function classifyRecord0(value) {
  if (!isPlainObject(value)) {
    return 'unknown';
  }

  const raw =
    value.tag ??
    value.kind ??
    value.verdict ??
    value.status ??
    value.result ??
    value.outcome;

  if (typeof raw !== 'string') {
    return 'unknown';
  }

  const normalized = raw.trim().toLowerCase();

  if (
    normalized === 'accept' ||
    normalized === 'accepted' ||
    normalized === 'ok' ||
    normalized === 'pass' ||
    normalized === 'passed'
  ) {
    return 'accept';
  }

  if (
    normalized === 'reject' ||
    normalized === 'rejected' ||
    normalized === 'err' ||
    normalized === 'error' ||
    normalized === 'fail' ||
    normalized === 'failed'
  ) {
    return 'reject';
  }

  return 'unknown';
}

function compactReject0(value) {
  if (!isPlainObject(value)) {
    return value;
  }

  return {
    checker: value.checker ?? null,
    coord: value.Coord ?? value.coord ?? null,
    path: value.Path ?? value.path ?? null,
    witness: value.Witness ?? value.witness ?? null,
    digest: value.Digest ?? value.digest ?? null,
  };
}

function arrayContainsAll0(actual, required) {
  if (!Array.isArray(actual)) {
    return false;
  }

  return required.every((entry) => actual.includes(entry));
}

function isNonEmptyString(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}
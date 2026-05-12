import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;

export const GPACK_REQUIRED_FIELDS0 = Object.freeze([
  'SchedHash',
  'IfaceHash',
  'PreNAND',
  'SlotAlloc',
  'SepCert',
  'CohCert',
  'MacroTables',
  'PrefixCert',
  'BaselineCert',
  'TraceCert',
  'ThresholdCert',
  'BoundsCert',
  'NoMinCert',
]);

export const GPACK_SLOT_FAMILIES0 = Object.freeze([
  'X',
  'T',
  'O',
  'R',
  'L',
  'z',
]);

export const GPACK_FORBIDDEN_EXEC_SYMBOLS0 = Object.freeze([
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

export const GPACK_NOMIN_EXPANSION_STAGES0 = Object.freeze([
  'macros',
  'aliases',
  'generatedTemplates',
  'imports',
]);

export const GPACK_ROWFAMG_REQUIRED_ROWS0 = Object.freeze([
  'PreNAND',
  'SlotAlloc',
  'SepCert',
  'CohCert',
  'MacroTables',
  'PrefixCert',
  'BaselineCert',
  'TraceCert',
  'ThresholdCert',
  'BoundsCert',
  'NoMinCert',
]);

export const LOCKED_NAND_MACRO_SIGNATURES0 = Object.freeze({
  Equality10: Object.freeze({
    kind: 'LockedNANDMacro0',
    name: 'M=',
    inputs: Object.freeze(['r', 'u', 's']),
    gateCount: 10,
    distinguished: 'a8',
    outputs: Object.freeze({
      a1: '11111100',
      a2: '11111010',
      a3: '00000011',
      a4: '11111110',
      a5: '11110011',
      a6: '00001100',
      a7: '11110111',
      a8: '00001001',
      a9: '11110000',
      a10: '11001111',
    }),
    projections: Object.freeze({
      r: '00001111',
      u: '00110011',
      s: '01010101',
    }),
  }),

  ConstOne2: Object.freeze({
    kind: 'LockedNANDMacro0',
    name: 'M1',
    inputs: Object.freeze(['r', 'u']),
    gateCount: 2,
    distinguished: 'b2',
    outputs: Object.freeze({
      b1: '1110',
      b2: '0001',
    }),
    projections: Object.freeze({
      r: '0011',
      u: '0101',
    }),
  }),

  ConstZero3: Object.freeze({
    kind: 'LockedNANDMacro0',
    name: 'M0',
    inputs: Object.freeze(['r', 'u']),
    gateCount: 3,
    distinguished: 'd3',
    outputs: Object.freeze({
      d1: '1110',
      d2: '1101',
      d3: '0010',
    }),
    projections: Object.freeze({
      r: '0011',
      u: '0101',
    }),
  }),

  NANDTrace18: Object.freeze({
    kind: 'LockedNANDMacro0',
    name: 'MN',
    inputs: Object.freeze(['ell', 't', 'u', 'v']),
    gateCount: 18,
    distinguished: 'q16',
    outputs: Object.freeze({
      q1: '1111111111110000',
      q2: '0000000000001111',
      q3: '1111111111001100',
      q4: '1111111110101010',
      q5: '1111111111110011',
      q6: '1111111111111100',
      q7: '0000000000000011',
      q8: '1111111111111101',
      q9: '1111111100001111',
      q10: '0000000011110000',
      q11: '1111111111001111',
      q12: '0000000000110000',
      q13: '1111111111101111',
      q14: '0000000000001110',
      q15: '1111111111110001',
      q16: '0000000000011110',
      q17: '1111111100000000',
      q18: '1111000011111111',
    }),
    projections: Object.freeze({
      ell: '0000000011111111',
      t: '0000111100001111',
      u: '0011001100110011',
      v: '0101010101010101',
    }),
  }),

  Prefix2: Object.freeze({
    kind: 'LockedNANDMacro0',
    name: 'Prefix2',
    inputs: Object.freeze(['a', 'b']),
    gateCount: 2,
    distinguished: 'p',
    exact: true,
    exposes: Object.freeze(['p', 'notP']),
  }),

  Final4: Object.freeze({
    kind: 'LockedNANDMacro0',
    name: 'Final4',
    inputs: Object.freeze(['z', 'Tphi', 'yout']),
    gateCount: 4,
    distinguished: 'Fphi',
    exact: true,
    exposesOnlyFinal: true,
  }),
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

export function makeLockedNANDMacroTables0(overrides = {}) {
  return {
    kind: 'LockedNANDMacroTables0',
    version: CHECKER_VERSION,
    macros: deepClone0(LOCKED_NAND_MACRO_SIGNATURES0),
    ...overrides,
  };
}

export function computeLockedNANDBaseline0({
  gateCount,
  equalityOccurrences,
  constZeroOccurrences,
  constOneOccurrences,
}) {
  if (!Number.isInteger(gateCount) || gateCount < 1) {
    throw new TypeError('computeLockedNANDBaseline0 requires a positive gateCount');
  }

  for (const [name, value] of Object.entries({
    equalityOccurrences,
    constZeroOccurrences,
    constOneOccurrences,
  })) {
    if (!Number.isInteger(value) || value < 0) {
      throw new TypeError(`computeLockedNANDBaseline0 requires non-negative ${name}`);
    }
  }

  return (
    18 * gateCount +
    10 * equalityOccurrences +
    3 * constZeroOccurrences +
    2 * constOneOccurrences +
    2 * (3 * gateCount - 1)
  );
}

export function makeSyntheticPreNAND0(overrides = {}) {
  return {
    kind: 'PreNAND0',
    version: CHECKER_VERSION,
    inputs: [
      'x0',
      'x1',
      'x2',
    ],
    gates: [
      {
        id: 'g0',
        op: 'NAND',
        sources: [
          'x0',
          'x1',
        ],
      },
      {
        id: 'g1',
        op: 'NAND',
        sources: [
          'g0',
          'x2',
        ],
      },
    ],
    output: 'g1',
    sourceOccurrences: {
      equality: 4,
      const0: 1,
      const1: 1,
    },
    formulaDigest: {
      alg: 'SHA256',
      hex: '6ea78bc9abbdfe1681af7024ad75ade93c7768d58ce81e0496250517010f0ae6',
    },
    ...overrides,
  };
}

export function makeSyntheticSlotAlloc0(preNAND = makeSyntheticPreNAND0(), overrides = {}) {
  const sourceCounts = getSourceCounts0(preNAND);
  const occurrenceCount =
    sourceCounts.equalityOccurrences +
    sourceCounts.constZeroOccurrences +
    sourceCounts.constOneOccurrences;

  return {
    kind: 'LockedNANDSlotAlloc0',
    version: CHECKER_VERSION,
    families: {
      X: preNAND.inputs.map((input) => `X.${input}`),
      T: preNAND.gates.map((gate) => `T.${gate.id}`),
      O: Array.from({ length: occurrenceCount }, (_, index) => `O.${index}`),
      R: Array.from({ length: occurrenceCount }, (_, index) => `R.${index}`),
      L: preNAND.gates.map((gate) => `L.${gate.id}`),
      z: [
        'z.final',
      ],
    },
    finalLock: 'z.final',
    macroInputsDistinct: true,
    occurrenceSlotsFresh: true,
    prefixLocksDistinct: true,
    ...overrides,
  };
}

export function makeSyntheticGPack0(overrides = {}) {
  const preNAND = makeSyntheticPreNAND0();
  const baseline = computeBaselineFromPreNAND0(preNAND);

  const gpack = {
    kind: 'GPack0',
    version: CHECKER_VERSION,

    SchedHash: {
      alg: 'SHA256',
      hex: 'f5c44e65ea7bd052ef9ea3bf0a542fbae487d604feb21f12b0bee486587bc261',
    },

    IfaceHash: {
      alg: 'SHA256',
      hex: 'e6f16343329a1df64f53903d9ba83a07df3f32cab92baa0996c6e291afdec009',
    },

    PreNAND: preNAND,
    SlotAlloc: makeSyntheticSlotAlloc0(preNAND),

    SepCert: {
      kind: 'GSepCert0',
      version: CHECKER_VERSION,
      pairwiseDistinct: true,
      macroInputsDistinct: true,
      occurrenceSlotsFresh: true,
      macroLocksFresh: true,
      finalLockOnlyFinal: true,
      prefixLocksDistinct: true,
      noCarrierConstants: true,
    },

    CohCert: {
      kind: 'GCohCert0',
      version: CHECKER_VERSION,
      allChecksOne: true,
      witness: {
        assignment: 'synthetic-all-distinguished-checks-one',
      },
    },

    MacroTables: makeLockedNANDMacroTables0(),

    PrefixCert: {
      kind: 'PrefixCert0',
      version: CHECKER_VERSION,
      exact: true,
      prefixConjunctionGates: 2 * (3 * preNAND.gates.length - 1),
      exposesNegations: true,
      finalOutputGates: 4,
      finalLockOnlyFinal: true,
      exposesOnlyFinal: true,
    },

    BaselineCert: {
      kind: 'BaselineCert0',
      version: CHECKER_VERSION,
      gateCount: preNAND.gates.length,
      equalityOccurrences: preNAND.sourceOccurrences.equality,
      constZeroOccurrences: preNAND.sourceOccurrences.const0,
      constOneOccurrences: preNAND.sourceOccurrences.const1,
      baseline,
      functionsCount: baseline,
      distinctNonconstantNonprojection: true,
      lowerBound: true,
      directWireOutputLowerBound: true,
      macroTruthSignaturesPairwiseDistinct: true,
      macroOutputsNonconstant: true,
      macroOutputsNonprojection: true,
      carrierTaggedCrossInstanceDistinct: true,
      prefixOutputsSeparatedFromMacros: true,
      duplicateSourceOccurrenceSlotsFresh: true,
      projectionModelPositiveBoundaryOnly: true,
      derivation: makeBaselineDerivation0(preNAND, baseline),
    },

    TraceCert: {
      kind: 'TraceCert0',
      version: CHECKER_VERSION,
      traceCoherent: true,
      traceEquivalence: true,
      lockActivationRequired: true,
      equalityLocksForceEquality: true,
      constantLocksForceValues: true,
      nandTraceLocksForceGateEquations: true,
      prefixCoversAllDistinguishedChecks: true,
      topologicalTraceInduction: true,
      outputSlotIsCircuitOutput: true,
      duplicateSourceOccurrencesFresh: true,
      gateTraceCount: preNAND.gates.length,
      allTraceMacrosAccepted: true,
      sourceOccurrenceCount:
        preNAND.sourceOccurrences.equality +
        preNAND.sourceOccurrences.const0 +
        preNAND.sourceOccurrences.const1,
      derivation: makeTraceDerivation0(preNAND),
    },

    ThresholdCert: {
      kind: 'ThresholdCert0',
      version: CHECKER_VERSION,
      lockedThreshold: true,
      baseline,
      fullWordSize: baseline + 4,
      residualSlackMax: 4,
      satIffMinAboveBaseline: true,
      unsatMinEqualsBaseline: true,
      zeroOutputConvention: true,
      finalLockSeparation: true,
      derivation: makeThresholdDerivation0(preNAND, baseline),
    },

    BoundsCert: {
      kind: 'GBoundsCert0',
      version: CHECKER_VERSION,
      finite: true,
      polynomial: true,
      constructionPolynomial: true,
      residualSlackMax: 4,
      noPrivateSchedule: true,
    },

    NoMinCert: {
      kind: 'GNoMinCert0',
      version: CHECKER_VERSION,
      expansionStages: GPACK_NOMIN_EXPANSION_STAGES0,
      forbiddenSymbols: GPACK_FORBIDDEN_EXEC_SYMBOLS0,
      occurrences: [
        {
          identifier: 'minimumEquivalent',
          expandedIdentifier: 'µ*',
          occurrenceClass: 'AssumeOnly',
          source: 'threshold theorem statement',
        },
      ],
      importsScanned: true,
      macrosExpanded: true,
      aliasesExpanded: true,
      generatedTemplatesExpanded: true,
      expandedArtifacts: [],
    },

    PiG: {
      kind: 'PiG0',
      version: CHECKER_VERSION,
      proofOrder: [
        'G.BaselineCert.proof',
        'G.TraceCert.proof',
        'G.ThresholdCert.proof',
      ],
      proofNodes: makeGProofNodes0(preNAND, baseline),
      note: 'synthetic locked NAND proof marker',
    },
  };

  return {
    ...gpack,
    ...overrides,
  };
}

export function makeSyntheticRowFamG0(gpack = makeSyntheticGPack0(), overrides = {}) {
  return {
    kind: 'RowFamG0',
    version: CHECKER_VERSION,
    GPack: gpack,
    rows: GPACK_ROWFAMG_REQUIRED_ROWS0.map((rowKind, index) => ({
      kind: 'RowFamGEntry0',
      version: CHECKER_VERSION,
      rowId: `G.${rowKind}`,
      rowKind,
      family: 'G',
      packageId: 'PG',
      selectedRoute: 'Accept',
      activeRouteSet: [
        'Accept',
      ],
      candidateRoutes: [
        'Accept',
      ],
      proofRef: {
        kind: 'ProofRef0',
        refKind: 'KPrimitive',
        id: `G.${rowKind}.proof`,
      },
      boundsRef: {
        kind: 'BoundsRef0',
        id: `G.${rowKind}.bounds`,
        polynomial: true,
        finite: true,
      },
      index,
    })),
    Coverage: {
      kind: 'RowFamGCoverage0',
      requiredRows: GPACK_ROWFAMG_REQUIRED_ROWS0,
    },
    PiRowFamG: {
      kind: 'PiRowFamG0',
      version: CHECKER_VERSION,
      note: 'synthetic RowFamG proof marker',
    },
    ...overrides,
  };
}

export async function CheckGPack0(gpack) {
  const checker = 'CheckGPack0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateGPackShape0(gpack)],
    ['preNAND', `${checker}.preNAND`, () => validatePreNAND0(gpack.PreNAND)],
    ['slotAlloc', `${checker}.slotAlloc`, () => validateSlotAllocation0(gpack.SlotAlloc)],
    ['sep', `${checker}.sep`, () => validateSepCert0(gpack)],
    ['coh', `${checker}.coh`, () => validateCohCert0(gpack.CohCert)],
    ['macroTables', `${checker}.macroTables`, () => validateMacroTables0(gpack.MacroTables)],
    ['prefix', `${checker}.prefix`, () => validatePrefixCert0(gpack)],
    ['baseline', `${checker}.baseline`, () => validateBaselineCertHardened0(gpack)],
    ['trace', `${checker}.trace`, () => validateTraceCertHardened0(gpack)],
    ['threshold', `${checker}.threshold`, () => validateThresholdCertHardened0(gpack)],
    ['derivationProofNodes', `${checker}.derivationProofNodes`, () => validateGDerivationProofNodes0(gpack)],
    ['bounds', `${checker}.bounds`, () => validateBoundsCert0(gpack.BoundsCert)],
    ['noHiddenMinMetadata', `${checker}.noHiddenMinMetadata`, () => validateNoMinCert0(gpack.NoMinCert)],
    ['noHiddenMin', `${checker}.noHiddenMin`, () => validateNoHiddenExecutableMin0(gpack, ['GPack0'])],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(gpack, ['GPack0'])],
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

  const baseline = computeBaselineFromPreNAND0(gpack.PreNAND);

  const nf = {
    kind: 'GPack0NF',
    checker,
    version: CHECKER_VERSION,
    gateCount: gpack.PreNAND.gates.length,
    baseline,
    fullWordSize: baseline + 4,
    residualSlackMax: gpack.ThresholdCert.residualSlackMax,
    macroCount: Object.keys(LOCKED_NAND_MACRO_SIGNATURES0).length,
    slotFamilyCount: GPACK_SLOT_FAMILIES0.length,
    piGDigest: digestCanonical0(getPiG0(gpack)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckRowFamG0(rowFam) {
  const checker = 'CheckRowFamG0';
  const ledger = [];

  const shape = validateRowFamGShape0(rowFam);

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

  const gpackRecord = await CheckGPack0(rowFam.GPack);
  const gpackResult = recordToValidation0(gpackRecord, ['GPack']);

  ledger.push({
    phase: 'CheckGPack0',
    status: gpackResult.ok ? 'pass' : 'fail',
    digest: gpackRecord.Digest ?? gpackRecord.digest ?? digestCanonical0(gpackRecord),
  });

  if (!gpackResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.GPack`,
      path: gpackResult.path,
      witness: gpackResult.witness,
      ledger,
    });
  }

  const coverage = validateRowFamGCoverage0(rowFam);

  ledger.push({
    phase: 'coverage',
    status: coverage.ok ? 'pass' : 'fail',
    digest: digestCanonical0(coverage.nf ?? coverage.witness ?? null),
  });

  if (!coverage.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.coverage`,
      path: coverage.path,
      witness: coverage.witness,
      ledger,
    });
  }

  const rows = validateRowFamGRows0(rowFam);

  ledger.push({
    phase: 'rows',
    status: rows.ok ? 'pass' : 'fail',
    digest: digestCanonical0(rows.nf ?? rows.witness ?? null),
  });

  if (!rows.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.rows`,
      path: rows.path,
      witness: rows.witness,
      ledger,
    });
  }

  const derivationProofRefs = validateRowFamGDerivationProofRefs0(rowFam);

  ledger.push({
    phase: 'derivationProofRefs',
    status: derivationProofRefs.ok ? 'pass' : 'fail',
    digest: digestCanonical0(derivationProofRefs.nf ?? derivationProofRefs.witness ?? null),
  });

  if (!derivationProofRefs.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.derivationProofRefs`,
      path: derivationProofRefs.path,
      witness: derivationProofRefs.witness,
      ledger,
    });
  }

  const noHiddenMin = validateNoHiddenExecutableMin0(rowFam, ['RowFamG0']);

  ledger.push({
    phase: 'noHiddenMin',
    status: noHiddenMin.ok ? 'pass' : 'fail',
    digest: digestCanonical0(noHiddenMin.nf ?? noHiddenMin.witness ?? null),
  });

  if (!noHiddenMin.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.noHiddenMin`,
      path: noHiddenMin.path,
      witness: noHiddenMin.witness,
      ledger,
    });
  }

  const noOpaque = validateNoOpaqueProof0(rowFam, ['RowFamG0']);

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
    kind: 'RowFamG0NF',
    checker,
    version: CHECKER_VERSION,
    rowCount: rowFam.rows.length,
    requiredRows: GPACK_ROWFAMG_REQUIRED_ROWS0,
    gpackDigest: gpackRecord.Digest,
    piRowFamGDigest: digestCanonical0(getPiRowFamG0(rowFam)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateGPackShape0(gpack) {
  if (!isPlainObject(gpack)) {
    return validationReject0([], 'GPack0 must be an object', {
      actual: typeof gpack,
    });
  }

  if (gpack.kind !== undefined && gpack.kind !== 'GPack0') {
    return validationReject0(['kind'], 'GPack0 kind must be GPack0 when present', {
      actual: gpack.kind,
    });
  }

  if (gpack.version !== undefined && gpack.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `GPack0 version must be ${CHECKER_VERSION} when present`, {
      actual: gpack.version,
    });
  }

  for (const field of GPACK_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(gpack, field)) {
      return validationReject0([field], 'GPack0 is missing a required field', {
        field,
      });
    }
  }

  if (getPiG0(gpack) === undefined) {
    return validationReject0(['PiG'], 'GPack0 is missing PiG or ΠG', null);
  }

  return validationAccept0({
    kind: 'GPackShape0NF',
  });
}

function validatePreNAND0(preNAND) {
  if (!isPlainObject(preNAND)) {
    return validationReject0(['PreNAND'], 'PreNAND0 must be an object', {
      actual: typeof preNAND,
    });
  }

  if (preNAND.kind !== undefined && preNAND.kind !== 'PreNAND0') {
    return validationReject0(['PreNAND', 'kind'], 'PreNAND0 kind must be PreNAND0 when present', {
      actual: preNAND.kind,
    });
  }

  if (!Array.isArray(preNAND.inputs) || preNAND.inputs.length === 0) {
    return validationReject0(['PreNAND', 'inputs'], 'PreNAND0 inputs must be a non-empty array', {
      actual: preNAND.inputs,
    });
  }

  if (!Array.isArray(preNAND.gates) || preNAND.gates.length === 0) {
    return validationReject0(['PreNAND', 'gates'], 'PreNAND0 gates must be a non-empty array', {
      actual: preNAND.gates,
    });
  }

  const knownSources = new Set(preNAND.inputs);

  for (let index = 0; index < preNAND.gates.length; index += 1) {
    const gate = preNAND.gates[index];

    if (!isPlainObject(gate)) {
      return validationReject0(['PreNAND', 'gates', index], 'PreNAND0 gate must be an object', {
        actual: typeof gate,
      });
    }

    if (!isNonEmptyString(gate.id)) {
      return validationReject0(['PreNAND', 'gates', index, 'id'], 'PreNAND0 gate must have a non-empty id', {
        actual: gate.id,
      });
    }

    if (knownSources.has(gate.id)) {
      return validationReject0(['PreNAND', 'gates', index, 'id'], 'PreNAND0 gate ids must be unique and distinct from inputs', {
        id: gate.id,
      });
    }

    if (gate.op !== 'NAND') {
      return validationReject0(['PreNAND', 'gates', index, 'op'], 'PreNAND0 gates must be NAND gates', {
        actual: gate.op,
      });
    }

    if (!Array.isArray(gate.sources) || gate.sources.length !== 2) {
      return validationReject0(['PreNAND', 'gates', index, 'sources'], 'PreNAND0 NAND gates must have exactly two sources', {
        actual: gate.sources,
      });
    }

    for (let sourceIndex = 0; sourceIndex < gate.sources.length; sourceIndex += 1) {
      const source = gate.sources[sourceIndex];

      if (source === 0 || source === 1 || source === '0' || source === '1') {
        return validationReject0(['PreNAND', 'gates', index, 'sources', sourceIndex], 'PreNAND0 may not use carrier constants directly', {
          source,
        });
      }

      if (!knownSources.has(source)) {
        return validationReject0(['PreNAND', 'gates', index, 'sources', sourceIndex], 'PreNAND0 gate source must be an input or earlier gate', {
          source,
        });
      }
    }

    knownSources.add(gate.id);
  }

  if (!knownSources.has(preNAND.output)) {
    return validationReject0(['PreNAND', 'output'], 'PreNAND0 output must name an input or gate', {
      output: preNAND.output,
    });
  }

  const counts = getSourceCounts0(preNAND);

  for (const [field, value] of Object.entries(counts)) {
    if (!Number.isInteger(value) || value < 0) {
      return validationReject0(['PreNAND', 'sourceOccurrences', field], 'PreNAND0 source occurrence counts must be non-negative integers', {
        field,
        actual: value,
      });
    }
  }

  return validationAccept0({
    kind: 'PreNAND0NF',
    gateCount: preNAND.gates.length,
    sourceCounts: counts,
  });
}

function validateSlotAllocation0(slotAlloc) {
  if (!isPlainObject(slotAlloc)) {
    return validationReject0(['SlotAlloc'], 'SlotAlloc must be an object', {
      actual: typeof slotAlloc,
    });
  }

  if (!isPlainObject(slotAlloc.families)) {
    return validationReject0(['SlotAlloc', 'families'], 'SlotAlloc families must be an object', {
      actual: typeof slotAlloc.families,
    });
  }

  const seen = new Map();

  for (const family of GPACK_SLOT_FAMILIES0) {
    const slots = slotAlloc.families[family];

    if (!Array.isArray(slots)) {
      return validationReject0(['SlotAlloc', 'families', family], 'SlotAlloc family must be an array', {
        family,
        actual: typeof slots,
      });
    }

    if (family === 'z' && slots.length !== 1) {
      return validationReject0(['SlotAlloc', 'families', family], 'SlotAlloc z family must contain exactly one final lock', {
        actual: slots.length,
      });
    }

    for (let index = 0; index < slots.length; index += 1) {
      const slot = slots[index];

      if (!isNonEmptyString(slot)) {
        return validationReject0(['SlotAlloc', 'families', family, index], 'SlotAlloc slot must be a non-empty string', {
          slot,
        });
      }

      if (seen.has(slot)) {
        return validationReject0(['SlotAlloc', 'families', family, index], 'SlotAlloc slots must be globally unique', {
          slot,
          previous: seen.get(slot),
          current: {
            family,
            index,
          },
        });
      }

      seen.set(slot, {
        family,
        index,
      });
    }
  }

  const finalLock = slotAlloc.finalLock ?? slotAlloc.families.z[0];

  if (finalLock !== slotAlloc.families.z[0]) {
    return validationReject0(['SlotAlloc', 'finalLock'], 'SlotAlloc finalLock must be the sole z slot', {
      expected: slotAlloc.families.z[0],
      actual: finalLock,
    });
  }

  return validationAccept0({
    kind: 'SlotAlloc0NF',
    slotCount: seen.size,
    finalLock,
  });
}

function validateSepCert0(gpack) {
  const cert = gpack.SepCert;

  if (!isPlainObject(cert)) {
    return validationReject0(['SepCert'], 'SepCert must be an object', {
      actual: typeof cert,
    });
  }

  for (const field of [
    'pairwiseDistinct',
    'macroInputsDistinct',
    'occurrenceSlotsFresh',
    'macroLocksFresh',
    'finalLockOnlyFinal',
    'prefixLocksDistinct',
    'noCarrierConstants',
  ]) {
    if (cert[field] !== true) {
      return validationReject0(['SepCert', field], `SepCert must certify ${field}`, {
        actual: cert[field],
      });
    }
  }

  return validationAccept0({
    kind: 'GSepCert0NF',
  });
}

function validateCohCert0(cert) {
  if (!isPlainObject(cert)) {
    return validationReject0(['CohCert'], 'CohCert must be an object', {
      actual: typeof cert,
    });
  }

  if (cert.allChecksOne !== true) {
    return validationReject0(['CohCert', 'allChecksOne'], 'CohCert must assign all distinguished checks the value one', {
      actual: cert.allChecksOne,
    });
  }

  if (cert.witness === undefined) {
    return validationReject0(['CohCert', 'witness'], 'CohCert must carry a coherence witness', null);
  }

  return validationAccept0({
    kind: 'GCohCert0NF',
  });
}

function validateMacroTables0(macroTables) {
  if (!isPlainObject(macroTables)) {
    return validationReject0(['MacroTables'], 'MacroTables must be an object', {
      actual: typeof macroTables,
    });
  }

  const actualMacros = macroTables.macros ?? macroTables;

  if (!isPlainObject(actualMacros)) {
    return validationReject0(['MacroTables', 'macros'], 'MacroTables macros must be an object', {
      actual: typeof actualMacros,
    });
  }

  for (const [macroId, expected] of Object.entries(LOCKED_NAND_MACRO_SIGNATURES0)) {
    const actual = actualMacros[macroId] ?? actualMacros[expected.name];

    if (!isPlainObject(actual)) {
      return validationReject0(['MacroTables', 'macros', macroId], 'MacroTables is missing a required locked NAND macro', {
        macroId,
      });
    }

    if (actual.gateCount !== expected.gateCount) {
      return validationReject0(['MacroTables', 'macros', macroId, 'gateCount'], 'locked NAND macro gate count mismatch', {
        macroId,
        expected: expected.gateCount,
        actual: actual.gateCount,
      });
    }

    if (expected.outputs !== undefined) {
      if (!isPlainObject(actual.outputs)) {
        return validationReject0(['MacroTables', 'macros', macroId, 'outputs'], 'locked NAND macro outputs must be an object', {
          macroId,
        });
      }

      const expectedLength = 2 ** expected.inputs.length;
      const seenSignatures = new Map();
      const projections = new Set(Object.values(expected.projections ?? {}));

      for (const [outputName, expectedSignature] of Object.entries(expected.outputs)) {
        const actualSignature = actual.outputs[outputName];

        if (actualSignature !== expectedSignature) {
          return validationReject0(['MacroTables', 'macros', macroId, 'outputs', outputName], 'locked NAND macro truth signature mismatch', {
            macroId,
            outputName,
            expected: expectedSignature,
            actual: actualSignature,
          });
        }

        if (!/^[01]+$/.test(actualSignature) || actualSignature.length !== expectedLength) {
          return validationReject0(['MacroTables', 'macros', macroId, 'outputs', outputName], 'locked NAND macro truth signature has invalid shape', {
            macroId,
            outputName,
            actual: actualSignature,
            expectedLength,
          });
        }

        if (/^0+$/.test(actualSignature) || /^1+$/.test(actualSignature)) {
          return validationReject0(['MacroTables', 'macros', macroId, 'outputs', outputName], 'locked NAND macro output must be nonconstant', {
            macroId,
            outputName,
            actual: actualSignature,
          });
        }

        if (projections.has(actualSignature)) {
          return validationReject0(['MacroTables', 'macros', macroId, 'outputs', outputName], 'locked NAND macro output must be nonprojection', {
            macroId,
            outputName,
            actual: actualSignature,
          });
        }

        if (seenSignatures.has(actualSignature)) {
          return validationReject0(['MacroTables', 'macros', macroId, 'outputs', outputName], 'locked NAND macro outputs must be pairwise distinct within a macro', {
            macroId,
            outputName,
            previous: seenSignatures.get(actualSignature),
          });
        }

        seenSignatures.set(actualSignature, outputName);
      }

      if (actual.outputs[expected.distinguished] === undefined) {
        return validationReject0(['MacroTables', 'macros', macroId, 'distinguished'], 'locked NAND macro distinguished output is missing', {
          macroId,
          distinguished: expected.distinguished,
        });
      }
    }

    if (expected.exact === true && actual.exact !== true) {
      return validationReject0(['MacroTables', 'macros', macroId, 'exact'], 'locked NAND macro exactness certificate is missing', {
        macroId,
      });
    }
  }

  return validationAccept0({
    kind: 'MacroTables0NF',
    macroCount: Object.keys(LOCKED_NAND_MACRO_SIGNATURES0).length,
  });
}

function validatePrefixCert0(gpack) {
  const cert = gpack.PrefixCert;
  const m = gpack.PreNAND.gates.length;

  if (!isPlainObject(cert)) {
    return validationReject0(['PrefixCert'], 'PrefixCert must be an object', {
      actual: typeof cert,
    });
  }

  if (cert.exact !== true) {
    return validationReject0(['PrefixCert', 'exact'], 'PrefixCert must certify prefix exactness', {
      actual: cert.exact,
    });
  }

  const expectedPrefixGates = 2 * (3 * m - 1);

  if (cert.prefixConjunctionGates !== expectedPrefixGates) {
    return validationReject0(['PrefixCert', 'prefixConjunctionGates'], 'PrefixCert prefix gate count mismatch', {
      expected: expectedPrefixGates,
      actual: cert.prefixConjunctionGates,
    });
  }

  if (cert.finalOutputGates !== 4) {
    return validationReject0(['PrefixCert', 'finalOutputGates'], 'PrefixCert final output must use four gates', {
      expected: 4,
      actual: cert.finalOutputGates,
    });
  }

  if (cert.finalLockOnlyFinal !== true) {
    return validationReject0(['PrefixCert', 'finalLockOnlyFinal'], 'PrefixCert must certify final lock appears only in final output construction', {
      actual: cert.finalLockOnlyFinal,
    });
  }

  if (cert.exposesOnlyFinal !== true) {
    return validationReject0(['PrefixCert', 'exposesOnlyFinal'], 'PrefixCert must expose only the final locked output', {
      actual: cert.exposesOnlyFinal,
    });
  }

  return validationAccept0({
    kind: 'PrefixCert0NF',
    prefixConjunctionGates: cert.prefixConjunctionGates,
    finalOutputGates: cert.finalOutputGates,
  });
}

function validateBaselineCert0(gpack) {
  const cert = gpack.BaselineCert;

  if (!isPlainObject(cert)) {
    return validationReject0(['BaselineCert'], 'BaselineCert must be an object', {
      actual: typeof cert,
    });
  }

  const expected = computeBaselineFromPreNAND0(gpack.PreNAND);

  if (cert.baseline !== expected) {
    return validationReject0(['BaselineCert', 'baseline'], 'BaselineCert baseline mismatch', {
      expected,
      actual: cert.baseline,
    });
  }

  if (cert.functionsCount !== expected) {
    return validationReject0(['BaselineCert', 'functionsCount'], 'BaselineCert function count mismatch', {
      expected,
      actual: cert.functionsCount,
    });
  }

  if (cert.distinctNonconstantNonprojection !== true) {
    return validationReject0(['BaselineCert', 'distinctNonconstantNonprojection'], 'BaselineCert must certify distinct nonconstant nonprojection functions', {
      actual: cert.distinctNonconstantNonprojection,
    });
  }

  if (cert.lowerBound !== true) {
    return validationReject0(['BaselineCert', 'lowerBound'], 'BaselineCert must certify baseline lower bound', {
      actual: cert.lowerBound,
    });
  }

  return validationAccept0({
    kind: 'BaselineCert0NF',
    baseline: expected,
  });
}

function validateTraceCert0(gpack) {
  const cert = gpack.TraceCert;

  if (!isPlainObject(cert)) {
    return validationReject0(['TraceCert'], 'TraceCert must be an object', {
      actual: typeof cert,
    });
  }

  if (cert.traceCoherent !== true) {
    return validationReject0(['TraceCert', 'traceCoherent'], 'TraceCert must certify trace coherence', {
      actual: cert.traceCoherent,
    });
  }

  if (cert.gateTraceCount !== gpack.PreNAND.gates.length) {
    return validationReject0(['TraceCert', 'gateTraceCount'], 'TraceCert gate trace count mismatch', {
      expected: gpack.PreNAND.gates.length,
      actual: cert.gateTraceCount,
    });
  }

  if (cert.allTraceMacrosAccepted !== true) {
    return validationReject0(['TraceCert', 'allTraceMacrosAccepted'], 'TraceCert must certify every trace macro table accepts', {
      actual: cert.allTraceMacrosAccepted,
    });
  }

  return validationAccept0({
    kind: 'TraceCert0NF',
    gateTraceCount: cert.gateTraceCount,
  });
}

function validateThresholdCert0(gpack) {
  const cert = gpack.ThresholdCert;

  if (!isPlainObject(cert)) {
    return validationReject0(['ThresholdCert'], 'ThresholdCert must be an object', {
      actual: typeof cert,
    });
  }

  const expectedBaseline = computeBaselineFromPreNAND0(gpack.PreNAND);

  if (cert.lockedThreshold !== true) {
    return validationReject0(['ThresholdCert', 'lockedThreshold'], 'ThresholdCert must certify locked NAND threshold', {
      actual: cert.lockedThreshold,
    });
  }

  if (cert.baseline !== expectedBaseline) {
    return validationReject0(['ThresholdCert', 'baseline'], 'ThresholdCert baseline mismatch', {
      expected: expectedBaseline,
      actual: cert.baseline,
    });
  }

  if (cert.fullWordSize !== expectedBaseline + 4) {
    return validationReject0(['ThresholdCert', 'fullWordSize'], 'ThresholdCert full word size must be baseline plus four', {
      expected: expectedBaseline + 4,
      actual: cert.fullWordSize,
    });
  }

  if (!Number.isInteger(cert.residualSlackMax) || cert.residualSlackMax > 4 || cert.residualSlackMax < 0) {
    return validationReject0(['ThresholdCert', 'residualSlackMax'], 'ThresholdCert residual slack must be an integer at most four', {
      actual: cert.residualSlackMax,
    });
  }

  if (cert.satIffMinAboveBaseline !== true) {
    return validationReject0(['ThresholdCert', 'satIffMinAboveBaseline'], 'ThresholdCert must certify SAT iff minimum is above baseline', {
      actual: cert.satIffMinAboveBaseline,
    });
  }

  if (cert.unsatMinEqualsBaseline !== true) {
    return validationReject0(['ThresholdCert', 'unsatMinEqualsBaseline'], 'ThresholdCert must certify unsat minimum equals baseline', {
      actual: cert.unsatMinEqualsBaseline,
    });
  }

  return validationAccept0({
    kind: 'ThresholdCert0NF',
    baseline: expectedBaseline,
    fullWordSize: expectedBaseline + 4,
    residualSlackMax: cert.residualSlackMax,
  });
}

function validateBoundsCert0(cert) {
  if (!isPlainObject(cert)) {
    return validationReject0(['BoundsCert'], 'BoundsCert must be an object', {
      actual: typeof cert,
    });
  }

  for (const field of [
    'finite',
    'polynomial',
    'constructionPolynomial',
    'noPrivateSchedule',
  ]) {
    if (cert[field] !== true) {
      return validationReject0(['BoundsCert', field], `BoundsCert must certify ${field}`, {
        actual: cert[field],
      });
    }
  }

  if (!Number.isInteger(cert.residualSlackMax) || cert.residualSlackMax > 4 || cert.residualSlackMax < 0) {
    return validationReject0(['BoundsCert', 'residualSlackMax'], 'BoundsCert residual slack must be an integer at most four', {
      actual: cert.residualSlackMax,
    });
  }

  return validationAccept0({
    kind: 'GBoundsCert0NF',
    residualSlackMax: cert.residualSlackMax,
  });
}

function validateNoMinCert0(cert) {
  if (!isPlainObject(cert)) {
    return validationReject0(['NoMinCert'], 'NoMinCert must be an object', {
      actual: typeof cert,
    });
  }

  if (!arrayContainsAll0(cert.expansionStages, GPACK_NOMIN_EXPANSION_STAGES0)) {
    return validationReject0(['NoMinCert', 'expansionStages'], 'NoMinCert must expand macros, aliases, generated templates, and imports', {
      expected: GPACK_NOMIN_EXPANSION_STAGES0,
      actual: cert.expansionStages,
    });
  }

  if (!arrayContainsAll0(cert.forbiddenSymbols, GPACK_FORBIDDEN_EXEC_SYMBOLS0)) {
    return validationReject0(['NoMinCert', 'forbiddenSymbols'], 'NoMinCert is missing a forbidden executable symbol', {
      expected: GPACK_FORBIDDEN_EXEC_SYMBOLS0,
      actual: cert.forbiddenSymbols,
    });
  }

  for (const field of [
    'importsScanned',
    'macrosExpanded',
    'aliasesExpanded',
    'generatedTemplatesExpanded',
  ]) {
    if (cert[field] !== true) {
      return validationReject0(['NoMinCert', field], `NoMinCert must set ${field}`, {
        actual: cert[field],
      });
    }
  }

  if (!Array.isArray(cert.occurrences)) {
    return validationReject0(['NoMinCert', 'occurrences'], 'NoMinCert occurrences must be an array', {
      actual: typeof cert.occurrences,
    });
  }

  for (let index = 0; index < cert.occurrences.length; index += 1) {
    const occurrence = cert.occurrences[index];

    if (!isPlainObject(occurrence)) {
      return validationReject0(['NoMinCert', 'occurrences', index], 'NoMinCert occurrence must be an object', {
        actual: typeof occurrence,
      });
    }

    const identifier = occurrence.identifier;
    const expanded = occurrence.expandedIdentifier ?? identifier;

    if (
      occurrence.occurrenceClass === 'ExecCall' &&
      (
        GPACK_FORBIDDEN_EXEC_SYMBOLS0.includes(identifier) ||
        GPACK_FORBIDDEN_EXEC_SYMBOLS0.includes(expanded)
      )
    ) {
      return validationReject0(['NoMinCert', 'occurrences', index, 'identifier'], 'forbidden minimization symbol appears in executable position', {
        identifier,
        expandedIdentifier: expanded,
      });
    }
  }

  return validationAccept0({
    kind: 'GNoMinCert0NF',
    occurrenceCount: cert.occurrences.length,
  });
}

function validateNoHiddenExecutableMin0(value, path) {
  const hit = findForbiddenExecutableUse0(value, path, false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'GNoHiddenExecutableMin0NF',
  });
}

function validateNoOpaqueProof0(value, path) {
  const hit = findOpaqueProof0(value, path);

  if (hit !== null) {
    return validationReject0(hit.path, 'opaque proof material is not allowed in GPack0', hit);
  }

  return validationAccept0({
    kind: 'GNoOpaqueProof0NF',
  });
}

function validateRowFamGShape0(rowFam) {
  if (!isPlainObject(rowFam)) {
    return validationReject0([], 'RowFamG0 must be an object', {
      actual: typeof rowFam,
    });
  }

  if (rowFam.kind !== undefined && rowFam.kind !== 'RowFamG0') {
    return validationReject0(['kind'], 'RowFamG0 kind must be RowFamG0 when present', {
      actual: rowFam.kind,
    });
  }

  if (rowFam.version !== undefined && rowFam.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `RowFamG0 version must be ${CHECKER_VERSION} when present`, {
      actual: rowFam.version,
    });
  }

  if (!isPlainObject(rowFam.GPack)) {
    return validationReject0(['GPack'], 'RowFamG0 must include a GPack object', {
      actual: typeof rowFam.GPack,
    });
  }

  if (!Array.isArray(rowFam.rows)) {
    return validationReject0(['rows'], 'RowFamG0 rows must be an array', {
      actual: typeof rowFam.rows,
    });
  }

  if (getPiRowFamG0(rowFam) === undefined) {
    return validationReject0(['PiRowFamG'], 'RowFamG0 is missing PiRowFamG or ΠrowFamG', null);
  }

  return validationAccept0({
    kind: 'RowFamGShape0NF',
  });
}

function validateRowFamGCoverage0(rowFam) {
  const covered = new Set();

  for (const row of rowFam.rows) {
    if (isPlainObject(row) && isNonEmptyString(row.rowKind)) {
      covered.add(row.rowKind);
    }
  }

  for (const rowKind of GPACK_ROWFAMG_REQUIRED_ROWS0) {
    if (!covered.has(rowKind)) {
      return validationReject0(['rows', 'coverage', rowKind], 'RowFamG0 is missing a required locked NAND row', {
        rowKind,
      });
    }
  }

  return validationAccept0({
    kind: 'RowFamGCoverage0NF',
    rowCount: rowFam.rows.length,
  });
}

function validateRowFamGRows0(rowFam) {
  const seen = new Set();

  for (let index = 0; index < rowFam.rows.length; index += 1) {
    const row = rowFam.rows[index];

    if (!isPlainObject(row)) {
      return validationReject0(['rows', index], 'RowFamG0 row must be an object', {
        actual: typeof row,
      });
    }

    if (!isNonEmptyString(row.rowId)) {
      return validationReject0(['rows', index, 'rowId'], 'RowFamG0 row must have a rowId', {
        actual: row.rowId,
      });
    }

    if (seen.has(row.rowId)) {
      return validationReject0(['rows', index, 'rowId'], 'RowFamG0 row ids must be unique', {
        rowId: row.rowId,
      });
    }

    seen.add(row.rowId);

    if (row.family !== 'G') {
      return validationReject0(['rows', index, 'family'], 'RowFamG0 rows must belong to family G', {
        actual: row.family,
      });
    }

    if (row.selectedRoute !== 'Accept') {
      return validationReject0(['rows', index, 'selectedRoute'], 'RowFamG0 rows must select Accept', {
        actual: row.selectedRoute,
      });
    }

    if (!Array.isArray(row.activeRouteSet) || !row.activeRouteSet.includes(row.selectedRoute)) {
      return validationReject0(['rows', index, 'activeRouteSet'], 'RowFamG0 selected route must be active', {
        selectedRoute: row.selectedRoute,
        activeRouteSet: row.activeRouteSet,
      });
    }

    if (!isPlainObject(row.proofRef)) {
      return validationReject0(['rows', index, 'proofRef'], 'RowFamG0 row proofRef must be an object', {
        actual: typeof row.proofRef,
      });
    }

    if (!isPlainObject(row.boundsRef)) {
      return validationReject0(['rows', index, 'boundsRef'], 'RowFamG0 row boundsRef must be an object', {
        actual: typeof row.boundsRef,
      });
    }

    if (row.boundsRef.polynomial !== true || row.boundsRef.finite !== true) {
      return validationReject0(['rows', index, 'boundsRef'], 'RowFamG0 row bounds must be finite and polynomial', {
        boundsRef: row.boundsRef,
      });
    }
  }

  return validationAccept0({
    kind: 'RowFamGRows0NF',
    rowCount: rowFam.rows.length,
  });
}

function computeBaselineFromPreNAND0(preNAND) {
  const counts = getSourceCounts0(preNAND);

  return computeLockedNANDBaseline0({
    gateCount: preNAND.gates.length,
    ...counts,
  });
}

function getSourceCounts0(preNAND) {
  const sourceOccurrences = preNAND.sourceOccurrences ?? {};

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

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && GPACK_FORBIDDEN_EXEC_SYMBOLS0.includes(value)) {
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

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
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

function getPiG0(gpack) {
  return gpack.PiG ?? gpack['ΠG'] ?? gpack.piG;
}

function getPiRowFamG0(rowFam) {
  return rowFam.PiRowFamG ?? rowFam['ΠrowFamG'] ?? rowFam.piRowFamG;
}

function arrayContainsAll0(actual, required) {
  if (!Array.isArray(actual)) {
    return false;
  }

  return required.every((entry) => actual.includes(entry));
}

function deepClone0(value) {
  return JSON.parse(JSON.stringify(value));
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

// Hardened locked-NAND derivation checks.
// These validators keep the existing structural checks, then require explicit
// derivation records for the theorem-bearing BaselineCert, TraceCert, and
// ThresholdCert fields. The intent is to prevent CheckGPack0 from accepting
// bare theorem booleans without auditable derivation metadata.

function makeBaselineDerivation0(preNAND, baseline) {
  const counts = getSourceCounts0(preNAND);
  const gateCount = preNAND.gates.length;

  return {
    kind: 'BaselineDerivation0',
    version: CHECKER_VERSION,
    rule: 'BaselineDistinctDirectWire0',
    baseline,
    gateCount,
    equalityOccurrences: counts.equalityOccurrences,
    constZeroOccurrences: counts.constZeroOccurrences,
    constOneOccurrences: counts.constOneOccurrences,
    formula: '18m + 10wEq + 3w0 + 2w1 + 2(3m - 1)',
    components: {
      traceOutputs: 18 * gateCount,
      equalityOutputs: 10 * counts.equalityOccurrences,
      constZeroOutputs: 3 * counts.constZeroOccurrences,
      constOneOutputs: 2 * counts.constOneOccurrences,
      prefixOutputs: 2 * (3 * gateCount - 1),
    },
    totalFunctions: baseline,
    functionsCount: baseline,
    directWireOutputConvention: true,
    directWireOutputLowerBound: true,
    pairwiseDistinctNonconstantNonprojection: true,
    macroTruthSignaturesPairwiseDistinct: true,
    macroOutputsNonconstant: true,
    macroOutputsNonprojection: true,
    carrierTaggedCrossInstanceDistinct: true,
    prefixOutputsSeparatedFromMacros: true,
    duplicateSourceOccurrenceSlotsFresh: true,
    projectionModelPositiveBoundaryOnly: true,
    privateLocksFresh: true,
    macroSignaturesChecked: true,
    crossMacroSharingForbiddenBySep: true,
    lowerBoundRuleApplied: true,
    gateOutputInjection: 'distinct-noninput-outputs-map-to-distinct-NAND-gates',
    constructedBaselineExact: true,
    proofRef: makeGProofRef0('BaselineCert'),
  };
}

function makeTraceDerivation0(preNAND) {
  const counts = getSourceCounts0(preNAND);
  const gateTraceCount = preNAND.gates.length;
  const sourceOccurrenceCount =
    counts.equalityOccurrences +
    counts.constZeroOccurrences +
    counts.constOneOccurrences;

  return {
    kind: 'TraceDerivation0',
    version: CHECKER_VERSION,
    rule: 'NANDTraceCoherence0',
    gateTraceCount,
    sourceOccurrenceCount,
    equalityOccurrences: counts.equalityOccurrences,
    constZeroOccurrences: counts.constZeroOccurrences,
    constOneOccurrences: counts.constOneOccurrences,
    traceMacroName: 'MN',
    distinguishedOutput: 'q16',
    traceEquivalence:
      'all distinguished checks one iff trace slots encode a valid NAND evaluation',
    topologicalInduction: true,
    topologicalTraceInduction: true,
    lockActivationRequired: true,
    equalityLocksForceEquality: true,
    constantLocksForceValues: true,
    nandTraceLocksForceGateEquations: true,
    prefixCoversAllDistinguishedChecks: true,
    outputSlotIsCircuitOutput: true,
    duplicateSourceOccurrencesFresh: true,
    sourceOccurrencesFresh: true,
    constantsThroughMacros: true,
    noCarrierConstants: true,
    traceCoherent: true,
    allTraceMacrosAccepted: true,
    proofRef: makeGProofRef0('TraceCert'),
  };
}

function makeThresholdDerivation0(preNAND, baseline) {
  return {
    kind: 'ThresholdDerivation0',
    version: CHECKER_VERSION,
    rule: 'LockedNANDThreshold0',
    baseline,
    fullWordSize: baseline + 4,
    residualSlackMax: 4,
    lockedThreshold: true,
    satIffMinAboveBaseline: true,
    unsatMinEqualsBaseline: true,
    zeroOutputConvention: true,
    finalLockSeparation: true,
    satUpperBoundExtraGates: 4,
    satLowerBoundExtraGates: 1,
    finalOutputGates: 4,
    finalOutput: 'Fphi = z && Tphi && yout',
    finalLockOnlyFinal: true,
    exposesOnlyFinal: true,
    baselineDerivation: 'BaselineDerivation0',
    traceDerivation: 'TraceDerivation0',
    noHiddenMinimization: true,
    proofRef: makeGProofRef0('ThresholdCert'),
  };
}

function makeGProofRef0(rowKind) {
  return {
    kind: 'ProofRef0',
    refKind: 'KPrimitive',
    id: `G.${rowKind}.proof`,
  };
}

function makeGProofNodes0(preNAND, baseline) {
  const baselineDerivation = makeBaselineDerivation0(preNAND, baseline);
  const traceDerivation = makeTraceDerivation0(preNAND);
  const thresholdDerivation = makeThresholdDerivation0(preNAND, baseline);

  return [
    {
      kind: 'KProofNode0',
      id: 'G.BaselineCert.proof',
      refKind: 'KPrimitive',
      rowKind: 'BaselineCert',
      rule: 'BaselineDistinctDirectWire0',
      mode: 'full',
      premises: [],
      conclusion: {
        kind: 'GProofConclusion0',
        rowKind: 'BaselineCert',
        theorem: 'BaselineDistinct',
        accepted: true,
      },
      payload: {
        derivationKind: 'BaselineDerivation0',
        baseline: baselineDerivation.baseline,
        totalFunctions: baselineDerivation.totalFunctions,
        directWireOutputConvention: baselineDerivation.directWireOutputConvention,
        directWireOutputLowerBound: baselineDerivation.directWireOutputLowerBound,
        pairwiseDistinctNonconstantNonprojection:
          baselineDerivation.pairwiseDistinctNonconstantNonprojection,
        macroTruthSignaturesPairwiseDistinct:
          baselineDerivation.macroTruthSignaturesPairwiseDistinct,
        macroOutputsNonconstant: baselineDerivation.macroOutputsNonconstant,
        macroOutputsNonprojection: baselineDerivation.macroOutputsNonprojection,
        carrierTaggedCrossInstanceDistinct:
          baselineDerivation.carrierTaggedCrossInstanceDistinct,
        prefixOutputsSeparatedFromMacros:
          baselineDerivation.prefixOutputsSeparatedFromMacros,
        duplicateSourceOccurrenceSlotsFresh:
          baselineDerivation.duplicateSourceOccurrenceSlotsFresh,
        projectionModelPositiveBoundaryOnly:
          baselineDerivation.projectionModelPositiveBoundaryOnly,
        lowerBoundRuleApplied: baselineDerivation.lowerBoundRuleApplied,
        gateOutputInjection: baselineDerivation.gateOutputInjection,
        proofRef: baselineDerivation.proofRef,
      },
      boundsRef: {
        kind: 'BoundsRef0',
        id: 'G.BaselineCert.bounds',
        finite: true,
        polynomial: true,
      },
    },
    {
      kind: 'KProofNode0',
      id: 'G.TraceCert.proof',
      refKind: 'KPrimitive',
      rowKind: 'TraceCert',
      rule: 'NANDTraceCoherence0',
      mode: 'full',
      premises: [],
      conclusion: {
        kind: 'GProofConclusion0',
        rowKind: 'TraceCert',
        theorem: 'TraceCoherence',
        accepted: true,
      },
      payload: {
        derivationKind: 'TraceDerivation0',
        gateTraceCount: traceDerivation.gateTraceCount,
        sourceOccurrenceCount: traceDerivation.sourceOccurrenceCount,
        traceEquivalence: traceDerivation.traceEquivalence,
        topologicalInduction: traceDerivation.topologicalInduction,
        topologicalTraceInduction: traceDerivation.topologicalTraceInduction,
        lockActivationRequired: traceDerivation.lockActivationRequired,
        equalityLocksForceEquality: traceDerivation.equalityLocksForceEquality,
        constantLocksForceValues: traceDerivation.constantLocksForceValues,
        nandTraceLocksForceGateEquations:
          traceDerivation.nandTraceLocksForceGateEquations,
        prefixCoversAllDistinguishedChecks:
          traceDerivation.prefixCoversAllDistinguishedChecks,
        outputSlotIsCircuitOutput: traceDerivation.outputSlotIsCircuitOutput,
        duplicateSourceOccurrencesFresh:
          traceDerivation.duplicateSourceOccurrencesFresh,
        traceCoherent: traceDerivation.traceCoherent,
        allTraceMacrosAccepted: traceDerivation.allTraceMacrosAccepted,
        proofRef: traceDerivation.proofRef,
      },
      boundsRef: {
        kind: 'BoundsRef0',
        id: 'G.TraceCert.bounds',
        finite: true,
        polynomial: true,
      },
    },
    {
      kind: 'KProofNode0',
      id: 'G.ThresholdCert.proof',
      refKind: 'KPrimitive',
      rowKind: 'ThresholdCert',
      rule: 'LockedNANDThreshold0',
      mode: 'full',
      premises: [
        'G.BaselineCert.proof',
        'G.TraceCert.proof',
      ],
      conclusion: {
        kind: 'GProofConclusion0',
        rowKind: 'ThresholdCert',
        theorem: 'LockedNANDThreshold',
        accepted: true,
      },
      payload: {
        derivationKind: 'ThresholdDerivation0',
        baseline: thresholdDerivation.baseline,
        fullWordSize: thresholdDerivation.fullWordSize,
        residualSlackMax: thresholdDerivation.residualSlackMax,
        lockedThreshold: thresholdDerivation.lockedThreshold,
        satIffMinAboveBaseline: thresholdDerivation.satIffMinAboveBaseline,
        unsatMinEqualsBaseline: thresholdDerivation.unsatMinEqualsBaseline,
        zeroOutputConvention: thresholdDerivation.zeroOutputConvention,
        finalLockSeparation: thresholdDerivation.finalLockSeparation,
        finalOutputGates: thresholdDerivation.finalOutputGates,
        noHiddenMinimization: thresholdDerivation.noHiddenMinimization,
        proofRef: thresholdDerivation.proofRef,
      },
      boundsRef: {
        kind: 'BoundsRef0',
        id: 'G.ThresholdCert.bounds',
        finite: true,
        polynomial: true,
      },
    },
  ];
}


function expectedGProofNodeSpec0(rowKind) {
  if (rowKind === 'BaselineCert') {
    return {
      id: 'G.BaselineCert.proof',
      rule: 'BaselineDistinctDirectWire0',
      theorem: 'BaselineDistinct',
      premises: [],
    };
  }

  if (rowKind === 'TraceCert') {
    return {
      id: 'G.TraceCert.proof',
      rule: 'NANDTraceCoherence0',
      theorem: 'TraceCoherence',
      premises: [],
    };
  }

  if (rowKind === 'ThresholdCert') {
    return {
      id: 'G.ThresholdCert.proof',
      rule: 'LockedNANDThreshold0',
      theorem: 'LockedNANDThreshold',
      premises: [
        'G.BaselineCert.proof',
        'G.TraceCert.proof',
      ],
    };
  }

  return null;
}

function validateGDerivationProofNodes0(gpack) {
  const piG = getPiG0(gpack);

  if (!isPlainObject(piG)) {
    return validationReject0(['PiG'], 'GPack must expose PiG for derivation proof-node checking', {
      actual: typeof piG,
    });
  }

  const expectedIds = [
    'G.BaselineCert.proof',
    'G.TraceCert.proof',
    'G.ThresholdCert.proof',
  ];

  if (!Array.isArray(piG.proofOrder)) {
    return validationReject0(['PiG', 'proofOrder'], 'PiG must include proofOrder', {
      actual: typeof piG.proofOrder,
    });
  }

  for (let index = 0; index < expectedIds.length; index += 1) {
    if (piG.proofOrder[index] !== expectedIds[index]) {
      return validationReject0(['PiG', 'proofOrder', index], 'PiG proofOrder mismatch', {
        expected: expectedIds[index],
        actual: piG.proofOrder[index],
      });
    }
  }

  if (piG.proofOrder.length !== expectedIds.length) {
    return validationReject0(['PiG', 'proofOrder'], 'PiG proofOrder must contain exactly the G derivation proof nodes', {
      expected: expectedIds.length,
      actual: piG.proofOrder.length,
    });
  }

  if (!Array.isArray(piG.proofNodes)) {
    return validationReject0(['PiG', 'proofNodes'], 'PiG must include proofNodes', {
      actual: typeof piG.proofNodes,
    });
  }

  const nodeById = new Map();

  for (let index = 0; index < piG.proofNodes.length; index += 1) {
    const node = piG.proofNodes[index];

    if (!isPlainObject(node)) {
      return validationReject0(['PiG', 'proofNodes', index], 'PiG proof node must be an object', {
        actual: typeof node,
      });
    }

    if (typeof node.id !== 'string' || node.id.length === 0) {
      return validationReject0(['PiG', 'proofNodes', index, 'id'], 'PiG proof node id must be a non-empty string', {
        actual: node.id,
      });
    }

    if (nodeById.has(node.id)) {
      return validationReject0(['PiG', 'proofNodes', index, 'id'], 'PiG proof node ids must be unique', {
        id: node.id,
      });
    }

    nodeById.set(node.id, node);
  }

  const certRows = [
    ['BaselineCert', gpack.BaselineCert],
    ['TraceCert', gpack.TraceCert],
    ['ThresholdCert', gpack.ThresholdCert],
  ];

  for (const [rowKind, cert] of certRows) {
    const ref = cert?.derivation?.proofRef;
    const refCheck = validateGDerivationProofRef0(
      ref,
      ['GPack', rowKind, 'derivation', 'proofRef'],
      rowKind,
    );

    if (!refCheck.ok) {
      return refCheck;
    }

    const node = nodeById.get(ref.id);

    if (!isPlainObject(node)) {
      return validationReject0(['PiG', 'proofNodes', ref.id], 'G derivation proofRef must resolve to a PiG proof node', {
        id: ref.id,
      });
    }

    const nodeCheck = validateGProofNode0(
      node,
      ['PiG', 'proofNodes', ref.id],
      rowKind,
      cert,
    );

    if (!nodeCheck.ok) {
      return nodeCheck;
    }
  }

  const acyclic = validateGProofNodeAcyclic0(nodeById, expectedIds);

  if (!acyclic.ok) {
    return acyclic;
  }

  return validationAccept0({
    kind: 'GDerivationProofNodes0NF',
    proofNodeCount: expectedIds.length,
    proofOrder: expectedIds,
  });
}

function validateGProofNode0(node, path, rowKind, cert) {
  const spec = expectedGProofNodeSpec0(rowKind);

  if (!isPlainObject(spec)) {
    return validationReject0(path, 'unknown G proof node row kind', {
      rowKind,
    });
  }

  const expected = {
    kind: 'KProofNode0',
    id: spec.id,
    refKind: 'KPrimitive',
    rowKind,
    rule: spec.rule,
    mode: 'full',
  };

  for (const [field, expectedValue] of Object.entries(expected)) {
    if (node[field] !== expectedValue) {
      return validationReject0([...path, field], 'G proof node field mismatch', {
        expected: expectedValue,
        actual: node[field],
      });
    }
  }

  if (!Array.isArray(node.premises)) {
    return validationReject0([...path, 'premises'], 'G proof node premises must be an array', {
      actual: typeof node.premises,
    });
  }

  if (node.premises.length !== spec.premises.length) {
    return validationReject0([...path, 'premises'], 'G proof node premise count mismatch', {
      expected: spec.premises.length,
      actual: node.premises.length,
    });
  }

  for (let index = 0; index < spec.premises.length; index += 1) {
    if (node.premises[index] !== spec.premises[index]) {
      return validationReject0([...path, 'premises', index], 'G proof node premise mismatch', {
        expected: spec.premises[index],
        actual: node.premises[index],
      });
    }
  }

  if (!isPlainObject(node.conclusion)) {
    return validationReject0([...path, 'conclusion'], 'G proof node conclusion must be an object', {
      actual: typeof node.conclusion,
    });
  }

  const expectedConclusion = {
    kind: 'GProofConclusion0',
    rowKind,
    theorem: spec.theorem,
    accepted: true,
  };

  for (const [field, expectedValue] of Object.entries(expectedConclusion)) {
    if (node.conclusion[field] !== expectedValue) {
      return validationReject0([...path, 'conclusion', field], 'G proof node conclusion mismatch', {
        expected: expectedValue,
        actual: node.conclusion[field],
      });
    }
  }

  const opaque = validateGProofNodeNoOpaque0(node, path);

  if (!opaque.ok) {
    return opaque;
  }

  const bounds = validateGProofNodeBounds0(node.boundsRef, [...path, 'boundsRef'], rowKind);

  if (!bounds.ok) {
    return bounds;
  }

  const payload = validateGProofNodePayload0(node.payload, [...path, 'payload'], rowKind, cert);

  if (!payload.ok) {
    return payload;
  }

  return validationAccept0({
    kind: 'GProofNode0NF',
    rowKind,
    id: spec.id,
  });
}

function validateGProofNodePayload0(payload, path, rowKind, cert) {
  if (!isPlainObject(payload)) {
    return validationReject0(path, 'G proof node payload must be an object', {
      actual: typeof payload,
    });
  }

  const derivation = cert?.derivation;

  if (!isPlainObject(derivation)) {
    return validationReject0(path, 'G proof node payload requires derivation object', {
      actual: typeof derivation,
    });
  }

  if (rowKind === 'BaselineCert') {
    const expected = {
      derivationKind: 'BaselineDerivation0',
      baseline: derivation.baseline,
      totalFunctions: derivation.totalFunctions,
      directWireOutputConvention: true,
      directWireOutputLowerBound: true,
      pairwiseDistinctNonconstantNonprojection: true,
      macroTruthSignaturesPairwiseDistinct: true,
      macroOutputsNonconstant: true,
      macroOutputsNonprojection: true,
      carrierTaggedCrossInstanceDistinct: true,
      prefixOutputsSeparatedFromMacros: true,
      duplicateSourceOccurrenceSlotsFresh: true,
      projectionModelPositiveBoundaryOnly: true,
      lowerBoundRuleApplied: true,
      gateOutputInjection: 'distinct-noninput-outputs-map-to-distinct-NAND-gates',
    };

    return validateGProofPayloadFields0(payload, path, expected);
  }

  if (rowKind === 'TraceCert') {
    const expected = {
      derivationKind: 'TraceDerivation0',
      gateTraceCount: derivation.gateTraceCount,
      sourceOccurrenceCount: derivation.sourceOccurrenceCount,
      traceEquivalence:
        'all distinguished checks one iff trace slots encode a valid NAND evaluation',
      topologicalInduction: true,
      topologicalTraceInduction: true,
      lockActivationRequired: true,
      equalityLocksForceEquality: true,
      constantLocksForceValues: true,
      nandTraceLocksForceGateEquations: true,
      prefixCoversAllDistinguishedChecks: true,
      outputSlotIsCircuitOutput: true,
      duplicateSourceOccurrencesFresh: true,
      traceCoherent: true,
      allTraceMacrosAccepted: true,
    };

    return validateGProofPayloadFields0(payload, path, expected);
  }

  if (rowKind === 'ThresholdCert') {
    const expected = {
      derivationKind: 'ThresholdDerivation0',
      baseline: derivation.baseline,
      fullWordSize: derivation.fullWordSize,
      residualSlackMax: 4,
      lockedThreshold: true,
      satIffMinAboveBaseline: true,
      unsatMinEqualsBaseline: true,
      zeroOutputConvention: true,
      finalLockSeparation: true,
      finalOutputGates: 4,
      noHiddenMinimization: true,
    };

    return validateGProofPayloadFields0(payload, path, expected);
  }

  return validationReject0(path, 'unknown G proof node payload row kind', {
    rowKind,
  });
}

function validateGProofPayloadFields0(payload, path, expected) {
  for (const [field, expectedValue] of Object.entries(expected)) {
    if (payload[field] !== expectedValue) {
      return validationReject0([...path, field], 'G proof node payload mismatch', {
        expected: expectedValue,
        actual: payload[field],
      });
    }
  }

  if (!isPlainObject(payload.proofRef)) {
    return validationReject0([...path, 'proofRef'], 'G proof node payload must carry proofRef', {
      actual: typeof payload.proofRef,
    });
  }

  return validationAccept0({
    kind: 'GProofPayload0NF',
  });
}

function validateGProofNodeNoOpaque0(node, path) {
  if (node.opaque === true) {
    return validationReject0([...path, 'opaque'], 'G proof node must not be opaque', {
      actual: node.opaque,
    });
  }

  for (const field of ['proofBlob', 'opaqueBytes', 'bytes']) {
    if (Object.prototype.hasOwnProperty.call(node, field)) {
      return validationReject0([...path, field], 'G proof node must not contain opaque proof material', {
        field,
      });
    }
  }

  return validationAccept0({
    kind: 'GProofNodeNoOpaque0NF',
  });
}

function validateGProofNodeBounds0(boundsRef, path, rowKind) {
  if (!isPlainObject(boundsRef)) {
    return validationReject0(path, 'G proof node boundsRef must be an object', {
      actual: typeof boundsRef,
    });
  }

  const expectedId = `G.${rowKind}.bounds`;

  if (
    boundsRef.kind !== 'BoundsRef0' ||
    boundsRef.id !== expectedId ||
    boundsRef.finite !== true ||
    boundsRef.polynomial !== true
  ) {
    return validationReject0(path, 'G proof node boundsRef mismatch', {
      expected: {
        kind: 'BoundsRef0',
        id: expectedId,
        finite: true,
        polynomial: true,
      },
      actual: boundsRef,
    });
  }

  return validationAccept0({
    kind: 'GProofNodeBounds0NF',
    id: expectedId,
  });
}

function validateGProofNodeAcyclic0(nodeById, requiredIds) {
  const visiting = new Set();
  const visited = new Set();

  function visit(id, stack) {
    if (visiting.has(id)) {
      return validationReject0(['PiG', 'proofNodes', id], 'G proof nodes must be acyclic', {
        cycle: [...stack, id],
      });
    }

    if (visited.has(id)) {
      return validationAccept0({
        kind: 'GProofNodeAcyclicStep0NF',
      });
    }

    const node = nodeById.get(id);

    if (!isPlainObject(node)) {
      return validationReject0(['PiG', 'proofNodes', id], 'G proof node premise must resolve', {
        id,
      });
    }

    visiting.add(id);

    for (let index = 0; index < (node.premises ?? []).length; index += 1) {
      const premise = node.premises[index];

      if (typeof premise !== 'string' || !nodeById.has(premise)) {
        return validationReject0(['PiG', 'proofNodes', id, 'premises', index], 'G proof node premise must resolve', {
          premise,
        });
      }

      const child = visit(premise, [...stack, id]);

      if (!child.ok) {
        return child;
      }
    }

    visiting.delete(id);
    visited.add(id);

    return validationAccept0({
      kind: 'GProofNodeAcyclicStep0NF',
    });
  }

  for (const id of requiredIds) {
    const result = visit(id, []);

    if (!result.ok) {
      return result;
    }
  }

  return validationAccept0({
    kind: 'GProofNodeAcyclic0NF',
    proofNodeCount: requiredIds.length,
  });
}


function validateGDerivationProofRef0(value, path, rowKind) {
  if (!isPlainObject(value)) {
    return validationReject0(path, 'G derivation proofRef must be an object', {
      actual: typeof value,
    });
  }

  const expected = makeGProofRef0(rowKind);

  for (const field of ['kind', 'refKind', 'id']) {
    if (value[field] !== expected[field]) {
      return validationReject0([...path, field], 'G derivation proofRef mismatch', {
        expected: expected[field],
        actual: value[field],
      });
    }
  }

  return validationAccept0({
    kind: 'GDerivationProofRef0NF',
    rowKind,
    proofRef: expected,
  });
}

function validateRowProofRefExact0(value, path, rowKind) {
  if (!isPlainObject(value)) {
    return validationReject0(path, 'RowFamG row proofRef must be an object', {
      actual: typeof value,
    });
  }

  const expected = makeGProofRef0(rowKind);

  for (const field of ['kind', 'refKind', 'id']) {
    if (value[field] !== expected[field]) {
      return validationReject0([...path, field], 'RowFamG row proofRef mismatch', {
        expected: expected[field],
        actual: value[field],
      });
    }
  }

  return validationAccept0({
    kind: 'RowFamGProofRefExact0NF',
    rowKind,
    proofRef: expected,
  });
}

function validateRowFamGDerivationProofRefs0(rowFam) {
  if (!isPlainObject(rowFam) || !isPlainObject(rowFam.GPack)) {
    return validationReject0(['GPack'], 'RowFamG derivation proof-ref binding requires GPack', {
      actual: typeof rowFam?.GPack,
    });
  }

  const rowsByKind = new Map();

  for (const row of rowFam.rows ?? []) {
    if (isPlainObject(row) && typeof row.rowKind === 'string') {
      rowsByKind.set(row.rowKind, row);
    }
  }

  const certRows = [
    ['BaselineCert', rowFam.GPack.BaselineCert],
    ['TraceCert', rowFam.GPack.TraceCert],
    ['ThresholdCert', rowFam.GPack.ThresholdCert],
  ];

  for (const [rowKind, cert] of certRows) {
    const row = rowsByKind.get(rowKind);

    if (!isPlainObject(row)) {
      return validationReject0(['rows', 'derivationProofRefs', rowKind], 'RowFamG is missing row required by derivation proofRef', {
        rowKind,
      });
    }

    const rowProofRef = validateRowProofRefExact0(
      row.proofRef,
      ['rows', rowKind, 'proofRef'],
      rowKind,
    );

    if (!rowProofRef.ok) {
      return rowProofRef;
    }

    const derivationProofRef = validateGDerivationProofRef0(
      cert?.derivation?.proofRef,
      ['GPack', rowKind, 'derivation', 'proofRef'],
      rowKind,
    );

    if (!derivationProofRef.ok) {
      return derivationProofRef;
    }

    if (
      cert.derivation.proofRef.kind !== row.proofRef.kind ||
      cert.derivation.proofRef.refKind !== row.proofRef.refKind ||
      cert.derivation.proofRef.id !== row.proofRef.id
    ) {
      return validationReject0(['GPack', rowKind, 'derivation', 'proofRef'], 'GPack derivation proofRef must match RowFamG row proofRef', {
        expected: row.proofRef,
        actual: cert.derivation.proofRef,
      });
    }
  }

  return validationAccept0({
    kind: 'RowFamGDerivationProofRefs0NF',
    proofRefCount: certRows.length,
  });
}


function validateBaselineCertHardened0(gpack) {
  const base = validateBaselineCert0(gpack);

  if (!base.ok) {
    return base;
  }

  const cert = gpack.BaselineCert;
  const baseline = computeBaselineFromPreNAND0(gpack.PreNAND);

  for (const field of [
    'distinctNonconstantNonprojection',
    'lowerBound',
    'directWireOutputLowerBound',
    'macroTruthSignaturesPairwiseDistinct',
    'macroOutputsNonconstant',
    'macroOutputsNonprojection',
    'carrierTaggedCrossInstanceDistinct',
    'prefixOutputsSeparatedFromMacros',
    'duplicateSourceOccurrenceSlotsFresh',
    'projectionModelPositiveBoundaryOnly',
  ]) {
    if (cert[field] !== true) {
      return validationReject0(['BaselineCert', field], `BaselineCert must certify ${field}`, {
        actual: cert[field],
      });
    }
  }

  if (cert.functionsCount !== baseline) {
    return validationReject0(['BaselineCert', 'functionsCount'], 'BaselineCert functionsCount must match computed baseline', {
      expected: baseline,
      actual: cert.functionsCount,
    });
  }

  const derivation = validateBaselineDerivation0(cert.derivation, gpack.PreNAND, baseline);

  if (!derivation.ok) {
    return derivation;
  }

  return validationAccept0({
    kind: 'BaselineCertHardened0NF',
    baseline,
    derivation: derivation.nf,
    prior: base.nf ?? null,
  });
}

function validateTraceCertHardened0(gpack) {
  const base = validateTraceCert0(gpack);

  if (!base.ok) {
    return base;
  }

  const cert = gpack.TraceCert;
  const counts = getSourceCounts0(gpack.PreNAND);
  const expectedSourceOccurrenceCount =
    counts.equalityOccurrences +
    counts.constZeroOccurrences +
    counts.constOneOccurrences;

  for (const field of [
    'traceCoherent',
    'traceEquivalence',
    'lockActivationRequired',
    'equalityLocksForceEquality',
    'constantLocksForceValues',
    'nandTraceLocksForceGateEquations',
    'prefixCoversAllDistinguishedChecks',
    'topologicalTraceInduction',
    'outputSlotIsCircuitOutput',
    'duplicateSourceOccurrencesFresh',
    'allTraceMacrosAccepted',
  ]) {
    if (cert[field] !== true) {
      return validationReject0(['TraceCert', field], `TraceCert must certify ${field}`, {
        actual: cert[field],
      });
    }
  }

  if (cert.gateTraceCount !== gpack.PreNAND.gates.length) {
    return validationReject0(['TraceCert', 'gateTraceCount'], 'TraceCert gateTraceCount mismatch', {
      expected: gpack.PreNAND.gates.length,
      actual: cert.gateTraceCount,
    });
  }

  if (cert.sourceOccurrenceCount !== expectedSourceOccurrenceCount) {
    return validationReject0(['TraceCert', 'sourceOccurrenceCount'], 'TraceCert sourceOccurrenceCount mismatch', {
      expected: expectedSourceOccurrenceCount,
      actual: cert.sourceOccurrenceCount,
    });
  }

  const derivation = validateTraceDerivation0(cert.derivation, gpack.PreNAND);

  if (!derivation.ok) {
    return derivation;
  }

  return validationAccept0({
    kind: 'TraceCertHardened0NF',
    gateTraceCount: cert.gateTraceCount,
    sourceOccurrenceCount: cert.sourceOccurrenceCount,
    derivation: derivation.nf,
    prior: base.nf ?? null,
  });
}

function validateThresholdCertHardened0(gpack) {
  const base = validateThresholdCert0(gpack);

  if (!base.ok) {
    return base;
  }

  const cert = gpack.ThresholdCert;
  const baseline = computeBaselineFromPreNAND0(gpack.PreNAND);

  for (const field of [
    'lockedThreshold',
    'satIffMinAboveBaseline',
    'unsatMinEqualsBaseline',
    'zeroOutputConvention',
    'finalLockSeparation',
  ]) {
    if (cert[field] !== true) {
      return validationReject0(['ThresholdCert', field], `ThresholdCert must certify ${field}`, {
        actual: cert[field],
      });
    }
  }

  if (cert.baseline !== baseline) {
    return validationReject0(['ThresholdCert', 'baseline'], 'ThresholdCert baseline mismatch', {
      expected: baseline,
      actual: cert.baseline,
    });
  }

  if (cert.fullWordSize !== baseline + 4) {
    return validationReject0(['ThresholdCert', 'fullWordSize'], 'ThresholdCert fullWordSize must be baseline plus four', {
      expected: baseline + 4,
      actual: cert.fullWordSize,
    });
  }

  if (cert.residualSlackMax !== 4) {
    return validationReject0(['ThresholdCert', 'residualSlackMax'], 'ThresholdCert residual slack must be exactly four for the locked NAND release theorem', {
      expected: 4,
      actual: cert.residualSlackMax,
    });
  }

  const derivation = validateThresholdDerivation0(cert.derivation, gpack.PreNAND, baseline);

  if (!derivation.ok) {
    return derivation;
  }

  return validationAccept0({
    kind: 'ThresholdCertHardened0NF',
    baseline,
    fullWordSize: baseline + 4,
    residualSlackMax: 4,
    derivation: derivation.nf,
    prior: base.nf ?? null,
  });
}

function validateBaselineDerivation0(value, preNAND, baseline) {
  if (!isPlainObject(value)) {
    return validationReject0(['BaselineCert', 'derivation'], 'BaselineCert must include a structured derivation record', {
      actual: typeof value,
    });
  }

  const counts = getSourceCounts0(preNAND);
  const expected = {
    kind: 'BaselineDerivation0',
    version: CHECKER_VERSION,
    rule: 'BaselineDistinctDirectWire0',
    baseline,
    gateCount: preNAND.gates.length,
    equalityOccurrences: counts.equalityOccurrences,
    constZeroOccurrences: counts.constZeroOccurrences,
    constOneOccurrences: counts.constOneOccurrences,
    totalFunctions: baseline,
    functionsCount: baseline,
  };

  for (const [field, expectedValue] of Object.entries(expected)) {
    if (value[field] !== expectedValue) {
      return validationReject0(['BaselineCert', 'derivation', field], 'Baseline derivation field mismatch', {
        expected: expectedValue,
        actual: value[field],
      });
    }
  }

  if (!isPlainObject(value.components)) {
    return validationReject0(['BaselineCert', 'derivation', 'components'], 'Baseline derivation components must be an object', {
      actual: typeof value.components,
    });
  }

  const expectedComponents = {
    traceOutputs: 18 * preNAND.gates.length,
    equalityOutputs: 10 * counts.equalityOccurrences,
    constZeroOutputs: 3 * counts.constZeroOccurrences,
    constOneOutputs: 2 * counts.constOneOccurrences,
    prefixOutputs: 2 * (3 * preNAND.gates.length - 1),
  };

  for (const [field, expectedValue] of Object.entries(expectedComponents)) {
    if (value.components[field] !== expectedValue) {
      return validationReject0(['BaselineCert', 'derivation', 'components', field], 'Baseline derivation component mismatch', {
        expected: expectedValue,
        actual: value.components[field],
      });
    }
  }

  for (const field of [
    'directWireOutputConvention',
    'directWireOutputLowerBound',
    'pairwiseDistinctNonconstantNonprojection',
    'macroTruthSignaturesPairwiseDistinct',
    'macroOutputsNonconstant',
    'macroOutputsNonprojection',
    'carrierTaggedCrossInstanceDistinct',
    'prefixOutputsSeparatedFromMacros',
    'duplicateSourceOccurrenceSlotsFresh',
    'projectionModelPositiveBoundaryOnly',
    'privateLocksFresh',
    'macroSignaturesChecked',
    'crossMacroSharingForbiddenBySep',
    'lowerBoundRuleApplied',
    'constructedBaselineExact',
  ]) {
    if (value[field] !== true) {
      return validationReject0(['BaselineCert', 'derivation', field], `Baseline derivation must certify ${field}`, {
        actual: value[field],
      });
    }
  }

  if (value.gateOutputInjection !== 'distinct-noninput-outputs-map-to-distinct-NAND-gates') {
    return validationReject0(['BaselineCert', 'derivation', 'gateOutputInjection'], 'Baseline derivation must state the direct-wire gate-output injection rule', {
      actual: value.gateOutputInjection,
    });
  }

  const proofRef = validateGDerivationProofRef0(
    value.proofRef,
    ['BaselineCert', 'derivation', 'proofRef'],
    'BaselineCert',
  );

  if (!proofRef.ok) {
    return proofRef;
  }

  return validationAccept0({
    kind: 'BaselineDerivation0NF',
    baseline,
    proofRef: proofRef.nf,
  });
}

function validateTraceDerivation0(value, preNAND) {
  if (!isPlainObject(value)) {
    return validationReject0(['TraceCert', 'derivation'], 'TraceCert must include a structured derivation record', {
      actual: typeof value,
    });
  }

  const counts = getSourceCounts0(preNAND);
  const sourceOccurrenceCount =
    counts.equalityOccurrences +
    counts.constZeroOccurrences +
    counts.constOneOccurrences;

  const expected = {
    kind: 'TraceDerivation0',
    version: CHECKER_VERSION,
    rule: 'NANDTraceCoherence0',
    gateTraceCount: preNAND.gates.length,
    sourceOccurrenceCount,
    equalityOccurrences: counts.equalityOccurrences,
    constZeroOccurrences: counts.constZeroOccurrences,
    constOneOccurrences: counts.constOneOccurrences,
    traceMacroName: 'MN',
    distinguishedOutput: 'q16',
  };

  for (const [field, expectedValue] of Object.entries(expected)) {
    if (value[field] !== expectedValue) {
      return validationReject0(['TraceCert', 'derivation', field], 'Trace derivation field mismatch', {
        expected: expectedValue,
        actual: value[field],
      });
    }
  }

  for (const field of [
    'topologicalInduction',
    'topologicalTraceInduction',
    'lockActivationRequired',
    'equalityLocksForceEquality',
    'constantLocksForceValues',
    'nandTraceLocksForceGateEquations',
    'prefixCoversAllDistinguishedChecks',
    'outputSlotIsCircuitOutput',
    'duplicateSourceOccurrencesFresh',
    'sourceOccurrencesFresh',
    'constantsThroughMacros',
    'noCarrierConstants',
    'traceCoherent',
    'allTraceMacrosAccepted',
  ]) {
    if (value[field] !== true) {
      return validationReject0(['TraceCert', 'derivation', field], `Trace derivation must certify ${field}`, {
        actual: value[field],
      });
    }
  }

  if (
    value.traceEquivalence !==
    'all distinguished checks one iff trace slots encode a valid NAND evaluation'
  ) {
    return validationReject0(['TraceCert', 'derivation', 'traceEquivalence'], 'Trace derivation must state the trace equivalence invariant', {
      actual: value.traceEquivalence,
    });
  }

  const proofRef = validateGDerivationProofRef0(
    value.proofRef,
    ['TraceCert', 'derivation', 'proofRef'],
    'TraceCert',
  );

  if (!proofRef.ok) {
    return proofRef;
  }

  return validationAccept0({
    kind: 'TraceDerivation0NF',
    gateTraceCount: preNAND.gates.length,
    sourceOccurrenceCount,
    proofRef: proofRef.nf,
  });
}

function validateThresholdDerivation0(value, preNAND, baseline) {
  if (!isPlainObject(value)) {
    return validationReject0(['ThresholdCert', 'derivation'], 'ThresholdCert must include a structured derivation record', {
      actual: typeof value,
    });
  }

  const expected = {
    kind: 'ThresholdDerivation0',
    version: CHECKER_VERSION,
    rule: 'LockedNANDThreshold0',
    baseline,
    fullWordSize: baseline + 4,
    residualSlackMax: 4,
    satUpperBoundExtraGates: 4,
    satLowerBoundExtraGates: 1,
    finalOutputGates: 4,
    finalOutput: 'Fphi = z && Tphi && yout',
    baselineDerivation: 'BaselineDerivation0',
    traceDerivation: 'TraceDerivation0',
  };

  for (const [field, expectedValue] of Object.entries(expected)) {
    if (value[field] !== expectedValue) {
      return validationReject0(['ThresholdCert', 'derivation', field], 'Threshold derivation field mismatch', {
        expected: expectedValue,
        actual: value[field],
      });
    }
  }

  for (const field of [
    'lockedThreshold',
    'satIffMinAboveBaseline',
    'unsatMinEqualsBaseline',
    'zeroOutputConvention',
    'finalLockSeparation',
    'finalLockOnlyFinal',
    'exposesOnlyFinal',
    'noHiddenMinimization',
  ]) {
    if (value[field] !== true) {
      return validationReject0(['ThresholdCert', 'derivation', field], `Threshold derivation must certify ${field}`, {
        actual: value[field],
      });
    }
  }

  const proofRef = validateGDerivationProofRef0(
    value.proofRef,
    ['ThresholdCert', 'derivation', 'proofRef'],
    'ThresholdCert',
  );

  if (!proofRef.ok) {
    return proofRef;
  }

  return validationAccept0({
    kind: 'ThresholdDerivation0NF',
    baseline,
    fullWordSize: baseline + 4,
    residualSlackMax: 4,
    proofRef: proofRef.nf,
  });
}

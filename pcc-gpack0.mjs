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
      hex: 'formula.synthetic',
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
      hex: 'sched.synthetic',
    },

    IfaceHash: {
      alg: 'SHA256',
      hex: 'iface.synthetic',
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
    },

    TraceCert: {
      kind: 'TraceCert0',
      version: CHECKER_VERSION,
      traceCoherent: true,
      gateTraceCount: preNAND.gates.length,
      allTraceMacrosAccepted: true,
      sourceOccurrenceCount:
        preNAND.sourceOccurrences.equality +
        preNAND.sourceOccurrences.const0 +
        preNAND.sourceOccurrences.const1,
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
    ['baseline', `${checker}.baseline`, () => validateBaselineCert0(gpack)],
    ['trace', `${checker}.trace`, () => validateTraceCert0(gpack)],
    ['threshold', `${checker}.threshold`, () => validateThresholdCert0(gpack)],
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
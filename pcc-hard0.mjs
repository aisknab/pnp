import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;

export const HARD_CHECKER_FIELDS0 = Object.freeze([
  'ValidatorCore',
  'IfaceCheck',
  'NFCheck',
  'RowKeyCheck',
  'DupCheck',
  'RouteCheck',
  'ProofRefCheck',
  'HashCheck',
  'NoMinCheck',
  'ImportCheck',
  'ReflectionCheck',
  'BoundsCheck',
  'DiagCheck',
]);

export const HARD_CHECKER_IDS0 = Object.freeze({
  ValidatorCore: 'ValidatorCore',
  IfaceCheck: 'CheckIfaceDict',
  NFCheck: 'CheckNFProtocol',
  RowKeyCheck: 'CheckRowKeys',
  DupCheck: 'CheckDuplicateRows',
  RouteCheck: 'CheckRoutePriority',
  ProofRefCheck: 'CheckProofRefs',
  HashCheck: 'CheckHashProtocol',
  NoMinCheck: 'CheckNoHiddenMin',
  ImportCheck: 'CheckImportGraph',
  ReflectionCheck: 'CheckReflection',
  BoundsCheck: 'CheckBounds',
  DiagCheck: 'CheckDiagnostics',
});

export const HARD_FORBIDDEN_SYMBOLS0 = Object.freeze([
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

export const HARD_NO_MIN_EXPANSION_STAGES0 = Object.freeze([
  'macros',
  'aliases',
  'generatedTemplates',
  'imports',
]);

export const HARD_OCCURRENCE_CLASSES0 = Object.freeze([
  'DefImport',
  'SoundImport',
  'ExecCall',
  'AssumeOnly',
  'EmitToken',
]);

export const HARD_ROWKEY_FIELDS0 = Object.freeze([
  'IfaceHash',
  'PackageID',
  'SchemaID',
  'KindKey',
  'ArityKey',
  'ModeKey',
  'FrontKey',
  'SemanticKey',
  'IncidenceKey',
  'DependencyKey',
  'ProfileKey',
  'ChargeKey',
  'ObligationKey',
  'BudgetKey',
  'ActivationKey',
  'RankKey',
  'PayloadKey',
]);

export const HARD_ROUTE_PRIORITY0 = Object.freeze([
  'Gain',
  'Minimum',
  'ZeroSlack',
  'NoBudget',
  'NoHereditary',
  'SelectorSilent',
  'Faithful',
  'Token',
  'Neutral',
  'Reject',
]);

export const HARD_ALLOWED_PROOF_REF_KINDS0 = Object.freeze([
  'KPrimitive',
  'SigmaInstance',
  'ReflectionInstance',
  'EarlierRowProof',
]);

export const HARD_FORBIDDEN_IMPORT_EDGES0 = Object.freeze([
  Object.freeze(['BC', 'UN']),
  Object.freeze(['UN', 'BC']),
  Object.freeze(['BCEL', 'R']),
  Object.freeze(['BUD', 'R']),
  Object.freeze(['O', 'G']),
  Object.freeze(['G', 'O']),
]);

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

const REQUIRED_DESCRIPTOR_FLAGS0 = Object.freeze([
  'total',
  'deterministic',
  'canonical',
  'hashIndependent',
  'modeSafe',
  'polynomial',
  'noUnknown',
]);

export function makeHardCheckerDescriptor0({
  checkerId,
  capabilities = [],
  polynomialBound = {
    kind: 'PolynomialBound0',
    exponent: 6,
  },
  extra = {},
}) {
  if (!isNonEmptyString(checkerId)) {
    throw new TypeError('makeHardCheckerDescriptor0 requires a non-empty checkerId');
  }

  return {
    kind: 'HardCheckerDescriptor0',
    version: CHECKER_VERSION,
    checkerId,
    total: true,
    deterministic: true,
    canonical: true,
    hashIndependent: true,
    modeSafe: true,
    polynomial: true,
    noUnknown: true,
    returns: {
      accept: [
        'NF',
        'Digest',
        'Ledger',
      ],
      reject: [
        'Coord',
        'Path',
        'Witness',
        'Digest',
      ],
    },
    capabilities,
    polynomialBound,
    ...extra,
  };
}

export function makeSyntheticHardCheck0(overrides = {}) {
  const hard = {
    kind: 'HardCheck0',
    version: CHECKER_VERSION,

    ValidatorCore: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.ValidatorCore,
      capabilities: [
        'total-dispatch',
        'accept-reject-records',
        'unique-first-failure',
      ],
      extra: {
        allowedOutputs: [
          'accept',
          'reject',
        ],
        unknownOutput: false,
      },
    }),

    IfaceCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.IfaceCheck,
      capabilities: [
        'interface-dictionary',
        'namespace-coherence',
        'forbidden-symbols',
      ],
      extra: {
        singleSourceOfTruth: true,
        namespaceCoherent: true,
        requiredObjects: [
          'publicConstructors',
          'routeTokens',
          'checkerPredicates',
          'forbiddenSymbols',
          'bounds',
        ],
      },
    }),

    NFCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.NFCheck,
      capabilities: [
        'canonical-normal-form',
        'transport-proof',
      ],
      extra: {
        idempotent: true,
        canonicalBytes: true,
        transportProofs: true,
      },
    }),

    RowKeyCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.RowKeyCheck,
      capabilities: [
        'row-key-recompute',
        'route-exclusion',
      ],
      extra: {
        rowKeyFields: HARD_ROWKEY_FIELDS0,
        excludesSelectedRoute: true,
      },
    }),

    DupCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.DupCheck,
      capabilities: [
        'duplicate-row-detection',
      ],
      extra: {
        fullRowKeyComparison: true,
        selectedRouteConflictReject: true,
      },
    }),

    RouteCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.RouteCheck,
      capabilities: [
        'route-priority',
      ],
      extra: {
        priority: HARD_ROUTE_PRIORITY0,
        noGainDowngrade: true,
        highestActiveRoute: true,
      },
    }),

    ProofRefCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.ProofRefCheck,
      capabilities: [
        'proof-reference-resolution',
      ],
      extra: {
        allowedRefKinds: HARD_ALLOWED_PROOF_REF_KINDS0,
        acyclic: true,
        rejectsOpaque: true,
        earlierRowOnly: true,
      },
    }),

    HashCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.HashCheck,
      capabilities: [
        'hash-as-index',
      ],
      extra: {
        hashAsIndexOnly: true,
        fullKeyCompareAfterHash: true,
        canonicalByteCompareAfterHash: true,
        digestEqualityIsNotObjectEquality: true,
      },
    }),

    NoMinCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.NoMinCheck,
      capabilities: [
        'no-hidden-minimization',
      ],
      extra: {
        expansionStages: HARD_NO_MIN_EXPANSION_STAGES0,
        occurrenceClasses: HARD_OCCURRENCE_CLASSES0,
        forbiddenSymbols: HARD_FORBIDDEN_SYMBOLS0,
        rejectsAliases: true,
        rejectsExecutableOnly: true,
      },
    }),

    ImportCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.ImportCheck,
      capabilities: [
        'import-acyclicity',
      ],
      extra: {
        acyclic: true,
        forbiddenEdges: HARD_FORBIDDEN_IMPORT_EDGES0,
      },
    }),

    ReflectionCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.ReflectionCheck,
      capabilities: [
        'reflection-validation',
      ],
      extra: {
        exact: true,
        publicConclusion: true,
        replayable: true,
      },
    }),

    BoundsCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.BoundsCheck,
      capabilities: [
        'polynomial-bounds',
      ],
      extra: {
        polynomialBounds: true,
        finiteSchedules: true,
        noPrivateSchedule: true,
      },
    }),

    DiagCheck: makeHardCheckerDescriptor0({
      checkerId: HARD_CHECKER_IDS0.DiagCheck,
      capabilities: [
        'diagnostics',
      ],
      extra: {
        uniqueFirstFailure: true,
        replayable: true,
        noUnknownOutput: true,
      },
    }),

    PiHard: {
      kind: 'PiHard0',
      version: CHECKER_VERSION,
      note: 'synthetic hard-checker suite proof marker',
    },
  };

  return {
    ...hard,
    ...overrides,
  };
}

export async function CheckHard0(hard) {
  const checker = 'CheckHard0';
  const ledger = [];

  const phases = [
    ['shape', `${checker}.input`, () => validateHardShape0(hard)],
    ['ValidatorCore', `${checker}.ValidatorCore`, () => validateValidatorCore0(hard.ValidatorCore)],
    ['checkerDescriptors', `${checker}.checkers`, () => validateHardCheckerDescriptors0(hard)],
    ['IfaceCheck', `${checker}.IfaceCheck`, () => validateIfaceCheck0(hard.IfaceCheck)],
    ['NFCheck', `${checker}.NFCheck`, () => validateNFCheck0(hard.NFCheck)],
    ['RowKeyCheck', `${checker}.RowKeyCheck`, () => validateRowKeyCheck0(hard.RowKeyCheck)],
    ['DupCheck', `${checker}.DupCheck`, () => validateDupCheck0(hard.DupCheck)],
    ['RouteCheck', `${checker}.RouteCheck`, () => validateRouteCheck0(hard.RouteCheck)],
    ['ProofRefCheck', `${checker}.ProofRefCheck`, () => validateProofRefCheck0(hard.ProofRefCheck)],
    ['HashCheck', `${checker}.HashCheck`, () => validateHashCheck0(hard.HashCheck)],
    ['NoMinCheck', `${checker}.NoMinCheck`, () => validateNoMinCheck0(hard.NoMinCheck)],
    ['ImportCheck', `${checker}.ImportCheck`, () => validateImportCheck0(hard.ImportCheck)],
    ['ReflectionCheck', `${checker}.ReflectionCheck`, () => validateReflectionCheck0(hard.ReflectionCheck)],
    ['BoundsCheck', `${checker}.BoundsCheck`, () => validateBoundsCheck0(hard.BoundsCheck)],
    ['DiagCheck', `${checker}.DiagCheck`, () => validateDiagCheck0(hard.DiagCheck)],
    ['noOpaqueProof', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(hard, ['HardCheck0'])],
    ['noHiddenMin', `${checker}.noHiddenMin`, () => validateNoHiddenExecutableMin0(hard, ['HardCheck0'])],
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
    kind: 'HardCheck0NF',
    checker,
    version: CHECKER_VERSION,
    checkerCount: HARD_CHECKER_FIELDS0.length,
    checkers: HARD_CHECKER_FIELDS0.map((field) => ({
      field,
      checkerId: hard[field].checkerId,
      digest: digestCanonical0(hard[field]),
    })),
    routePriority: hard.RouteCheck.priority,
    rowKeyFields: hard.RowKeyCheck.rowKeyFields,
    forbiddenSymbols: hard.NoMinCheck.forbiddenSymbols,
    forbiddenImportEdges: hard.ImportCheck.forbiddenEdges,
    piHardDigest: digestCanonical0(getPiHard0(hard)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateHardShape0(hard) {
  if (!isPlainObject(hard)) {
    return validationReject0([], 'HardCheck0 must be an object', {
      actual: typeof hard,
    });
  }

  if (hard.kind !== undefined && hard.kind !== 'HardCheck0') {
    return validationReject0(['kind'], 'HardCheck0 kind must be HardCheck0 when present', {
      actual: hard.kind,
    });
  }

  if (hard.version !== undefined && hard.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `HardCheck0 version must be ${CHECKER_VERSION} when present`, {
      actual: hard.version,
    });
  }

  for (const field of HARD_CHECKER_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(hard, field)) {
      return validationReject0([field], 'HardCheck0 is missing a required checker descriptor', {
        field,
      });
    }
  }

  if (getPiHard0(hard) === undefined) {
    return validationReject0(['PiHard'], 'HardCheck0 is missing PiHard or Πhard', null);
  }

  return validationAccept0({
    kind: 'HardCheck0ShapeNF',
  });
}

function validateValidatorCore0(descriptor) {
  const base = validateCheckerDescriptor0(descriptor, HARD_CHECKER_IDS0.ValidatorCore, ['ValidatorCore']);

  if (!base.ok) {
    return base;
  }

  if (!Array.isArray(descriptor.allowedOutputs)) {
    return validationReject0(['ValidatorCore', 'allowedOutputs'], 'ValidatorCore must list allowed outputs', null);
  }

  const allowed = new Set(descriptor.allowedOutputs);

  if (!allowed.has('accept') || !allowed.has('reject') || allowed.size !== 2) {
    return validationReject0(['ValidatorCore', 'allowedOutputs'], 'ValidatorCore outputs must be exactly accept and reject', {
      actual: descriptor.allowedOutputs,
    });
  }

  if (descriptor.unknownOutput !== false) {
    return validationReject0(['ValidatorCore', 'unknownOutput'], 'ValidatorCore must reject unknown outputs', {
      actual: descriptor.unknownOutput,
    });
  }

  return validationAccept0({
    kind: 'ValidatorCore0NF',
  });
}

function validateHardCheckerDescriptors0(hard) {
  const seenCheckerIds = new Set();

  for (const field of HARD_CHECKER_FIELDS0) {
    const expectedCheckerId = HARD_CHECKER_IDS0[field];
    const result = validateCheckerDescriptor0(hard[field], expectedCheckerId, [field]);

    if (!result.ok) {
      return result;
    }

    if (seenCheckerIds.has(hard[field].checkerId)) {
      return validationReject0([field, 'checkerId'], 'hard checker ids must be unique', {
        checkerId: hard[field].checkerId,
      });
    }

    seenCheckerIds.add(hard[field].checkerId);
  }

  return validationAccept0({
    kind: 'HardCheckerDescriptors0NF',
    checkerCount: HARD_CHECKER_FIELDS0.length,
  });
}

function validateCheckerDescriptor0(descriptor, expectedCheckerId, path) {
  if (!isPlainObject(descriptor)) {
    return validationReject0(path, 'checker descriptor must be an object', {
      actual: typeof descriptor,
    });
  }

  if (descriptor.kind !== undefined && descriptor.kind !== 'HardCheckerDescriptor0') {
    return validationReject0([...path, 'kind'], 'checker descriptor kind must be HardCheckerDescriptor0 when present', {
      actual: descriptor.kind,
    });
  }

  if (descriptor.version !== undefined && descriptor.version !== CHECKER_VERSION) {
    return validationReject0([...path, 'version'], `checker descriptor version must be ${CHECKER_VERSION} when present`, {
      actual: descriptor.version,
    });
  }

  if (descriptor.checkerId !== expectedCheckerId) {
    return validationReject0([...path, 'checkerId'], 'checker descriptor has the wrong checkerId', {
      expected: expectedCheckerId,
      actual: descriptor.checkerId,
    });
  }

  for (const flag of REQUIRED_DESCRIPTOR_FLAGS0) {
    if (descriptor[flag] !== true) {
      return validationReject0([...path, flag], `checker descriptor flag ${flag} must be true`, {
        actual: descriptor[flag],
      });
    }
  }

  if (!isPlainObject(descriptor.returns)) {
    return validationReject0([...path, 'returns'], 'checker descriptor must specify return shapes', null);
  }

  if (!arrayContainsAll0(descriptor.returns.accept, ['NF', 'Digest', 'Ledger'])) {
    return validationReject0([...path, 'returns', 'accept'], 'accept return shape must include NF, Digest, and Ledger', {
      actual: descriptor.returns.accept,
    });
  }

  if (!arrayContainsAll0(descriptor.returns.reject, ['Coord', 'Path', 'Witness', 'Digest'])) {
    return validationReject0([...path, 'returns', 'reject'], 'reject return shape must include Coord, Path, Witness, and Digest', {
      actual: descriptor.returns.reject,
    });
  }

  if (
    Object.prototype.hasOwnProperty.call(descriptor.returns, 'unknown') ||
    descriptor.unknownOutputs === true ||
    descriptor.unknownOutput === true
  ) {
    return validationReject0([...path, 'returns'], 'checker descriptor must not expose an unknown output', null);
  }

  if (descriptor.polynomialBound !== undefined) {
    const bound = descriptor.polynomialBound;

    if (!isPlainObject(bound)) {
      return validationReject0([...path, 'polynomialBound'], 'polynomialBound must be an object when present', null);
    }

    if (!Number.isInteger(bound.exponent) || bound.exponent <= 0) {
      return validationReject0([...path, 'polynomialBound', 'exponent'], 'polynomialBound exponent must be positive', {
        actual: bound.exponent,
      });
    }
  }

  return validationAccept0({
    kind: 'HardCheckerDescriptor0NF',
    checkerId: descriptor.checkerId,
  });
}

function validateIfaceCheck0(descriptor) {
  if (descriptor.singleSourceOfTruth !== true) {
    return validationReject0(['IfaceCheck', 'singleSourceOfTruth'], 'IfaceCheck must enforce a single interface dictionary source', null);
  }

  if (descriptor.namespaceCoherent !== true) {
    return validationReject0(['IfaceCheck', 'namespaceCoherent'], 'IfaceCheck must enforce namespace coherence', null);
  }

  if (!arrayContainsAll0(descriptor.requiredObjects, [
    'publicConstructors',
    'routeTokens',
    'checkerPredicates',
    'forbiddenSymbols',
    'bounds',
  ])) {
    return validationReject0(['IfaceCheck', 'requiredObjects'], 'IfaceCheck is missing required interface objects', {
      actual: descriptor.requiredObjects,
    });
  }

  return validationAccept0({
    kind: 'IfaceCheck0NF',
  });
}

function validateNFCheck0(descriptor) {
  for (const field of ['idempotent', 'canonicalBytes', 'transportProofs']) {
    if (descriptor[field] !== true) {
      return validationReject0(['NFCheck', field], `NFCheck must enforce ${field}`, {
        actual: descriptor[field],
      });
    }
  }

  return validationAccept0({
    kind: 'NFCheck0NF',
  });
}

function validateRowKeyCheck0(descriptor) {
  if (!Array.isArray(descriptor.rowKeyFields)) {
    return validationReject0(['RowKeyCheck', 'rowKeyFields'], 'RowKeyCheck must list row-key fields', null);
  }

  if (descriptor.rowKeyFields.length !== HARD_ROWKEY_FIELDS0.length) {
    return validationReject0(['RowKeyCheck', 'rowKeyFields'], 'RowKeyCheck must use exactly seventeen row-key fields', {
      expected: HARD_ROWKEY_FIELDS0.length,
      actual: descriptor.rowKeyFields.length,
    });
  }

  for (let index = 0; index < HARD_ROWKEY_FIELDS0.length; index += 1) {
    if (descriptor.rowKeyFields[index] !== HARD_ROWKEY_FIELDS0[index]) {
      return validationReject0(['RowKeyCheck', 'rowKeyFields', index], 'RowKeyCheck row-key field order mismatch', {
        expected: HARD_ROWKEY_FIELDS0[index],
        actual: descriptor.rowKeyFields[index],
      });
    }
  }

  if (descriptor.excludesSelectedRoute !== true) {
    return validationReject0(['RowKeyCheck', 'excludesSelectedRoute'], 'RowKeyCheck must exclude SelectedRoute from row identity', null);
  }

  return validationAccept0({
    kind: 'RowKeyCheck0NF',
    rowKeyFields: descriptor.rowKeyFields,
  });
}

function validateDupCheck0(descriptor) {
  if (descriptor.fullRowKeyComparison !== true) {
    return validationReject0(['DupCheck', 'fullRowKeyComparison'], 'DupCheck must compare full row keys', null);
  }

  if (descriptor.selectedRouteConflictReject !== true) {
    return validationReject0(['DupCheck', 'selectedRouteConflictReject'], 'DupCheck must reject conflicting selected routes', null);
  }

  return validationAccept0({
    kind: 'DupCheck0NF',
  });
}

function validateRouteCheck0(descriptor) {
  if (!Array.isArray(descriptor.priority)) {
    return validationReject0(['RouteCheck', 'priority'], 'RouteCheck priority must be an array', null);
  }

  if (descriptor.priority[0] !== 'Gain') {
    return validationReject0(['RouteCheck', 'priority', 0], 'RouteCheck must give Gain highest priority', {
      actual: descriptor.priority[0],
    });
  }

  if (!arrayContainsAll0(descriptor.priority, HARD_ROUTE_PRIORITY0)) {
    return validationReject0(['RouteCheck', 'priority'], 'RouteCheck priority is missing required routes', {
      actual: descriptor.priority,
    });
  }

  if (descriptor.noGainDowngrade !== true) {
    return validationReject0(['RouteCheck', 'noGainDowngrade'], 'RouteCheck must prevent gain downgrade', null);
  }

  if (descriptor.highestActiveRoute !== true) {
    return validationReject0(['RouteCheck', 'highestActiveRoute'], 'RouteCheck must select the highest active route', null);
  }

  return validationAccept0({
    kind: 'RouteCheck0NF',
    priority: descriptor.priority,
  });
}

function validateProofRefCheck0(descriptor) {
  if (!arrayContainsAll0(descriptor.allowedRefKinds, HARD_ALLOWED_PROOF_REF_KINDS0)) {
    return validationReject0(['ProofRefCheck', 'allowedRefKinds'], 'ProofRefCheck is missing allowed proof-reference kinds', {
      actual: descriptor.allowedRefKinds,
    });
  }

  if (descriptor.acyclic !== true) {
    return validationReject0(['ProofRefCheck', 'acyclic'], 'ProofRefCheck must enforce acyclic proof references', null);
  }

  if (descriptor.rejectsOpaque !== true) {
    return validationReject0(['ProofRefCheck', 'rejectsOpaque'], 'ProofRefCheck must reject opaque proof blobs', null);
  }

  if (descriptor.earlierRowOnly !== true) {
    return validationReject0(['ProofRefCheck', 'earlierRowOnly'], 'ProofRefCheck must restrict row references to earlier accepted row proofs', null);
  }

  return validationAccept0({
    kind: 'ProofRefCheck0NF',
  });
}

function validateHashCheck0(descriptor) {
  if (descriptor.hashAsIndexOnly !== true) {
    return validationReject0(['HashCheck', 'hashAsIndexOnly'], 'HashCheck must treat hashes only as indexes', null);
  }

  if (descriptor.fullKeyCompareAfterHash !== true && descriptor.canonicalByteCompareAfterHash !== true) {
    return validationReject0(['HashCheck', 'fullKeyCompareAfterHash'], 'HashCheck must compare full keys or canonical bytes after hash lookup', null);
  }

  if (descriptor.digestEqualityIsNotObjectEquality !== true) {
    return validationReject0(['HashCheck', 'digestEqualityIsNotObjectEquality'], 'HashCheck must reject digest equality as object equality', null);
  }

  return validationAccept0({
    kind: 'HashCheck0NF',
  });
}

function validateNoMinCheck0(descriptor) {
  if (!arrayContainsAll0(descriptor.expansionStages, HARD_NO_MIN_EXPANSION_STAGES0)) {
    return validationReject0(['NoMinCheck', 'expansionStages'], 'NoMinCheck must expand macros, aliases, generated templates, and imports', {
      actual: descriptor.expansionStages,
    });
  }

  if (!arrayContainsAll0(descriptor.occurrenceClasses, HARD_OCCURRENCE_CLASSES0)) {
    return validationReject0(['NoMinCheck', 'occurrenceClasses'], 'NoMinCheck must classify all required occurrence kinds', {
      actual: descriptor.occurrenceClasses,
    });
  }

  for (const symbol of HARD_FORBIDDEN_SYMBOLS0) {
    if (!Array.isArray(descriptor.forbiddenSymbols) || !descriptor.forbiddenSymbols.includes(symbol)) {
      return validationReject0(['NoMinCheck', 'forbiddenSymbols', symbol], 'NoMinCheck is missing a forbidden minimization symbol or alias', {
        symbol,
      });
    }
  }

  if (descriptor.rejectsAliases !== true) {
    return validationReject0(['NoMinCheck', 'rejectsAliases'], 'NoMinCheck must reject forbidden aliases', null);
  }

  if (descriptor.rejectsExecutableOnly !== true) {
    return validationReject0(['NoMinCheck', 'rejectsExecutableOnly'], 'NoMinCheck must classify executable occurrences before rejection', null);
  }

  return validationAccept0({
    kind: 'NoMinCheck0NF',
    forbiddenSymbolCount: descriptor.forbiddenSymbols.length,
  });
}

function validateImportCheck0(descriptor) {
  if (descriptor.acyclic !== true) {
    return validationReject0(['ImportCheck', 'acyclic'], 'ImportCheck must enforce acyclic imports', null);
  }

  if (!Array.isArray(descriptor.forbiddenEdges)) {
    return validationReject0(['ImportCheck', 'forbiddenEdges'], 'ImportCheck must list forbidden import edges', null);
  }

  const actual = new Set(descriptor.forbiddenEdges.map((edge) => edgeKey0(edge)));

  for (const edge of HARD_FORBIDDEN_IMPORT_EDGES0) {
    if (!actual.has(edgeKey0(edge))) {
      return validationReject0(['ImportCheck', 'forbiddenEdges'], 'ImportCheck is missing a forbidden import edge', {
        edge,
      });
    }
  }

  return validationAccept0({
    kind: 'ImportCheck0NF',
    forbiddenEdgeCount: descriptor.forbiddenEdges.length,
  });
}

function validateReflectionCheck0(descriptor) {
  if (descriptor.exact !== true) {
    return validationReject0(['ReflectionCheck', 'exact'], 'ReflectionCheck must enforce exact reflection', null);
  }

  if (descriptor.publicConclusion !== true) {
    return validationReject0(['ReflectionCheck', 'publicConclusion'], 'ReflectionCheck must expose public theorem conclusions', null);
  }

  if (descriptor.replayable !== true) {
    return validationReject0(['ReflectionCheck', 'replayable'], 'ReflectionCheck must be replayable', null);
  }

  return validationAccept0({
    kind: 'ReflectionCheck0NF',
  });
}

function validateBoundsCheck0(descriptor) {
  if (descriptor.polynomialBounds !== true) {
    return validationReject0(['BoundsCheck', 'polynomialBounds'], 'BoundsCheck must enforce polynomial bounds', null);
  }

  if (descriptor.finiteSchedules !== true) {
    return validationReject0(['BoundsCheck', 'finiteSchedules'], 'BoundsCheck must enforce finite schedules', null);
  }

  if (descriptor.noPrivateSchedule !== true) {
    return validationReject0(['BoundsCheck', 'noPrivateSchedule'], 'BoundsCheck must reject private schedule enlargement', null);
  }

  return validationAccept0({
    kind: 'BoundsCheck0NF',
  });
}

function validateDiagCheck0(descriptor) {
  if (descriptor.uniqueFirstFailure !== true) {
    return validationReject0(['DiagCheck', 'uniqueFirstFailure'], 'DiagCheck must emit a unique first failure', null);
  }

  if (descriptor.replayable !== true) {
    return validationReject0(['DiagCheck', 'replayable'], 'DiagCheck must emit replayable diagnostics', null);
  }

  if (descriptor.noUnknownOutput !== true) {
    return validationReject0(['DiagCheck', 'noUnknownOutput'], 'DiagCheck must reject unknown outputs', null);
  }

  return validationAccept0({
    kind: 'DiagCheck0NF',
  });
}

function validateNoOpaqueProof0(value, path) {
  const hit = findOpaqueProof0(value, path);

  if (hit !== null) {
    return validationReject0(hit.path, 'opaque proof material is not allowed in HardCheck0', hit);
  }

  return validationAccept0({
    kind: 'NoOpaqueProof0NF',
  });
}

function validateNoHiddenExecutableMin0(value, path) {
  const hit = findForbiddenExecutableUse0(value, path, false);

  if (hit !== null) {
    return validationReject0(hit.path, 'forbidden minimization symbol appears in executable position', hit);
  }

  return validationAccept0({
    kind: 'HardNoHiddenExecutableMin0NF',
  });
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

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && HARD_FORBIDDEN_SYMBOLS0.includes(value)) {
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

function getPiHard0(hard) {
  return hard.PiHard ?? hard['Πhard'] ?? hard.piHard;
}

function arrayContainsAll0(actual, required) {
  if (!Array.isArray(actual)) {
    return false;
  }

  return required.every((entry) => actual.includes(entry));
}

function edgeKey0(edge) {
  if (Array.isArray(edge)) {
    return `${String(edge[0])}->${String(edge[1])}`;
  }

  if (isPlainObject(edge)) {
    return `${String(edge.from ?? edge.src)}->${String(edge.to ?? edge.dst)}`;
  }

  return String(edge);
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
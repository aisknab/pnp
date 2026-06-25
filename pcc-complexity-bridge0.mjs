import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

const CHECKER_VERSION = 0;

export const COMPLEXITY_BRIDGE_SCOPE0 = Object.freeze({
  kind: 'ComplexityBridgeScope0',
  version: CHECKER_VERSION,
  scope: 'guarded-standard-complexity-bridge',
  satInPAssumptionRequired: true,
  satNPCompletenessDependencyRequired: true,
  pSubsetNPDependencyRequired: true,
  polynomialReductionClosureRequired: true,
  conditionalEqualityOnly: true,
  unconditionalEqualityForbidden: true,
  cookLevinFormalizationIncluded: false,
  standardTheoremDependencyTrustRequired: true,
  publicTheoremEmissionNotAllowed: true,
});

export const COMPLEXITY_BRIDGE_POLICY0 = Object.freeze({
  kind: 'ComplexityBridgePolicy0',
  version: CHECKER_VERSION,
  exactSATinPSourceBindingRequired: true,
  exactStandardBasisRequired: true,
  exactConditionalClaimRequired: true,
  deterministicPolynomialManyOneReductionsOnly: true,
  derivesNPSubsetPFromSATCompletenessAndSATinP: true,
  derivesPSubsetNPFromDeterministicSimulation: true,
  equalityRequiresBothInclusions: true,
  callerTruthAssertionsForbidden: true,
  unrestrictedComplexityTheoremSoundnessNotClaimed: true,
  publicTheoremEmissionNotAllowed: true,
});

export const STANDARD_COMPLEXITY_BASIS0 = Object.freeze({
  kind: 'StandardComplexityBasis0',
  version: CHECKER_VERSION,
  classDefinitions: Object.freeze({
    P: Object.freeze({
      id: 'P',
      machineModel: 'deterministic-turing-machine',
      resource: 'polynomial-time',
      languageDecision: true,
    }),
    NP: Object.freeze({
      id: 'NP',
      machineModel: 'nondeterministic-turing-machine',
      resource: 'polynomial-time',
      languageDecision: true,
    }),
  }),
  pSubsetNP: Object.freeze({
    theoremId: 'DeterministicSimulationInNP',
    premiseClass: 'P',
    conclusionClass: 'NP',
    simulation: 'deterministic-machine-is-a-special-case-of-nondeterministic-machine',
    inclusion: 'P subseteq NP',
  }),
  satNPCompleteness: Object.freeze({
    theoremId: 'CookLevin',
    language: 'SAT',
    membershipClass: 'NP',
    membership: true,
    hardnessClass: 'NP',
    hardness: true,
    reductionKind: 'deterministic-polynomial-time-many-one',
    quantifiedSource: 'every language in NP',
    conclusion: 'SAT is NP-complete',
    theoremTreatment: 'trusted-standard-mathematical-dependency',
    formalProofIncluded: false,
  }),
  reductionClosure: Object.freeze({
    theoremId: 'PolynomialReductionToPClosure',
    reductionKind: 'deterministic-polynomial-time-many-one',
    premise: 'L reduces to A and A is in P',
    conclusion: 'L is in P',
    compositionDeterministic: true,
    compositionPolynomial: true,
  }),
  equalityRule: Object.freeze({
    theoremId: 'MutualInclusionClassEquality',
    premises: Object.freeze(['NP subseteq P', 'P subseteq NP']),
    conclusion: 'P = NP',
  }),
});

export const CONDITIONAL_COMPLEXITY_CLAIM0 = Object.freeze({
  kind: 'ConditionalComplexityEqualityClaim0',
  version: CHECKER_VERSION,
  assumptions: Object.freeze(['SAT in P', 'SAT is NP-complete']),
  conclusion: 'P = NP',
  conditionalOnPackageAcceptance: true,
  usesSATinP: true,
  usesSATNPCompleteness: true,
  usesPSubsetNP: true,
  usesPolynomialReductionClosure: true,
  noUnconditionalClaim: true,
  publiclyActive: false,
});

export function makeComplexityBridgeInput0({
  sourceNodeId = 'Final.AcceptedPackageImpliesSATinP',
  sourceDerivationDigest = digestCanonical0({
    kind: 'SyntheticSATReductionDerivation0',
    version: CHECKER_VERSION,
  }),
  Basis = STANDARD_COMPLEXITY_BASIS0,
  Claim = CONDITIONAL_COMPLEXITY_CLAIM0,
} = {}) {
  return Object.freeze({
    kind: 'ComplexityBridgeInput0',
    version: CHECKER_VERSION,
    SATInP: Object.freeze({
      kind: 'SATInPBoundSource0',
      version: CHECKER_VERSION,
      language: 'SAT',
      classId: 'P',
      conclusion: 'SAT in P',
      sourceNodeId,
      sourceDerivationDigest,
      conditionalOnPackageAcceptance: true,
      publiclyActive: false,
    }),
    Basis,
    Claim,
    Scope: { ...COMPLEXITY_BRIDGE_SCOPE0 },
    Policy: { ...COMPLEXITY_BRIDGE_POLICY0 },
  });
}

export async function CheckComplexityBridge0(input) {
  const checker = 'CheckComplexityBridge0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const satSource = validateSATInPSource0(input.SATInP);
  ledger.push(makeLedgerEntry0(
    'satInPSource',
    satSource.ok,
    satSource.nf ?? satSource.witness,
  ));
  if (!satSource.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.SATInP`,
      satSource,
      ledger,
    );
  }

  const basis = validateStandardBasis0(input.Basis);
  ledger.push(makeLedgerEntry0(
    'standardComplexityBasis',
    basis.ok,
    basis.nf ?? basis.witness,
  ));
  if (!basis.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.Basis`,
      basis,
      ledger,
    );
  }

  const claim = validateConditionalClaim0(input.Claim);
  ledger.push(makeLedgerEntry0(
    'conditionalClaim',
    claim.ok,
    claim.nf ?? claim.witness,
  ));
  if (!claim.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.Claim`,
      claim,
      ledger,
    );
  }

  const derivation = makeBridgeDerivation0(input);
  ledger.push(makeLedgerEntry0('bridgeDerivation', true, derivation));

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'ComplexityBridge0NF',
      checker,
      version: CHECKER_VERSION,
      satInPAssumptionChecked: true,
      satNPCompletenessDependencyChecked: true,
      polynomialReductionClosureChecked: true,
      pSubsetNPDependencyChecked: true,
      npSubsetPDerived: true,
      pSubsetNPDerived: true,
      conditionalPEqualsNPDerived: true,
      unconditionalPEqualsNPDerived: false,
      conditionalOnPackageAcceptance: true,
      noUnconditionalClaim: true,
      publiclyActive: false,
      publicTheoremEmissionAllowed: false,
      guardedStandardComplexityBridgeReady: true,
      cookLevinFormalizationIncluded: false,
      standardTheoremDependencyTrustRequired: true,
      unrestrictedComplexityTheoremSoundnessNotClaimed: true,
      sourceNodeId: input.SATInP.sourceNodeId,
      sourceDerivationDigest: input.SATInP.sourceDerivationDigest,
      basisDigest: digestCanonical0(input.Basis),
      claimDigest: digestCanonical0(input.Claim),
      derivation,
      derivationDigest: digestCanonical0(derivation),
      scopeDigest: digestCanonical0(input.Scope),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'complexity bridge input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'ComplexityBridgeInput0') {
    return validationReject0(
      ['kind'],
      'complexity bridge input kind must be ComplexityBridgeInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `complexity bridge input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of ['SATInP', 'Basis', 'Claim', 'Scope', 'Policy']) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'complexity bridge input is missing a required field',
        { field },
      );
    }
  }
  for (const field of ['SATInP', 'Basis', 'Claim', 'Scope', 'Policy']) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'complexity bridge dependency surface must be an object',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (!sameCanonical0(input.Scope, COMPLEXITY_BRIDGE_SCOPE0)) {
    return validationReject0(
      ['Scope'],
      'complexity bridge scope must match the guarded fail-closed scope',
      { expected: COMPLEXITY_BRIDGE_SCOPE0, actual: input.Scope },
    );
  }
  if (!sameCanonical0(input.Policy, COMPLEXITY_BRIDGE_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'complexity bridge policy must match the guarded fail-closed policy',
      { expected: COMPLEXITY_BRIDGE_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'SATInP',
    'Basis',
    'Claim',
    'Scope',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'complexity bridge checker rejects caller-supplied truth or readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'ComplexityBridgeInputShape0NF',
  });
}

function validateSATInPSource0(source) {
  if (!isPlainObject0(source)) {
    return validationReject0(
      ['SATInP'],
      'SAT-in-P source must be an object',
      { actual: typeof source },
    );
  }
  const expected = {
    kind: 'SATInPBoundSource0',
    version: CHECKER_VERSION,
    language: 'SAT',
    classId: 'P',
    conclusion: 'SAT in P',
    sourceNodeId: 'Final.AcceptedPackageImpliesSATinP',
    conditionalOnPackageAcceptance: true,
    publiclyActive: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (source[field] !== value) {
      return validationReject0(
        ['SATInP', field],
        'SAT-in-P source field mismatch',
        { field, expected: value, actual: source[field] },
      );
    }
  }
  if (!isDigest0(source.sourceDerivationDigest)) {
    return validationReject0(
      ['SATInP', 'sourceDerivationDigest'],
      'SAT-in-P source must bind a SHA256 derivation digest',
      { actual: source.sourceDerivationDigest },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'language',
    'classId',
    'conclusion',
    'sourceNodeId',
    'sourceDerivationDigest',
    'conditionalOnPackageAcceptance',
    'publiclyActive',
  ]);
  const unexpected = Object.keys(source).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['SATInP', unexpected[0]],
      'SAT-in-P source rejects caller-supplied truth metadata',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'SATInPBoundSource0NF',
    sourceNodeId: source.sourceNodeId,
    sourceDerivationDigest: source.sourceDerivationDigest,
  });
}

function validateStandardBasis0(basis) {
  if (!sameCanonical0(basis, STANDARD_COMPLEXITY_BASIS0)) {
    return validationReject0(
      ['Basis'],
      'complexity bridge basis must exactly match the version-zero standard dependency basis',
      { expected: STANDARD_COMPLEXITY_BASIS0, actual: basis },
    );
  }
  return validationAccept0({
    kind: 'StandardComplexityBasis0NF',
    satCompletenessTheoremId: basis.satNPCompleteness.theoremId,
    reductionKind: basis.satNPCompleteness.reductionKind,
    formalProofIncluded: basis.satNPCompleteness.formalProofIncluded,
  });
}

function validateConditionalClaim0(claim) {
  if (!isPlainObject0(claim)) {
    return validationReject0(
      ['Claim'],
      'conditional complexity claim must be an object',
      { actual: typeof claim },
    );
  }
  if (!sameCanonical0(claim.assumptions, ['SAT in P', 'SAT is NP-complete'])) {
    return validationReject0(
      ['Claim', 'assumptions'],
      'conditional complexity claim requires exactly SAT in P and SAT NP-completeness',
      {
        expected: ['SAT in P', 'SAT is NP-complete'],
        actual: claim.assumptions,
      },
    );
  }
  if (!sameCanonical0(claim, CONDITIONAL_COMPLEXITY_CLAIM0)) {
    return validationReject0(
      ['Claim'],
      'conditional complexity claim must exactly match the guarded version-zero claim',
      { expected: CONDITIONAL_COMPLEXITY_CLAIM0, actual: claim },
    );
  }
  return validationAccept0({
    kind: 'ConditionalComplexityEqualityClaim0NF',
    assumptions: [...claim.assumptions],
    conclusion: claim.conclusion,
    noUnconditionalClaim: true,
  });
}

function makeBridgeDerivation0(input) {
  const steps = [
    Object.freeze({
      id: 'Complexity.SATInP',
      premises: Object.freeze([]),
      conclusion: 'SAT in P',
      dependencyDigest: input.SATInP.sourceDerivationDigest,
    }),
    Object.freeze({
      id: 'Complexity.SATNPComplete',
      premises: Object.freeze([]),
      conclusion: 'SAT is NP-complete',
      dependencyDigest: digestCanonical0(input.Basis.satNPCompleteness),
    }),
    Object.freeze({
      id: 'Complexity.NPSubsetP',
      premises: Object.freeze([
        'Complexity.SATInP',
        'Complexity.SATNPComplete',
      ]),
      conclusion: 'NP subseteq P',
      dependencyDigest: digestCanonical0(input.Basis.reductionClosure),
    }),
    Object.freeze({
      id: 'Complexity.PSubsetNP',
      premises: Object.freeze([]),
      conclusion: 'P subseteq NP',
      dependencyDigest: digestCanonical0(input.Basis.pSubsetNP),
    }),
    Object.freeze({
      id: 'Complexity.ConditionalPEqualsNP',
      premises: Object.freeze([
        'Complexity.NPSubsetP',
        'Complexity.PSubsetNP',
      ]),
      conclusion: 'P = NP',
      dependencyDigest: digestCanonical0(input.Basis.equalityRule),
      conditionalOnPackageAcceptance: true,
      publiclyActive: false,
    }),
  ];
  return Object.freeze({
    kind: 'ComplexityBridgeDerivation0',
    version: CHECKER_VERSION,
    steps: Object.freeze(steps),
    terminalStepId: 'Complexity.ConditionalPEqualsNP',
    conditionalOnPackageAcceptance: true,
    noUnconditionalClaim: true,
    publiclyActive: false,
  });
}

function isDigest0(value) {
  return isPlainObject0(value)
    && value.alg === 'SHA256'
    && typeof value.hex === 'string'
    && /^[0-9a-f]{64}$/u.test(value.hex);
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

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

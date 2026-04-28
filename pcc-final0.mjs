import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckFinalIntegration0,
  makeSyntheticFinalIntegration0,
} from './pcc-final-framework0.mjs';

const CHECKER_VERSION = 0;

export const FINAL0_REQUIRED_FIELDS0 = Object.freeze([
  'FinalIntegration',
  'PCCMinBridge',
  'AcceptedPackageImpliesSATinP',
  'AcceptedPackageImpliesPEqualsNP',
  'GeneratedPackageSufficiency',
  'FinalPublicTheorem',
  'PolynomialBound',
  'ReflectionCert',
  'NoHiddenMinCert',
]);

export const FINAL0_THEOREM_IDS0 = Object.freeze([
  'PackageAcceptanceImpliesSATinP',
  'PackageAcceptanceImpliesPEqualsNP',
  'GeneratedPackageSufficiency',
  'GeneratedPackageAcceptanceImpliesPEqualsNP',
]);

export const ROWFAMFINAL_REQUIRED_ROWS0 = Object.freeze([
  'FinalIntegration',
  'FrameworkMatch',
  'SATDecision',
  'SATBounds',
  'PCCMinBridge',
  'PackageAcceptanceImpliesSATinP',
  'PackageAcceptanceImpliesPEqualsNP',
  'GeneratedPackageSufficiency',
  'FinalPublicTheorem',
  'PolynomialBound',
  'ReflectionCert',
  'NoHiddenMinCert',
]);

export const FINAL0_FORBIDDEN_EXEC_SYMBOLS0 = Object.freeze([
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

export const FINAL0_EXPANSION_STAGES0 = Object.freeze([
  'macros',
  'aliases',
  'generatedTemplates',
  'imports',
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

export function makeSyntheticFinalTheorem0({
  finalIntegration = makeSyntheticFinalIntegration0(),
  overrides = {},
} = {}) {
  const finalTheorem = {
    kind: 'FinalTheorem0',
    version: CHECKER_VERSION,

    FinalIntegration: finalIntegration,

    PCCMinBridge: {
      kind: 'PCCMinBridge0',
      version: CHECKER_VERSION,
      exactMinimizer: 'PCCMin',
      residualBandBound: 4,
      residualBandPolynomial: true,
      lockedNANDReduction: true,
      satReduction: true,
      usesExactMinimum: true,
      rejectsApproximateMinimum: true,
      decisionComparator: 'minSize>baseline',
      sourceTheorems: [
        'ResidualBandExactMinimization',
        'LockedNANDThreshold',
        'SATDecision',
      ],
    },

    AcceptedPackageImpliesSATinP: {
      kind: 'FinalImplication0',
      id: 'PackageAcceptanceImpliesSATinP',
      assumptions: [
        'CheckPCCPackexp(P)=accept',
        'CheckFinalIntegration0(FinalIntPack)=accept',
        'Lambda(WNAND_phi)<=4',
      ],
      conclusion: 'SAT in P',
      public: true,
      polynomial: true,
      usesPCCMinBridge: true,
      usesSATDecision: true,
    },

    AcceptedPackageImpliesPEqualsNP: {
      kind: 'FinalImplication0',
      id: 'PackageAcceptanceImpliesPEqualsNP',
      assumptions: [
        'SAT in P',
        'SAT is NP-complete',
      ],
      conclusion: 'P = NP',
      public: true,
      conditionalOnPackageAcceptance: true,
      usesSATinP: true,
      noUnconditionalClaim: true,
    },

    GeneratedPackageSufficiency: {
      kind: 'GeneratedPackageSufficiency0',
      id: 'GeneratedPackageSufficiency',
      generatorUntrusted: true,
      materializedOutputOnly: true,
      canonicalByteEquality: true,
      noDigestOnlyEquality: true,
      linksFinalAcceptance: true,
      assumption: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      conclusion: 'P = NP',
    },

    FinalPublicTheorem: {
      kind: 'FinalPublicTheorem0',
      id: 'GeneratedPackageAcceptanceImpliesPEqualsNP',
      theorem: 'CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP',
      publicConclusion: true,
      noClaimBeforeAccept: true,
      finalVerdict: 'conditional',
      exportedStatement: {
        antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
        consequent: 'P = NP',
      },
    },

    PolynomialBound: {
      kind: 'FinalPolynomialBound0',
      version: CHECKER_VERSION,
      input: 'BooleanCircuit',
      converterPolynomial: true,
      lockedBuilderPolynomial: true,
      residualBandPolynomial: true,
      satDecisionPolynomial: true,
      exponent: 42,
      residualSlackBound: 4,
      noPrivateSchedule: true,
    },

    ReflectionCert: {
      kind: 'FinalReflectionCert0',
      version: CHECKER_VERSION,
      exact: true,
      publicConclusion: true,
      replayable: true,
      reflectedTheorems: FINAL0_THEOREM_IDS0,
      proofRef: {
        kind: 'ProofRef0',
        refKind: 'ReflectionInstance',
        id: 'Final.Theorem.Reflection',
      },
    },

    NoHiddenMinCert: {
      kind: 'FinalNoHiddenMinCert0',
      version: CHECKER_VERSION,
      expansionStages: FINAL0_EXPANSION_STAGES0,
      forbiddenSymbols: FINAL0_FORBIDDEN_EXEC_SYMBOLS0,
      occurrences: [
        {
          identifier: 'minimumEquivalent',
          expandedIdentifier: 'µ*',
          occurrenceClass: 'AssumeOnly',
          source: 'definition of exact minimum',
        },
        {
          identifier: 'PCCMin',
          occurrenceClass: 'ExecCall',
          source: 'accepted residual-band minimizer',
        },
      ],
      importsScanned: true,
      macrosExpanded: true,
      aliasesExpanded: true,
      generatedTemplatesExpanded: true,
      expandedArtifacts: [],
    },

    PiFinal: {
      kind: 'PiFinal0',
      version: CHECKER_VERSION,
      note: 'synthetic final theorem proof marker',
    },
  };

  return {
    ...finalTheorem,
    ...overrides,
  };
}

export function makeSyntheticRowFamFinal0(finalTheorem = makeSyntheticFinalTheorem0(), overrides = {}) {
  return {
    kind: 'RowFamFinal0',
    version: CHECKER_VERSION,
    FinalTheorem: finalTheorem,
    rows: ROWFAMFINAL_REQUIRED_ROWS0.map((rowKind, index) => ({
      kind: 'RowFamFinalEntry0',
      version: CHECKER_VERSION,
      rowId: `Final.${rowKind}`,
      rowKind,
      family: 'Final',
      packageId: 'PFinal',
      selectedRoute: 'Accept',
      activeRouteSet: [
        'Accept',
      ],
      candidateRoutes: [
        'Accept',
      ],
      proofRef: {
        kind: 'ProofRef0',
        refKind: 'ReflectionInstance',
        id: `Final.${rowKind}.proof`,
      },
      boundsRef: {
        kind: 'BoundsRef0',
        id: `Final.${rowKind}.bounds`,
        finite: true,
        polynomial: true,
      },
      index,
    })),
    Coverage: {
      kind: 'RowFamFinalCoverage0',
      requiredRows: ROWFAMFINAL_REQUIRED_ROWS0,
    },
    PiRowFamFinal: {
      kind: 'PiRowFamFinal0',
      version: CHECKER_VERSION,
      note: 'synthetic RowFamFinal proof marker',
    },
    ...overrides,
  };
}

export async function CheckFinal0(finalTheorem) {
  const checker = 'CheckFinal0';
  const ledger = [];

  const shape = validateFinalShape0(finalTheorem);

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

  const finalIntegrationRecord = await CheckFinalIntegration0(finalTheorem.FinalIntegration);
  const finalIntegration = recordToValidation0(finalIntegrationRecord, ['FinalIntegration']);

  ledger.push({
    phase: 'CheckFinalIntegration0',
    status: finalIntegration.ok ? 'pass' : 'fail',
    digest: finalIntegrationRecord.Digest ?? finalIntegrationRecord.digest ?? digestCanonical0(finalIntegrationRecord),
  });

  if (!finalIntegration.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.FinalIntegration`,
      path: finalIntegration.path,
      witness: finalIntegration.witness,
      ledger,
    });
  }

  const phases = [
    ['pccMinBridge', `${checker}.PCCMinBridge`, () => validatePCCMinBridge0(finalTheorem.PCCMinBridge)],
    ['satInP', `${checker}.SATinP`, () => validateSATinPImplication0(finalTheorem.AcceptedPackageImpliesSATinP)],
    ['pEqualsNP', `${checker}.PEqualsNP`, () => validatePEqualsNPImplication0(finalTheorem.AcceptedPackageImpliesPEqualsNP)],
    ['generatedSufficiency', `${checker}.GeneratedPackageSufficiency`, () => validateGeneratedSufficiency0(finalTheorem.GeneratedPackageSufficiency)],
    ['publicTheorem', `${checker}.FinalPublicTheorem`, () => validateFinalPublicTheorem0(finalTheorem.FinalPublicTheorem)],
    ['polynomialBound', `${checker}.PolynomialBound`, () => validateFinalPolynomialBound0(finalTheorem.PolynomialBound)],
    ['reflection', `${checker}.ReflectionCert`, () => validateFinalReflectionCert0(finalTheorem.ReflectionCert)],
    ['noHiddenMinMetadata', `${checker}.NoHiddenMinCert`, () => validateFinalNoHiddenMinMetadata0(finalTheorem.NoHiddenMinCert)],
    ['noHiddenMin', `${checker}.noHiddenMin`, () => validateNoHiddenExecutableMin0(finalTheorem, ['FinalTheorem0'])],
    ['opaque', `${checker}.opaqueProof`, () => validateNoOpaqueProof0(finalTheorem, ['FinalTheorem0'])],
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
    kind: 'FinalTheorem0NF',
    checker,
    version: CHECKER_VERSION,
    theoremIds: FINAL0_THEOREM_IDS0,
    publicTheorem: finalTheorem.FinalPublicTheorem.theorem,
    exportedStatement: finalTheorem.FinalPublicTheorem.exportedStatement,
    residualSlackBound: finalTheorem.PCCMinBridge.residualBandBound,
    polynomialExponent: finalTheorem.PolynomialBound.exponent,
    finalIntegrationDigest: finalIntegrationRecord.Digest ?? finalIntegrationRecord.digest,
    piFinalDigest: digestCanonical0(getPiFinal0(finalTheorem)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function CheckRowFamFinal0(rowFam) {
  const checker = 'CheckRowFamFinal0';
  const ledger = [];

  const shape = validateRowFamFinalShape0(rowFam);

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

  const finalRecord = await CheckFinal0(rowFam.FinalTheorem);
  const finalResult = recordToValidation0(finalRecord, ['FinalTheorem']);

  ledger.push({
    phase: 'CheckFinal0',
    status: finalResult.ok ? 'pass' : 'fail',
    digest: finalRecord.Digest ?? finalRecord.digest ?? digestCanonical0(finalRecord),
  });

  if (!finalResult.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.FinalTheorem`,
      path: finalResult.path,
      witness: finalResult.witness,
      ledger,
    });
  }

  const coverage = validateRowFamFinalCoverage0(rowFam);

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

  const rows = validateRowFamFinalRows0(rowFam);

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

  const noHiddenMin = validateNoHiddenExecutableMin0(rowFam, ['RowFamFinal0']);

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

  const noOpaque = validateNoOpaqueProof0(rowFam, ['RowFamFinal0']);

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
    kind: 'RowFamFinal0NF',
    checker,
    version: CHECKER_VERSION,
    rowCount: rowFam.rows.length,
    requiredRows: ROWFAMFINAL_REQUIRED_ROWS0,
    finalDigest: finalRecord.Digest,
    piRowFamFinalDigest: digestCanonical0(getPiRowFamFinal0(rowFam)),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

function validateFinalShape0(finalTheorem) {
  if (!isPlainObject(finalTheorem)) {
    return validationReject0([], 'FinalTheorem0 must be an object', {
      actual: typeof finalTheorem,
    });
  }

  if (finalTheorem.kind !== undefined && finalTheorem.kind !== 'FinalTheorem0') {
    return validationReject0(['kind'], 'FinalTheorem0 kind must be FinalTheorem0 when present', {
      actual: finalTheorem.kind,
    });
  }

  if (finalTheorem.version !== undefined && finalTheorem.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `FinalTheorem0 version must be ${CHECKER_VERSION} when present`, {
      actual: finalTheorem.version,
    });
  }

  for (const field of FINAL0_REQUIRED_FIELDS0) {
    if (!Object.prototype.hasOwnProperty.call(finalTheorem, field)) {
      return validationReject0([field], 'FinalTheorem0 is missing a required field', {
        field,
      });
    }
  }

  if (getPiFinal0(finalTheorem) === undefined) {
    return validationReject0(['PiFinal'], 'FinalTheorem0 is missing PiFinal or Πfinal', null);
  }

  return validationAccept0({
    kind: 'FinalShape0NF',
  });
}

function validatePCCMinBridge0(bridge) {
  if (!isPlainObject(bridge)) {
    return validationReject0(['PCCMinBridge'], 'PCCMinBridge must be an object', {
      actual: typeof bridge,
    });
  }

  if (bridge.exactMinimizer !== 'PCCMin') {
    return validationReject0(['PCCMinBridge', 'exactMinimizer'], 'PCCMinBridge exactMinimizer must be PCCMin', {
      actual: bridge.exactMinimizer,
    });
  }

  if (!Number.isInteger(bridge.residualBandBound) || bridge.residualBandBound < 0 || bridge.residualBandBound > 4) {
    return validationReject0(['PCCMinBridge', 'residualBandBound'], 'PCCMinBridge residualBandBound must be an integer at most four', {
      actual: bridge.residualBandBound,
    });
  }

  for (const field of [
    'residualBandPolynomial',
    'lockedNANDReduction',
    'satReduction',
    'usesExactMinimum',
    'rejectsApproximateMinimum',
  ]) {
    if (bridge[field] !== true) {
      return validationReject0(['PCCMinBridge', field], `PCCMinBridge must certify ${field}`, {
        actual: bridge[field],
      });
    }
  }

  if (bridge.decisionComparator !== 'minSize>baseline') {
    return validationReject0(['PCCMinBridge', 'decisionComparator'], 'PCCMinBridge comparator must be minSize>baseline', {
      actual: bridge.decisionComparator,
    });
  }

  return validationAccept0({
    kind: 'PCCMinBridge0NF',
    residualBandBound: bridge.residualBandBound,
  });
}

function validateSATinPImplication0(theorem) {
  if (!isPlainObject(theorem)) {
    return validationReject0(['AcceptedPackageImpliesSATinP'], 'AcceptedPackageImpliesSATinP must be an object', {
      actual: typeof theorem,
    });
  }

  if (theorem.id !== 'PackageAcceptanceImpliesSATinP') {
    return validationReject0(['AcceptedPackageImpliesSATinP', 'id'], 'SAT in P implication id mismatch', {
      actual: theorem.id,
    });
  }

  if (!Array.isArray(theorem.assumptions) || !theorem.assumptions.includes('CheckPCCPackexp(P)=accept')) {
    return validationReject0(['AcceptedPackageImpliesSATinP', 'assumptions'], 'SAT in P implication must be conditional on package acceptance', {
      actual: theorem.assumptions,
    });
  }

  if (theorem.conclusion !== 'SAT in P') {
    return validationReject0(['AcceptedPackageImpliesSATinP', 'conclusion'], 'SAT in P implication conclusion mismatch', {
      actual: theorem.conclusion,
    });
  }

  for (const field of [
    'public',
    'polynomial',
    'usesPCCMinBridge',
    'usesSATDecision',
  ]) {
    if (theorem[field] !== true) {
      return validationReject0(['AcceptedPackageImpliesSATinP', field], `SAT in P implication must certify ${field}`, {
        actual: theorem[field],
      });
    }
  }

  return validationAccept0({
    kind: 'SATinPImplication0NF',
  });
}

function validatePEqualsNPImplication0(theorem) {
  if (!isPlainObject(theorem)) {
    return validationReject0(['AcceptedPackageImpliesPEqualsNP'], 'AcceptedPackageImpliesPEqualsNP must be an object', {
      actual: typeof theorem,
    });
  }

  if (theorem.id !== 'PackageAcceptanceImpliesPEqualsNP') {
    return validationReject0(['AcceptedPackageImpliesPEqualsNP', 'id'], 'P equals NP implication id mismatch', {
      actual: theorem.id,
    });
  }

  if (!Array.isArray(theorem.assumptions) || !theorem.assumptions.includes('SAT in P')) {
    return validationReject0(['AcceptedPackageImpliesPEqualsNP', 'assumptions'], 'P equals NP implication must assume SAT in P', {
      actual: theorem.assumptions,
    });
  }

  if (theorem.conclusion !== 'P = NP') {
    return validationReject0(['AcceptedPackageImpliesPEqualsNP', 'conclusion'], 'P equals NP implication conclusion mismatch', {
      actual: theorem.conclusion,
    });
  }

  for (const field of [
    'public',
    'conditionalOnPackageAcceptance',
    'usesSATinP',
    'noUnconditionalClaim',
  ]) {
    if (theorem[field] !== true) {
      return validationReject0(['AcceptedPackageImpliesPEqualsNP', field], `P equals NP implication must certify ${field}`, {
        actual: theorem[field],
      });
    }
  }

  return validationAccept0({
    kind: 'PEqualsNPImplication0NF',
  });
}

function validateGeneratedSufficiency0(theorem) {
  if (!isPlainObject(theorem)) {
    return validationReject0(['GeneratedPackageSufficiency'], 'GeneratedPackageSufficiency must be an object', {
      actual: typeof theorem,
    });
  }

  if (theorem.id !== 'GeneratedPackageSufficiency') {
    return validationReject0(['GeneratedPackageSufficiency', 'id'], 'GeneratedPackageSufficiency id mismatch', {
      actual: theorem.id,
    });
  }

  for (const field of [
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
    'linksFinalAcceptance',
  ]) {
    if (theorem[field] !== true) {
      return validationReject0(['GeneratedPackageSufficiency', field], `GeneratedPackageSufficiency must certify ${field}`, {
        actual: theorem[field],
      });
    }
  }

  if (theorem.assumption !== 'CheckPCCPackexp(GeneratePCCPack())=accept') {
    return validationReject0(['GeneratedPackageSufficiency', 'assumption'], 'GeneratedPackageSufficiency assumption mismatch', {
      actual: theorem.assumption,
    });
  }

  if (theorem.conclusion !== 'P = NP') {
    return validationReject0(['GeneratedPackageSufficiency', 'conclusion'], 'GeneratedPackageSufficiency conclusion mismatch', {
      actual: theorem.conclusion,
    });
  }

  return validationAccept0({
    kind: 'GeneratedPackageSufficiency0NF',
  });
}

function validateFinalPublicTheorem0(theorem) {
  if (!isPlainObject(theorem)) {
    return validationReject0(['FinalPublicTheorem'], 'FinalPublicTheorem must be an object', {
      actual: typeof theorem,
    });
  }

  if (theorem.id !== 'GeneratedPackageAcceptanceImpliesPEqualsNP') {
    return validationReject0(['FinalPublicTheorem', 'id'], 'FinalPublicTheorem id mismatch', {
      actual: theorem.id,
    });
  }

  if (theorem.publicConclusion !== true) {
    return validationReject0(['FinalPublicTheorem', 'publicConclusion'], 'FinalPublicTheorem must expose a public conclusion', {
      actual: theorem.publicConclusion,
    });
  }

  if (theorem.noClaimBeforeAccept !== true) {
    return validationReject0(['FinalPublicTheorem', 'noClaimBeforeAccept'], 'FinalPublicTheorem must not claim P = NP before acceptance', {
      actual: theorem.noClaimBeforeAccept,
    });
  }

  if (theorem.finalVerdict !== 'conditional') {
    return validationReject0(['FinalPublicTheorem', 'finalVerdict'], 'FinalPublicTheorem finalVerdict must be conditional', {
      actual: theorem.finalVerdict,
    });
  }

  if (!isPlainObject(theorem.exportedStatement)) {
    return validationReject0(['FinalPublicTheorem', 'exportedStatement'], 'FinalPublicTheorem must include an exported statement object', {
      actual: typeof theorem.exportedStatement,
    });
  }

  if (theorem.exportedStatement.antecedent !== 'CheckPCCPackexp(GeneratePCCPack())=accept') {
    return validationReject0(['FinalPublicTheorem', 'exportedStatement', 'antecedent'], 'FinalPublicTheorem antecedent mismatch', {
      actual: theorem.exportedStatement.antecedent,
    });
  }

  if (theorem.exportedStatement.consequent !== 'P = NP') {
    return validationReject0(['FinalPublicTheorem', 'exportedStatement', 'consequent'], 'FinalPublicTheorem consequent mismatch', {
      actual: theorem.exportedStatement.consequent,
    });
  }

  return validationAccept0({
    kind: 'FinalPublicTheorem0NF',
  });
}

function validateFinalPolynomialBound0(bound) {
  if (!isPlainObject(bound)) {
    return validationReject0(['PolynomialBound'], 'PolynomialBound must be an object', {
      actual: typeof bound,
    });
  }

  for (const field of [
    'converterPolynomial',
    'lockedBuilderPolynomial',
    'residualBandPolynomial',
    'satDecisionPolynomial',
    'noPrivateSchedule',
  ]) {
    if (bound[field] !== true) {
      return validationReject0(['PolynomialBound', field], `PolynomialBound must certify ${field}`, {
        actual: bound[field],
      });
    }
  }

  if (!Number.isInteger(bound.exponent) || bound.exponent <= 0) {
    return validationReject0(['PolynomialBound', 'exponent'], 'PolynomialBound exponent must be positive', {
      actual: bound.exponent,
    });
  }

  if (!Number.isInteger(bound.residualSlackBound) || bound.residualSlackBound < 0 || bound.residualSlackBound > 4) {
    return validationReject0(['PolynomialBound', 'residualSlackBound'], 'PolynomialBound residualSlackBound must be an integer at most four', {
      actual: bound.residualSlackBound,
    });
  }

  return validationAccept0({
    kind: 'FinalPolynomialBound0NF',
    exponent: bound.exponent,
  });
}

function validateFinalReflectionCert0(cert) {
  if (!isPlainObject(cert)) {
    return validationReject0(['ReflectionCert'], 'ReflectionCert must be an object', {
      actual: typeof cert,
    });
  }

  for (const field of [
    'exact',
    'publicConclusion',
    'replayable',
  ]) {
    if (cert[field] !== true) {
      return validationReject0(['ReflectionCert', field], `ReflectionCert must certify ${field}`, {
        actual: cert[field],
      });
    }
  }

  if (!arrayContainsAll0(cert.reflectedTheorems, FINAL0_THEOREM_IDS0)) {
    return validationReject0(['ReflectionCert', 'reflectedTheorems'], 'ReflectionCert is missing required final theorem reflections', {
      expected: FINAL0_THEOREM_IDS0,
      actual: cert.reflectedTheorems,
    });
  }

  if (!isPlainObject(cert.proofRef)) {
    return validationReject0(['ReflectionCert', 'proofRef'], 'ReflectionCert must include a proofRef object', {
      actual: typeof cert.proofRef,
    });
  }

  return validationAccept0({
    kind: 'FinalReflectionCert0NF',
  });
}

function validateFinalNoHiddenMinMetadata0(cert) {
  if (!isPlainObject(cert)) {
    return validationReject0(['NoHiddenMinCert'], 'NoHiddenMinCert must be an object', {
      actual: typeof cert,
    });
  }

  if (!arrayContainsAll0(cert.expansionStages, FINAL0_EXPANSION_STAGES0)) {
    return validationReject0(['NoHiddenMinCert', 'expansionStages'], 'NoHiddenMinCert must expand macros, aliases, generated templates, and imports', {
      expected: FINAL0_EXPANSION_STAGES0,
      actual: cert.expansionStages,
    });
  }

  if (!arrayContainsAll0(cert.forbiddenSymbols, FINAL0_FORBIDDEN_EXEC_SYMBOLS0)) {
    return validationReject0(['NoHiddenMinCert', 'forbiddenSymbols'], 'NoHiddenMinCert is missing a forbidden executable symbol', {
      expected: FINAL0_FORBIDDEN_EXEC_SYMBOLS0,
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
      return validationReject0(['NoHiddenMinCert', field], `NoHiddenMinCert must set ${field}`, {
        actual: cert[field],
      });
    }
  }

  if (!Array.isArray(cert.occurrences)) {
    return validationReject0(['NoHiddenMinCert', 'occurrences'], 'NoHiddenMinCert occurrences must be an array', {
      actual: typeof cert.occurrences,
    });
  }

  for (let index = 0; index < cert.occurrences.length; index += 1) {
    const occurrence = cert.occurrences[index];

    if (!isPlainObject(occurrence)) {
      return validationReject0(['NoHiddenMinCert', 'occurrences', index], 'NoHiddenMinCert occurrence must be an object', {
        actual: typeof occurrence,
      });
    }

    const identifier = occurrence.identifier;
    const expanded = occurrence.expandedIdentifier ?? identifier;

    if (
      occurrence.occurrenceClass === 'ExecCall' &&
      (
        FINAL0_FORBIDDEN_EXEC_SYMBOLS0.includes(identifier) ||
        FINAL0_FORBIDDEN_EXEC_SYMBOLS0.includes(expanded)
      )
    ) {
      return validationReject0(['NoHiddenMinCert', 'occurrences', index, 'identifier'], 'forbidden minimization symbol appears in executable position', {
        identifier,
        expandedIdentifier: expanded,
      });
    }
  }

  return validationAccept0({
    kind: 'FinalNoHiddenMinCert0NF',
    occurrenceCount: cert.occurrences.length,
  });
}

function validateRowFamFinalShape0(rowFam) {
  if (!isPlainObject(rowFam)) {
    return validationReject0([], 'RowFamFinal0 must be an object', {
      actual: typeof rowFam,
    });
  }

  if (rowFam.kind !== undefined && rowFam.kind !== 'RowFamFinal0') {
    return validationReject0(['kind'], 'RowFamFinal0 kind must be RowFamFinal0 when present', {
      actual: rowFam.kind,
    });
  }

  if (rowFam.version !== undefined && rowFam.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `RowFamFinal0 version must be ${CHECKER_VERSION} when present`, {
      actual: rowFam.version,
    });
  }

  if (!isPlainObject(rowFam.FinalTheorem)) {
    return validationReject0(['FinalTheorem'], 'RowFamFinal0 must include a FinalTheorem object', {
      actual: typeof rowFam.FinalTheorem,
    });
  }

  if (!Array.isArray(rowFam.rows)) {
    return validationReject0(['rows'], 'RowFamFinal0 rows must be an array', {
      actual: typeof rowFam.rows,
    });
  }

  if (getPiRowFamFinal0(rowFam) === undefined) {
    return validationReject0(['PiRowFamFinal'], 'RowFamFinal0 is missing PiRowFamFinal or ΠrowFamFinal', null);
  }

  return validationAccept0({
    kind: 'RowFamFinalShape0NF',
  });
}

function validateRowFamFinalCoverage0(rowFam) {
  const covered = new Set();

  for (const row of rowFam.rows) {
    if (isPlainObject(row) && isNonEmptyString(row.rowKind)) {
      covered.add(row.rowKind);
    }
  }

  for (const rowKind of ROWFAMFINAL_REQUIRED_ROWS0) {
    if (!covered.has(rowKind)) {
      return validationReject0(['rows', 'coverage', rowKind], 'RowFamFinal0 is missing a required final row', {
        rowKind,
      });
    }
  }

  return validationAccept0({
    kind: 'RowFamFinalCoverage0NF',
    rowCount: rowFam.rows.length,
  });
}

function validateRowFamFinalRows0(rowFam) {
  const seen = new Set();

  for (let index = 0; index < rowFam.rows.length; index += 1) {
    const row = rowFam.rows[index];

    if (!isPlainObject(row)) {
      return validationReject0(['rows', index], 'RowFamFinal0 row must be an object', {
        actual: typeof row,
      });
    }

    if (!isNonEmptyString(row.rowId)) {
      return validationReject0(['rows', index, 'rowId'], 'RowFamFinal0 row must have a rowId', {
        actual: row.rowId,
      });
    }

    if (seen.has(row.rowId)) {
      return validationReject0(['rows', index, 'rowId'], 'RowFamFinal0 row ids must be unique', {
        rowId: row.rowId,
      });
    }

    seen.add(row.rowId);

    if (row.family !== 'Final') {
      return validationReject0(['rows', index, 'family'], 'RowFamFinal0 rows must belong to family Final', {
        actual: row.family,
      });
    }

    if (row.selectedRoute !== 'Accept') {
      return validationReject0(['rows', index, 'selectedRoute'], 'RowFamFinal0 rows must select Accept', {
        actual: row.selectedRoute,
      });
    }

    if (!Array.isArray(row.activeRouteSet) || !row.activeRouteSet.includes(row.selectedRoute)) {
      return validationReject0(['rows', index, 'activeRouteSet'], 'RowFamFinal0 selected route must be active', {
        selectedRoute: row.selectedRoute,
        activeRouteSet: row.activeRouteSet,
      });
    }

    if (!isPlainObject(row.proofRef)) {
      return validationReject0(['rows', index, 'proofRef'], 'RowFamFinal0 row proofRef must be an object', {
        actual: typeof row.proofRef,
      });
    }

    if (!isPlainObject(row.boundsRef)) {
      return validationReject0(['rows', index, 'boundsRef'], 'RowFamFinal0 row boundsRef must be an object', {
        actual: typeof row.boundsRef,
      });
    }

    if (row.boundsRef.polynomial !== true || row.boundsRef.finite !== true) {
      return validationReject0(['rows', index, 'boundsRef'], 'RowFamFinal0 row bounds must be finite and polynomial', {
        boundsRef: row.boundsRef,
      });
    }
  }

  return validationAccept0({
    kind: 'RowFamFinalRows0NF',
    rowCount: rowFam.rows.length,
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
    return validationReject0(hit.path, 'opaque proof material is not allowed in Final0', hit);
  }

  return validationAccept0({
    kind: 'FinalNoOpaqueProof0NF',
  });
}

function findForbiddenExecutableUse0(value, path = [], inExecutablePosition = false) {
  if (typeof value === 'string') {
    if (inExecutablePosition && FINAL0_FORBIDDEN_EXEC_SYMBOLS0.includes(value)) {
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

function getPiFinal0(finalTheorem) {
  return finalTheorem.PiFinal ?? finalTheorem['Πfinal'] ?? finalTheorem.piFinal;
}

function getPiRowFamFinal0(rowFam) {
  return rowFam.PiRowFamFinal ?? rowFam['ΠrowFamFinal'] ?? rowFam.piRowFamFinal;
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
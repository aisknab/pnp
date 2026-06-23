import {
  CheckVerifierFrag0,
  digestCanonical0,
  makeAuditCase,
  makeRejectCase,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckBoot0,
  CheckBootAudit0,
  CheckBootBatch0,
  makeBootstrapB0Rows0,
} from './pcc-boot0.mjs';

import {
  makeMaterializedBoot0,
} from './pcc-boot-materialized0.mjs';

import {
  CheckKImpl0,
  CheckReflectionRegistry0,
  REFLECTION_REQUIRED_CHECKERS0,
  makeKernelRuleTable0,
  makeReflectionRegistry0,
  makeSyntheticKImpl0,
} from './pcc-kimpl0.mjs';

import {
  CheckSemanticSigma0,
  makeSemanticSigmaInput0,
} from './pcc-sigma-semantic0.mjs';

const CHECKER_VERSION = 0;

export const SEMANTIC_REFLECTION_REQUIRED_CHECKERS0 = Object.freeze([
  ...REFLECTION_REQUIRED_CHECKERS0,
]);

export const SEMANTIC_REFLECTION_POLICY0 = Object.freeze({
  kind: 'SemanticReflectionRefinementPolicy0',
  version: CHECKER_VERSION,
  requiresSemanticSigmaReadiness: true,
  requiresLegacyReflectionRegistryAcceptance: true,
  oneRefinementPerRequiredChecker: true,
  bindsEveryRefinementToRegistryEntryDigest: true,
  bindsEveryRefinementToExecutableCheckerContractDigest: true,
  canonicalPositiveProbeMustAccept: true,
  canonicalNegativeProbeMustReject: true,
  acceptedNormalFormKindMustMatch: true,
  rejectionCoordinateMustMatch: true,
  callerSoundnessAssertionsForbidden: true,
  boundedExecutableRefinementsOnly: true,
  unrestrictedCheckerSoundnessNotClaimed: true,
  globalNodeDerivationsRemainSeparateSurface: true,
});

export const SEMANTIC_REFLECTION_CHECKER_CONTRACTS0 = Object.freeze({
  CheckVerifierFrag0: Object.freeze({
    kind: 'SemanticReflectionCheckerContract0',
    version: CHECKER_VERSION,
    checker: 'CheckVerifierFrag0',
    module: 'pcc-verifier-frag0.mjs',
    positiveFixture: 'canonical-two-case-audit-suite',
    negativeFixture: 'malformed-cases-container',
    positiveNFKind: 'VerifierFrag0AuditNF',
    negativeCoord: 'CheckVerifierFrag0.input',
    totalAcceptRejectRecordRequired: true,
    deterministicDigestRequired: true,
  }),
  CheckBoot0: Object.freeze({
    kind: 'SemanticReflectionCheckerContract0',
    version: CHECKER_VERSION,
    checker: 'CheckBoot0',
    module: 'pcc-boot0.mjs',
    positiveFixture: 'materialized-bootstrap-record',
    negativeFixture: 'schedule-core-B0-mismatch',
    positiveNFKind: 'Boot0NF',
    negativeCoord: 'CheckBoot0.Sched0',
    totalAcceptRejectRecordRequired: true,
    deterministicDigestRequired: true,
  }),
  CheckBootBatch0: Object.freeze({
    kind: 'SemanticReflectionCheckerContract0',
    version: CHECKER_VERSION,
    checker: 'CheckBootBatch0',
    module: 'pcc-boot0.mjs',
    positiveFixture: 'complete-bootstrap-row-batch',
    negativeFixture: 'missing-required-bootstrap-row-family',
    positiveNFKind: 'BootBatch0NF',
    negativeCoord: 'CheckBootBatch0.coverage',
    totalAcceptRejectRecordRequired: true,
    deterministicDigestRequired: true,
  }),
  CheckBootAudit0: Object.freeze({
    kind: 'SemanticReflectionCheckerContract0',
    version: CHECKER_VERSION,
    checker: 'CheckBootAudit0',
    module: 'pcc-boot0.mjs',
    positiveFixture: 'canonical-verifier-fragment-audit',
    negativeFixture: 'non-array-audit-cases',
    positiveNFKind: 'BootAudit0NF',
    negativeCoord: 'CheckBootAudit0.input',
    totalAcceptRejectRecordRequired: true,
    deterministicDigestRequired: true,
  }),
  CheckKImpl0: Object.freeze({
    kind: 'SemanticReflectionCheckerContract0',
    version: CHECKER_VERSION,
    checker: 'CheckKImpl0',
    module: 'pcc-kimpl0.mjs',
    positiveFixture: 'complete-synthetic-kernel-implementation',
    negativeFixture: 'missing-Hall-primitive-rule',
    positiveNFKind: 'KImpl0NF',
    negativeCoord: 'CheckKImpl0.RuleTable',
    totalAcceptRejectRecordRequired: true,
    deterministicDigestRequired: true,
  }),
});

export function makeSemanticReflectionSuite0({
  ReflectionRegistry = makeReflectionRegistry0(),
} = {}) {
  const entries = getReflectionEntries0(ReflectionRegistry);
  if (!Array.isArray(entries)) {
    throw new TypeError(
      'makeSemanticReflectionSuite0 ReflectionRegistry must expose reflections',
    );
  }
  return Object.freeze({
    kind: 'SemanticReflectionSuite0',
    version: CHECKER_VERSION,
    suiteId: 'Reflection.semantic.required-checkers.bounded0',
    refinements: Object.freeze(
      SEMANTIC_REFLECTION_REQUIRED_CHECKERS0.map((checker, index) => {
        const registryEntry = entries.find((entry) => entry?.checker === checker);
        if (registryEntry === undefined) {
          throw new TypeError(
            `makeSemanticReflectionSuite0 requires registry entry ${checker}`,
          );
        }
        return makeSemanticReflectionRefinement0({
          index,
          checker,
          registryEntry,
        });
      }),
    ),
    Policy: { ...SEMANTIC_REFLECTION_POLICY0 },
  });
}

export function makeSemanticReflectionInput0({
  KImpl,
  K0,
  K0SemanticConformance,
  PSigma,
  SigmaSemanticDerivations,
  ReflectionRegistry = makeReflectionRegistry0(),
  SemanticReflection = makeSemanticReflectionSuite0({ ReflectionRegistry }),
} = {}) {
  return Object.freeze({
    kind: 'SemanticReflectionInput0',
    version: CHECKER_VERSION,
    KImpl,
    K0,
    K0SemanticConformance,
    PSigma,
    SigmaSemanticDerivations,
    ReflectionRegistry,
    SemanticReflection,
    Policy: { ...SEMANTIC_REFLECTION_POLICY0 },
  });
}

export async function CheckSemanticReflection0(input) {
  const checker = 'CheckSemanticReflection0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const sigmaCall = await callChecker0(
    'CheckSemanticSigma0',
    () => CheckSemanticSigma0(makeSemanticSigmaInput0({
      KImpl: input.KImpl,
      K0: input.K0,
      K0SemanticConformance: input.K0SemanticConformance,
      PSigma: input.PSigma,
      SemanticSigma: input.SigmaSemanticDerivations,
    })),
  );
  ledger.push(makeLedgerEntry0(
    'CheckSemanticSigma0',
    sigmaCall.ok && isSemanticSigmaAccept0(sigmaCall.record),
    sigmaCall.ok ? sigmaCall.record : sigmaCall.witness,
  ));
  if (!sigmaCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticSigma.exception`,
      path: ['SigmaSemanticDerivations'],
      witness: sigmaCall.witness,
      ledger,
    });
  }
  if (!isSemanticSigmaAccept0(sigmaCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticSigma`,
      path: ['SigmaSemanticDerivations'],
      witness: {
        reason: 'semantic reflection refinements require accepted semantic Sigma derivations',
        inner: compactRecord0(sigmaCall.record),
      },
      ledger,
    });
  }

  const registryCall = await callChecker0(
    'CheckReflectionRegistry0',
    () => CheckReflectionRegistry0(input.ReflectionRegistry),
  );
  ledger.push(makeLedgerEntry0(
    'CheckReflectionRegistry0',
    registryCall.ok && registryCall.record.tag === 'accept',
    registryCall.ok ? registryCall.record : registryCall.witness,
  ));
  if (!registryCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyReflection.exception`,
      path: ['ReflectionRegistry'],
      witness: registryCall.witness,
      ledger,
    });
  }
  if (registryCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyReflection`,
      path: ['ReflectionRegistry'],
      witness: {
        reason: 'legacy reflection registry rejected before semantic refinement upgrade',
        inner: compactRecord0(registryCall.record),
      },
      ledger,
    });
  }

  const suite = validateSemanticReflectionSuite0(
    input.SemanticReflection,
    input.ReflectionRegistry,
  );
  ledger.push(makeLedgerEntry0(
    'semanticReflectionSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticReflectionSuite`,
      suite,
      ledger,
    );
  }

  const acceptedRefinements = [];
  for (let index = 0;
    index < SEMANTIC_REFLECTION_REQUIRED_CHECKERS0.length;
    index += 1) {
    const checkerName = SEMANTIC_REFLECTION_REQUIRED_CHECKERS0[index];
    const refinement = input.SemanticReflection.refinements[index];
    const probeCall = await runCanonicalProbe0(checkerName);
    const probe = validateProbePair0({
      checkerName,
      contract: SEMANTIC_REFLECTION_CHECKER_CONTRACTS0[checkerName],
      refinement,
      probeCall,
    });
    ledger.push(makeLedgerEntry0(
      `reflection.${checkerName}`,
      probe.ok,
      probe.nf ?? probe.witness,
    ));
    if (!probe.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.reflection.${checkerName}`,
        probe,
        ledger,
      );
    }
    acceptedRefinements.push(probe.nf);
  }

  const sigmaNF = sigmaCall.record.NF ?? sigmaCall.record.nf ?? {};
  const registryNF = registryCall.record.NF ?? registryCall.record.nf ?? {};
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'SemanticReflection0NF',
      checker,
      version: CHECKER_VERSION,
      semanticReflectionReady: true,
      semanticReflectionContractReady: true,
      semanticReflectionSoundnessSurfaceReady: true,
      boundedExecutableRefinementsOnly: true,
      unrestrictedCheckerSoundnessNotClaimed: true,

      semanticKImplFinalReady: sigmaNF.semanticKImplFinalReady === true,
      semanticKImplFinalDigest: sigmaNF.semanticKImplFinalDigest ?? null,
      semanticK0ConformanceReady:
        sigmaNF.semanticK0ConformanceReady === true,
      semanticK0ConformanceDigest:
        sigmaNF.semanticK0ConformanceDigest ?? null,
      semanticSigmaReady: sigmaNF.semanticSigmaReady === true,
      semanticSigmaDigest: sigmaCall.record.Digest ?? sigmaCall.record.digest,
      semanticSigmaTheorems: sigmaNF.semanticSigmaTheorems ?? [],

      legacyReflectionAccepted: true,
      legacyReflectionChecker: registryCall.record.checker,
      legacyReflectionDigest:
        registryCall.record.Digest ?? registryCall.record.digest,
      legacyReflectionCount: registryNF.reflectionCount ?? null,
      legacyReflectionCheckers: registryNF.checkers ?? [],

      semanticReflectionSuiteId: suite.nf.suiteId,
      semanticReflectionCount: acceptedRefinements.length,
      semanticReflectionCheckers:
        [...SEMANTIC_REFLECTION_REQUIRED_CHECKERS0],
      semanticReflectionRefinements: acceptedRefinements,
      semanticReflectionRefinementDigests:
        acceptedRefinements.map((entry) => ({
          checker: entry.reflectedChecker,
          digest: entry.refinementDigest,
          registryEntryDigest: entry.registryEntryDigest,
          checkerContractDigest: entry.checkerContractDigest,
          positiveRecordDigest: entry.positiveRecordDigest,
          negativeRecordDigest: entry.negativeRecordDigest,
          conclusionDigest: entry.conclusionDigest,
        })),
      canonicalPositiveProbeCount: acceptedRefinements.length,
      canonicalNegativeProbeCount: acceptedRefinements.length,
      callerSoundnessAssertionsForbidden: true,
      globalNodeDerivationsReady: false,
      globalNodeDerivationsRemainSeparateSurface: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeSemanticReflectionRefinement0({
  index,
  checker,
  registryEntry,
}) {
  const contract = SEMANTIC_REFLECTION_CHECKER_CONTRACTS0[checker];
  const base = Object.freeze({
    kind: 'SemanticReflectionRefinement0',
    version: CHECKER_VERSION,
    index,
    checker,
    registryEntryChecker: registryEntry.checker,
    registryEntryDigest: digestCanonical0(registryEntry),
    checkerContractDigest: digestCanonical0(contract),
    positiveNFKind: contract.positiveNFKind,
    negativeCoord: contract.negativeCoord,
    scope: 'bounded-canonical-positive-negative-executable-refinement',
    unrestrictedCheckerSoundnessNotClaimed: true,
  });
  return Object.freeze({
    ...base,
    refinementDigest: digestCanonical0(base),
  });
}

async function runCanonicalProbe0(checkerName) {
  if (checkerName === 'CheckVerifierFrag0') {
    const positive = await CheckVerifierFrag0({
      kind: 'VerifierFrag0',
      version: CHECKER_VERSION,
      suiteId: 'reflection.CheckVerifierFrag0.positive',
      cases: [
        makeAuditCase({
          id: 'reflection.verifierfrag.test-pass',
          target: 'CheckVerifierFrag0',
          run: () => ({ tag: 'test-pass' }),
        }),
        makeRejectCase({
          id: 'reflection.verifierfrag.reject-observed',
          target: 'CheckVerifierFrag0',
          run: () => ({
            tag: 'reject',
            checker: 'ReflectionProbe0',
            Coord: 'ReflectionProbe0.negative',
          }),
        }),
      ],
    });
    const negative = await CheckVerifierFrag0({
      kind: 'VerifierFrag0',
      version: CHECKER_VERSION,
      suiteId: 'reflection.CheckVerifierFrag0.negative',
      cases: { malformed: true },
    });
    return { positive, negative };
  }

  if (checkerName === 'CheckBootBatch0') {
    const rows = makeBootstrapB0Rows0();
    const positiveInput = {
      kind: 'BootBatch0',
      version: CHECKER_VERSION,
      batchId: 'B0',
      rows,
    };
    const positive = await CheckBootBatch0(positiveInput);
    const negative = await CheckBootBatch0({
      ...positiveInput,
      rows: rows.slice(1),
    });
    return { positive, negative };
  }

  if (checkerName === 'CheckBootAudit0') {
    const positive = await CheckBootAudit0({
      kind: 'VerifierFrag0',
      version: CHECKER_VERSION,
      suiteId: 'reflection.CheckBootAudit0.positive',
      cases: [
        makeAuditCase({
          id: 'reflection.bootaudit.test-pass',
          target: 'CheckBootAudit0',
          run: () => ({ tag: 'test-pass' }),
        }),
      ],
    });
    const negative = await CheckBootAudit0({
      kind: 'BootAudit0',
      version: CHECKER_VERSION,
      cases: null,
    });
    return { positive, negative };
  }

  if (checkerName === 'CheckBoot0') {
    const boot = await makeMaterializedBoot0();
    const positive = await CheckBoot0(boot);
    const negative = await CheckBoot0({
      ...boot,
      Sched0: {
        ...boot.Sched0,
        core: {
          ...boot.Sched0.core,
          B0: 63,
        },
      },
    });
    return { positive, negative };
  }

  if (checkerName === 'CheckKImpl0') {
    const positive = await CheckKImpl0(makeSyntheticKImpl0());
    const negative = await CheckKImpl0(makeSyntheticKImpl0({
      RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'Hall'),
    }));
    return { positive, negative };
  }

  return {
    positive: null,
    negative: null,
    unsupportedChecker: checkerName,
  };
}

function validateProbePair0({
  checkerName,
  contract,
  refinement,
  probeCall,
}) {
  if (!isPlainObject0(probeCall)) {
    return validationReject0(
      ['SemanticReflection', 'probes', checkerName],
      'semantic reflection canonical probe did not return a probe pair',
      { actual: typeof probeCall },
    );
  }
  const positive = probeCall.positive;
  const negative = probeCall.negative;
  if (!isPlainObject0(positive)
      || positive.tag !== 'accept'
      || positive.checker !== checkerName) {
    return validationReject0(
      ['SemanticReflection', 'probes', checkerName, 'positive'],
      'semantic reflection canonical positive probe must return the reflected checker accept record',
      { checker: checkerName, actual: compactRecord0(positive) },
    );
  }
  const positiveNF = positive.NF ?? positive.nf;
  if (!isPlainObject0(positiveNF)
      || positiveNF.kind !== contract.positiveNFKind) {
    return validationReject0(
      ['SemanticReflection', 'probes', checkerName, 'positive', 'NF', 'kind'],
      'semantic reflection canonical positive probe accepted normal-form kind mismatch',
      {
        checker: checkerName,
        expected: contract.positiveNFKind,
        actual: positiveNF?.kind ?? null,
      },
    );
  }
  if (!isPlainObject0(negative)
      || negative.tag !== 'reject'
      || negative.checker !== checkerName) {
    return validationReject0(
      ['SemanticReflection', 'probes', checkerName, 'negative'],
      'semantic reflection canonical negative probe must return the reflected checker reject record',
      { checker: checkerName, actual: compactRecord0(negative) },
    );
  }
  const negativeCoord = negative.Coord ?? negative.coord;
  if (negativeCoord !== contract.negativeCoord) {
    return validationReject0(
      ['SemanticReflection', 'probes', checkerName, 'negative', 'Coord'],
      'semantic reflection canonical negative probe rejection coordinate mismatch',
      {
        checker: checkerName,
        expected: contract.negativeCoord,
        actual: negativeCoord,
      },
    );
  }

  const conclusion = Object.freeze({
    kind: 'CheckerReflectionRefinementConclusion0',
    version: CHECKER_VERSION,
    checker: checkerName,
    scope: refinement.scope,
    canonicalPositiveAccepted: true,
    canonicalNegativeRejected: true,
    positiveNFKind: contract.positiveNFKind,
    negativeCoord: contract.negativeCoord,
    boundedExecutableRefinement: true,
    unrestrictedCheckerSoundnessNotClaimed: true,
  });
  const nf = {
    kind: 'SemanticReflectionRefinement0NF',
    version: CHECKER_VERSION,
    reflectedChecker: checkerName,
    registryEntryDigest: refinement.registryEntryDigest,
    checkerContractDigest: refinement.checkerContractDigest,
    positiveRecordDigest: positive.Digest ?? positive.digest ?? digestCanonical0(positive),
    positiveNFKind: positiveNF.kind,
    negativeRecordDigest: negative.Digest ?? negative.digest ?? digestCanonical0(negative),
    negativeCoord,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    boundedExecutableRefinement: true,
    unrestrictedCheckerSoundnessNotClaimed: true,
  };
  return validationAccept0({
    ...nf,
    refinementDigest: digestCanonical0(nf),
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'semantic reflection input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'SemanticReflectionInput0') {
    return validationReject0(
      ['kind'],
      'semantic reflection input kind must be SemanticReflectionInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic reflection input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of [
    'KImpl',
    'K0',
    'K0SemanticConformance',
    'PSigma',
    'SigmaSemanticDerivations',
    'ReflectionRegistry',
    'SemanticReflection',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic reflection input is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.KImpl)
      || !isPlainObject0(input.K0)
      || !isPlainObject0(input.K0SemanticConformance)
      || !isPlainObject0(input.PSigma)
      || !isPlainObject0(input.SigmaSemanticDerivations)
      || !isPlainObject0(input.ReflectionRegistry)
      || !isPlainObject0(input.SemanticReflection)) {
    return validationReject0(
      ['input'],
      'semantic reflection dependency surfaces must be objects',
    );
  }
  if (!sameCanonical0(input.Policy, SEMANTIC_REFLECTION_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic reflection policy must match the fail-closed policy',
      { expected: SEMANTIC_REFLECTION_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'KImpl',
    'K0',
    'K0SemanticConformance',
    'PSigma',
    'SigmaSemanticDerivations',
    'ReflectionRegistry',
    'SemanticReflection',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic reflection rejects caller-supplied readiness or soundness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({ kind: 'SemanticReflectionInputShape0NF' });
}

function validateSemanticReflectionSuite0(suite, registry) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SemanticReflection'],
      'semantic reflection suite must be an object',
      { actual: typeof suite },
    );
  }
  const allowed = new Set([
    'kind', 'version', 'suiteId', 'refinements', 'Policy',
  ]);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['SemanticReflection', unexpected[0]],
      'semantic reflection suite rejects caller-supplied theorem or soundness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (suite.kind !== 'SemanticReflectionSuite0') {
    return validationReject0(
      ['SemanticReflection', 'kind'],
      'semantic reflection suite kind must be SemanticReflectionSuite0',
      { actual: suite.kind },
    );
  }
  if (suite.version !== CHECKER_VERSION) {
    return validationReject0(
      ['SemanticReflection', 'version'],
      `semantic reflection suite version must be ${CHECKER_VERSION}`,
      { actual: suite.version },
    );
  }
  if (!isNonEmptyString0(suite.suiteId)) {
    return validationReject0(
      ['SemanticReflection', 'suiteId'],
      'semantic reflection suiteId must be a non-empty string',
      { actual: suite.suiteId },
    );
  }
  if (!Array.isArray(suite.refinements)
      || suite.refinements.length !== SEMANTIC_REFLECTION_REQUIRED_CHECKERS0.length) {
    return validationReject0(
      ['SemanticReflection', 'refinements'],
      'semantic reflection suite must provide one refinement per required checker',
      {
        expected: SEMANTIC_REFLECTION_REQUIRED_CHECKERS0.length,
        actual: suite.refinements?.length,
      },
    );
  }
  if (!sameCanonical0(suite.Policy, SEMANTIC_REFLECTION_POLICY0)) {
    return validationReject0(
      ['SemanticReflection', 'Policy'],
      'semantic reflection suite policy must match the fail-closed policy',
      { expected: SEMANTIC_REFLECTION_POLICY0, actual: suite.Policy },
    );
  }

  const registryEntries = getReflectionEntries0(registry);
  const refinementDigests = [];
  const registryEntryDigests = [];
  const checkerContractDigests = [];
  for (let index = 0;
    index < SEMANTIC_REFLECTION_REQUIRED_CHECKERS0.length;
    index += 1) {
    const checker = SEMANTIC_REFLECTION_REQUIRED_CHECKERS0[index];
    const entry = suite.refinements[index];
    if (!isPlainObject0(entry)) {
      return validationReject0(
        ['SemanticReflection', 'refinements', index],
        'semantic reflection refinement must be an object',
        { actual: typeof entry },
      );
    }
    const registryEntry = registryEntries.find((candidate) => candidate?.checker === checker);
    if (registryEntry === undefined) {
      return validationReject0(
        ['ReflectionRegistry', 'reflections', checker],
        'semantic reflection refinement has no matching registry entry',
        { checker },
      );
    }
    const expected = makeSemanticReflectionRefinement0({
      index,
      checker,
      registryEntry,
    });
    if (!sameCanonical0(entry, expected)) {
      return validationReject0(
        ['SemanticReflection', 'refinements', index],
        'semantic reflection refinement must exactly match the computed registry and executable checker binding',
        { checker, expected, actual: entry },
      );
    }
    refinementDigests.push(entry.refinementDigest);
    registryEntryDigests.push(entry.registryEntryDigest);
    checkerContractDigests.push(entry.checkerContractDigest);
  }

  return validationAccept0({
    kind: 'SemanticReflectionSuite0NF',
    suiteId: suite.suiteId,
    refinementCount: suite.refinements.length,
    checkers: [...SEMANTIC_REFLECTION_REQUIRED_CHECKERS0],
    refinementDigests,
    registryEntryDigests,
    checkerContractDigests,
    policyDigest: digestCanonical0(suite.Policy),
  });
}

function isSemanticSigmaAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.semanticSigmaReady === true
    && nf?.semanticK0ConformanceReady === true
    && nf?.semanticKImplFinalReady === true;
}

function getReflectionEntries0(registry) {
  return registry?.reflections
    ?? registry?.Reflections
    ?? registry?.entries
    ?? registry?.Entries;
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

function isNonEmptyString0(value) {
  return typeof value === 'string' && value.length > 0;
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

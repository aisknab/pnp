import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckKImpl0,
  KERNEL_RULES0,
  makeSyntheticKImpl0,
} from './pcc-kimpl0.mjs';

import {
  CheckSemanticKernelProof0,
  CheckSemanticKernelReadiness0,
  SEMANTIC_KERNEL_REQUIRED_RULES0,
  SEMANTIC_KERNEL_SUPPORTED_RULES0,
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

export const KIMPL_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const KIMPL_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'KImplSemanticReleasePolicy0',
  version: CHECKER_VERSION,
  developmentMayUsePartialSemanticKernel: true,
  finalTheoremRequiresCompleteSemanticKernel: true,
  publicTheoremEmissionRequiresFinalTheoremReady: true,
  legacyAcceptanceIsNotSemanticReadiness: true,
});

export const KIMPL_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'KImplSemanticKernelBinding0',
  version: CHECKER_VERSION,
  proofChecker: 'CheckSemanticKernelProof0',
  readinessChecker: 'CheckSemanticKernelReadiness0',
});

/**
 * Successor KImpl envelope. The legacy KImpl remains an input because its
 * grammar, rule-table, bounds, parser, and structural checks are still useful.
 * Semantic proof checking and final-theorem readiness are separate computed
 * records and cannot be asserted by caller-provided booleans.
 */
export function makeKImplSuccessor0({
  KImpl = makeSyntheticKImpl0(),
  SemanticProofDAG = makeSemanticProofDAG0(),
  Purpose = 'development',
} = {}) {
  if (!KIMPL_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeKImplSuccessor0 Purpose must be one of ${KIMPL_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }

  return {
    kind: 'KImplSemanticSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KImpl,
    SemanticKernel: {
      ...KIMPL_SUCCESSOR_BINDING0,
      ProofDAG: SemanticProofDAG,
    },
    Policy: { ...KIMPL_SUCCESSOR_POLICY0 },
  };
}

/**
 * Development-facing successor checker. A partial semantic kernel may accept
 * only with development-only status. A record requesting final-theorem use is
 * rejected unless the independently computed readiness checker accepts.
 */
export async function CheckKImplSuccessor0(input) {
  return checkKImplSuccessorInternal0(input, {
    checker: 'CheckKImplSuccessor0',
    requiredPurpose: null,
  });
}

/**
 * Final-theorem gate. It refuses development-purpose records before checking
 * anything else and cannot be weakened by fields inside the input envelope.
 */
export async function CheckKImplFinalTheoremReadiness0(input) {
  return checkKImplSuccessorInternal0(input, {
    checker: 'CheckKImplFinalTheoremReadiness0',
    requiredPurpose: 'final-theorem',
  });
}

async function checkKImplSuccessorInternal0(input, {
  checker,
  requiredPurpose,
}) {
  const ledger = [];

  const shape = validateSuccessorShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));

  if (!shape.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.input`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  if (requiredPurpose !== null && input.Purpose !== requiredPurpose) {
    const witness = {
      reason: 'final-theorem readiness requires a final-theorem purpose record',
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
    kind: 'KImplSuccessorPurpose0NF',
    purpose,
  }));

  const ruleUniverse = validateRuleUniverse0();
  ledger.push(makeLedgerEntry0(
    'semanticRuleUniverse',
    ruleUniverse.ok,
    ruleUniverse.nf ?? ruleUniverse.witness,
  ));

  if (!ruleUniverse.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticRuleUniverse`,
      path: ruleUniverse.path,
      witness: ruleUniverse.witness,
      ledger,
    });
  }

  const legacyCall = await callChecker0(
    'CheckKImpl0',
    () => CheckKImpl0(input.KImpl),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKImpl0',
    legacyCall.ok && legacyCall.record.tag === 'accept',
    legacyCall.ok ? legacyCall.record : legacyCall.witness,
  ));

  if (!legacyCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyKImpl.exception`,
      path: ['KImpl'],
      witness: legacyCall.witness,
      ledger,
    });
  }

  const legacyRecord = legacyCall.record;
  if (legacyRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyKImpl`,
      path: ['KImpl'],
      witness: {
        reason: 'legacy CheckKImpl0 rejected the successor base KImpl',
        inner: compactReject0(legacyRecord),
      },
      ledger,
    });
  }

  const semanticProofCall = await callChecker0(
    'CheckSemanticKernelProof0',
    () => CheckSemanticKernelProof0(input.SemanticKernel.ProofDAG),
  );
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProof0',
    semanticProofCall.ok && semanticProofCall.record.tag === 'accept',
    semanticProofCall.ok ? semanticProofCall.record : semanticProofCall.witness,
  ));

  if (!semanticProofCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticProof.exception`,
      path: ['SemanticKernel', 'ProofDAG'],
      witness: semanticProofCall.witness,
      ledger,
    });
  }

  const semanticProofRecord = semanticProofCall.record;
  if (semanticProofRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticProof`,
      path: ['SemanticKernel', 'ProofDAG'],
      witness: {
        reason: 'semantic proof checker rejected the successor proof DAG',
        inner: compactReject0(semanticProofRecord),
      },
      ledger,
    });
  }

  const readinessCall = await callChecker0(
    'CheckSemanticKernelReadiness0',
    () => CheckSemanticKernelReadiness0(),
  );

  if (!readinessCall.ok) {
    ledger.push(makeLedgerEntry0(
      'CheckSemanticKernelReadiness0',
      false,
      readinessCall.witness,
    ));
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticReadiness.exception`,
      path: ['SemanticKernel'],
      witness: readinessCall.witness,
      ledger,
    });
  }

  const readinessRecord = readinessCall.record;
  const semanticKernelReady = isReadinessAccept0(readinessRecord);
  const readinessSummary = summarizeReadiness0(readinessRecord);
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelReadiness0',
    semanticKernelReady,
    readinessRecord,
  ));

  if (purpose === 'final-theorem' && !semanticKernelReady) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticReadiness`,
      path: ['SemanticKernel'],
      witness: {
        reason: 'successor KImpl is not ready for final-theorem use',
        missingRules: readinessSummary.missingRules,
        supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES0],
        requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES0],
        readinessChecker: 'CheckSemanticKernelReadiness0',
        inner: compactReject0(readinessRecord),
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem' && semanticKernelReady;
  const developmentOnly = !finalTheoremReady;
  const semanticProofNF = semanticProofRecord.NF ?? semanticProofRecord.nf ?? {};

  const nf = {
    kind: 'KImplSemanticSuccessor0NF',
    checker,
    version: CHECKER_VERSION,
    purpose,
    status: finalTheoremReady ? 'final-theorem-ready' : 'development-only',

    legacyKImplAccepted: true,
    legacyKImplChecker: legacyRecord.checker,
    legacyKImplDigest: legacyRecord.Digest ?? legacyRecord.digest,
    legacyAcceptanceIsNotSemanticReadiness: true,

    semanticProofAccepted: true,
    semanticProofChecker: semanticProofRecord.checker,
    semanticProofDigest: semanticProofRecord.Digest ?? semanticProofRecord.digest,
    semanticProofNodeCount: semanticProofNF.nodeCount ?? null,

    semanticReadinessChecker: readinessRecord.checker,
    semanticReadinessCheckerAccepted: readinessRecord.tag === 'accept',
    semanticReadinessDigest: readinessRecord.Digest ?? readinessRecord.digest,
    semanticKernelReady,
    requiredSemanticRules: [...SEMANTIC_KERNEL_REQUIRED_RULES0],
    supportedSemanticRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES0],
    missingSemanticRules: readinessSummary.missingRules,
    semanticRuleUniverseMatchesLegacyKImpl: true,

    developmentOnly,
    finalTheoremReady,
    publicTheoremEmissionAllowed: finalTheoremReady,
    finalTheoremRequiresCompleteSemanticKernel: true,
    policyDigest: digestCanonical0(input.Policy),
    bindingDigest: digestCanonical0({
      kind: input.SemanticKernel.kind,
      version: input.SemanticKernel.version,
      proofChecker: input.SemanticKernel.proofChecker,
      readinessChecker: input.SemanticKernel.readinessChecker,
    }),
  };

  return makeAcceptRecord0({
    checker,
    nf,
    ledger,
  });
}

function validateSuccessorShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'successor KImpl input must be an object', {
      actual: typeof input,
    });
  }

  if (input.kind !== 'KImplSemanticSuccessor0') {
    return validationReject0(
      ['kind'],
      'successor KImpl kind must be KImplSemanticSuccessor0',
      { actual: input.kind },
    );
  }

  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `successor KImpl version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }

  if (!KIMPL_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'successor KImpl Purpose is unsupported',
      {
        actual: input.Purpose,
        supportedPurposes: [...KIMPL_SUCCESSOR_PURPOSES0],
      },
    );
  }

  if (!isPlainObject0(input.KImpl)) {
    return validationReject0(['KImpl'], 'successor KImpl must include a base KImpl object', {
      actual: typeof input.KImpl,
    });
  }

  if (!isPlainObject0(input.SemanticKernel)) {
    return validationReject0(
      ['SemanticKernel'],
      'successor KImpl must include SemanticKernel binding',
      { actual: typeof input.SemanticKernel },
    );
  }

  const binding = {
    kind: input.SemanticKernel.kind,
    version: input.SemanticKernel.version,
    proofChecker: input.SemanticKernel.proofChecker,
    readinessChecker: input.SemanticKernel.readinessChecker,
  };

  if (!sameCanonical0(binding, KIMPL_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['SemanticKernel'],
      'successor KImpl semantic-kernel binding must match the executable checker boundary',
      {
        expected: KIMPL_SUCCESSOR_BINDING0,
        actual: binding,
      },
    );
  }

  if (!Object.prototype.hasOwnProperty.call(input.SemanticKernel, 'ProofDAG')) {
    return validationReject0(
      ['SemanticKernel', 'ProofDAG'],
      'successor KImpl semantic-kernel binding must include ProofDAG',
      null,
    );
  }

  if (!isPlainObject0(input.Policy)) {
    return validationReject0(
      ['Policy'],
      'successor KImpl must include semantic release policy',
      { actual: typeof input.Policy },
    );
  }

  if (!sameCanonical0(input.Policy, KIMPL_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'successor KImpl semantic release policy must match the fail-closed policy',
      {
        expected: KIMPL_SUCCESSOR_POLICY0,
        actual: input.Policy,
      },
    );
  }

  const allowedTopLevel = new Set([
    'kind',
    'version',
    'Purpose',
    'KImpl',
    'SemanticKernel',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowedTopLevel.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'successor KImpl rejects undeclared top-level readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  const allowedSemanticKernel = new Set([
    'kind',
    'version',
    'proofChecker',
    'readinessChecker',
    'ProofDAG',
  ]);
  const unexpectedSemantic = Object.keys(input.SemanticKernel)
    .filter((key) => !allowedSemanticKernel.has(key));
  if (unexpectedSemantic.length !== 0) {
    return validationReject0(
      ['SemanticKernel', unexpectedSemantic[0]],
      'successor KImpl rejects caller-supplied semantic readiness assertions',
      { unexpectedFields: unexpectedSemantic.sort() },
    );
  }

  return validationAccept0({
    kind: 'KImplSemanticSuccessorShape0NF',
    purpose: input.Purpose,
  });
}

function validateRuleUniverse0() {
  const legacy = [...KERNEL_RULES0];
  const semantic = [...SEMANTIC_KERNEL_REQUIRED_RULES0];

  if (!sameCanonical0(legacy, semantic)) {
    return validationReject0(
      ['SemanticKernel', 'requiredRules'],
      'semantic required-rule universe must exactly match the legacy KImpl primitive-rule universe',
      { legacyRules: legacy, semanticRules: semantic },
    );
  }

  return validationAccept0({
    kind: 'KImplSemanticRuleUniverse0NF',
    ruleCount: legacy.length,
    rules: legacy,
  });
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

function isReadinessAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return (
    record?.tag === 'accept'
    && nf?.semanticRuleCoverageComplete === true
    && Array.isArray(nf?.missingRules)
    && nf.missingRules.length === 0
  );
}

function summarizeReadiness0(record) {
  if (record?.tag === 'accept') {
    const nf = record.NF ?? record.nf ?? {};
    return {
      missingRules: Array.isArray(nf.missingRules) ? [...nf.missingRules] : [],
    };
  }

  const witness = record?.Witness ?? record?.witness ?? {};
  return {
    missingRules: Array.isArray(witness.missingRules)
      ? [...witness.missingRules]
      : SEMANTIC_KERNEL_REQUIRED_RULES0.filter(
        (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES0.includes(rule),
      ),
  };
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

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  KERNEL_RULES0,
  makeSyntheticKImpl0,
} from './pcc-kimpl0.mjs';

import {
  CheckKImplDAGIndSuccessor0,
  makeKImplDAGIndSuccessor0,
} from './pcc-kimpl-dagind-successor0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0,
} from './pcc-kernel-dagind-semantic0.mjs';

import {
  CheckSemanticKernelProofLedgerInd0,
  CheckSemanticKernelReadinessLedgerInd0,
  SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0,
  SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0,
} from './pcc-kernel-ledgerind-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

export const KIMPL_LEDGERIND_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const KIMPL_LEDGERIND_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'KImplSemanticLedgerIndReleasePolicy0',
  version: CHECKER_VERSION,
  developmentMayUsePartialSemanticKernel: true,
  predecessorSuccessorMustRemainDevelopmentOnly: true,
  localLedgerCasesMustBeAcceptedRecordEvidence: true,
  localTransitionJudgmentsMustBeAccepted: true,
  finalTheoremRequiresCompleteSemanticKernel: true,
  publicTheoremEmissionRequiresFinalTheoremReady: true,
  callerReadinessAssertionsForbidden: true,
});

export const KIMPL_LEDGERIND_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'KImplSemanticLedgerIndKernelBinding0',
  version: CHECKER_VERSION,
  predecessorSuccessorChecker: 'CheckKImplDAGIndSuccessor0',
  predecessorProofChecker: 'CheckSemanticKernelProofDAGInd0',
  proofChecker: 'CheckSemanticKernelProofLedgerInd0',
  readinessChecker: 'CheckSemanticKernelReadinessLedgerInd0',
});

export function makeKImplLedgerIndSuccessor0({
  KImpl = makeSyntheticKImpl0(),
  SemanticProofDAG = makeSemanticProofDAG0(),
  Purpose = 'development',
} = {}) {
  if (!KIMPL_LEDGERIND_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeKImplLedgerIndSuccessor0 Purpose must be one of ${KIMPL_LEDGERIND_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }

  return {
    kind: 'KImplSemanticLedgerIndSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KImpl,
    SemanticKernel: {
      ...KIMPL_LEDGERIND_SUCCESSOR_BINDING0,
      ProofDAG: SemanticProofDAG,
    },
    Policy: { ...KIMPL_LEDGERIND_SUCCESSOR_POLICY0 },
  };
}

export async function CheckKImplLedgerIndSuccessor0(input) {
  return checkSuccessorInternal0(input, {
    checker: 'CheckKImplLedgerIndSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckKImplLedgerIndFinalTheoremReadiness0(input) {
  return checkSuccessorInternal0(input, {
    checker: 'CheckKImplLedgerIndFinalTheoremReadiness0',
    requiredPurpose: 'final-theorem',
  });
}

async function checkSuccessorInternal0(input, {
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
      reason: 'LedgerInd final-theorem readiness requires a final-theorem purpose record',
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
    kind: 'KImplLedgerIndSuccessorPurpose0NF',
    purpose,
  }));

  const ruleUniverse = validateRuleUniverse0();
  ledger.push(makeLedgerEntry0(
    'semanticRuleUniverse',
    ruleUniverse.ok,
    ruleUniverse.nf ?? ruleUniverse.witness,
  ));
  if (!ruleUniverse.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticRuleUniverse`,
      ruleUniverse,
      ledger,
    );
  }

  const fullNodes = extractNodes0(input.SemanticKernel.ProofDAG);
  ledger.push(makeLedgerEntry0(
    'proofDAGShape',
    fullNodes.ok,
    fullNodes.nf ?? fullNodes.witness,
  ));
  if (!fullNodes.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.proofDAGShape`,
      fullNodes,
      ledger,
    );
  }

  const predecessorNodes = fullNodes.nodes.filter(
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_DAGIND0.includes(node?.RuleName),
  );
  const predecessorInput = makeKImplDAGIndSuccessor0({
    KImpl: input.KImpl,
    SemanticProofDAG: makeSemanticProofDAG0(predecessorNodes),
    Purpose: 'development',
  });

  const predecessorCall = await callChecker0(
    'CheckKImplDAGIndSuccessor0',
    () => CheckKImplDAGIndSuccessor0(predecessorInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKImplDAGIndSuccessor0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));

  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorSuccessor.exception`,
      path: ['KImpl'],
      witness: predecessorCall.witness,
      ledger,
    });
  }

  const predecessorRecord = predecessorCall.record;
  if (predecessorRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorSuccessor`,
      path: ['KImpl'],
      witness: {
        reason: 'DAGInd predecessor successor rejected the Eq/Subst/Record/DAGInd base',
        predecessorNodeIds: predecessorNodes.map((node) => node?.id ?? null),
        inner: compactReject0(predecessorRecord),
      },
      ledger,
    });
  }

  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'predecessorDevelopmentBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.predecessorDevelopmentBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const proofCall = await callChecker0(
    'CheckSemanticKernelProofLedgerInd0',
    () => CheckSemanticKernelProofLedgerInd0(input.SemanticKernel.ProofDAG),
  );
  ledger.push(makeLedgerEntry0(
    'CheckSemanticKernelProofLedgerInd0',
    proofCall.ok && proofCall.record.tag === 'accept',
    proofCall.ok ? proofCall.record : proofCall.witness,
  ));

  if (!proofCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticProof.exception`,
      path: ['SemanticKernel', 'ProofDAG'],
      witness: proofCall.witness,
      ledger,
    });
  }

  const proofRecord = proofCall.record;
  if (proofRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticProof`,
      path: ['SemanticKernel', 'ProofDAG'],
      witness: {
        reason: 'LedgerInd-extended semantic proof checker rejected the proof DAG',
        inner: compactReject0(proofRecord),
      },
      ledger,
    });
  }

  const readinessCall = await callChecker0(
    'CheckSemanticKernelReadinessLedgerInd0',
    () => CheckSemanticKernelReadinessLedgerInd0(),
  );
  if (!readinessCall.ok) {
    ledger.push(makeLedgerEntry0(
      'CheckSemanticKernelReadinessLedgerInd0',
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
    'CheckSemanticKernelReadinessLedgerInd0',
    semanticKernelReady,
    readinessRecord,
  ));

  if (purpose === 'final-theorem' && !semanticKernelReady) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticReadiness`,
      path: ['SemanticKernel'],
      witness: {
        reason: 'LedgerInd-extended successor KImpl is not ready for final-theorem use',
        missingRules: readinessSummary.missingRules,
        supportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0],
        requiredRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0],
        readinessChecker: 'CheckSemanticKernelReadinessLedgerInd0',
        inner: compactReject0(readinessRecord),
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem' && semanticKernelReady;
  const proofNF = proofRecord.NF ?? proofRecord.nf ?? {};

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'KImplSemanticLedgerIndSuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: finalTheoremReady ? 'final-theorem-ready' : 'development-only',

      predecessorSuccessorAccepted: true,
      predecessorSuccessorChecker: predecessorRecord.checker,
      predecessorSuccessorDigest: predecessorRecord.Digest ?? predecessorRecord.digest,
      predecessorSuccessorDevelopmentOnly: true,
      predecessorPublicTheoremEmissionAllowed: false,

      legacyKImplAccepted: predecessorNF.legacyKImplAccepted === true,
      legacyKImplDigest: predecessorNF.legacyKImplDigest ?? null,
      legacyAcceptanceIsNotSemanticReadiness: true,

      semanticProofAccepted: true,
      semanticProofChecker: proofRecord.checker,
      semanticProofDigest: proofRecord.Digest ?? proofRecord.digest,
      semanticProofNodeCount: proofNF.nodeCount ?? null,
      semanticLedgerIndNodeCount: proofNF.ledgerIndNodeCount ?? null,

      semanticReadinessChecker: readinessRecord.checker,
      semanticReadinessCheckerAccepted: readinessRecord.tag === 'accept',
      semanticReadinessDigest: readinessRecord.Digest ?? readinessRecord.digest,
      semanticKernelReady,
      requiredSemanticRules: [...SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0],
      supportedSemanticRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0],
      missingSemanticRules: readinessSummary.missingRules,
      semanticRuleUniverseMatchesLegacyKImpl: true,

      developmentOnly: !finalTheoremReady,
      finalTheoremReady,
      publicTheoremEmissionAllowed: finalTheoremReady,
      finalTheoremRequiresCompleteSemanticKernel: true,
      policyDigest: digestCanonical0(input.Policy),
      bindingDigest: digestCanonical0({
        kind: input.SemanticKernel.kind,
        version: input.SemanticKernel.version,
        predecessorSuccessorChecker: input.SemanticKernel.predecessorSuccessorChecker,
        predecessorProofChecker: input.SemanticKernel.predecessorProofChecker,
        proofChecker: input.SemanticKernel.proofChecker,
        readinessChecker: input.SemanticKernel.readinessChecker,
      }),
    },
    ledger,
  });
}

function validateShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'LedgerInd successor KImpl input must be an object', {
      actual: typeof input,
    });
  }

  if (input.kind !== 'KImplSemanticLedgerIndSuccessor0') {
    return validationReject0(
      ['kind'],
      'LedgerInd successor KImpl kind must be KImplSemanticLedgerIndSuccessor0',
      { actual: input.kind },
    );
  }

  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `LedgerInd successor KImpl version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }

  if (!KIMPL_LEDGERIND_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'LedgerInd successor KImpl Purpose is unsupported',
      {
        actual: input.Purpose,
        supportedPurposes: [...KIMPL_LEDGERIND_SUCCESSOR_PURPOSES0],
      },
    );
  }

  if (!isPlainObject0(input.KImpl)) {
    return validationReject0(
      ['KImpl'],
      'LedgerInd successor KImpl must include a base KImpl object',
      { actual: typeof input.KImpl },
    );
  }

  if (!isPlainObject0(input.SemanticKernel)) {
    return validationReject0(
      ['SemanticKernel'],
      'LedgerInd successor KImpl must include SemanticKernel binding',
      { actual: typeof input.SemanticKernel },
    );
  }

  const binding = {
    kind: input.SemanticKernel.kind,
    version: input.SemanticKernel.version,
    predecessorSuccessorChecker: input.SemanticKernel.predecessorSuccessorChecker,
    predecessorProofChecker: input.SemanticKernel.predecessorProofChecker,
    proofChecker: input.SemanticKernel.proofChecker,
    readinessChecker: input.SemanticKernel.readinessChecker,
  };
  if (!sameCanonical0(binding, KIMPL_LEDGERIND_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['SemanticKernel'],
      'LedgerInd semantic-kernel binding must match the executable checker boundary',
      {
        expected: KIMPL_LEDGERIND_SUCCESSOR_BINDING0,
        actual: binding,
      },
    );
  }

  if (!Object.prototype.hasOwnProperty.call(input.SemanticKernel, 'ProofDAG')) {
    return validationReject0(
      ['SemanticKernel', 'ProofDAG'],
      'LedgerInd semantic-kernel binding must include ProofDAG',
      null,
    );
  }

  if (!isPlainObject0(input.Policy)) {
    return validationReject0(
      ['Policy'],
      'LedgerInd successor KImpl must include semantic release policy',
      { actual: typeof input.Policy },
    );
  }

  if (!sameCanonical0(input.Policy, KIMPL_LEDGERIND_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'LedgerInd successor release policy must match the fail-closed policy',
      {
        expected: KIMPL_LEDGERIND_SUCCESSOR_POLICY0,
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
      'LedgerInd successor rejects undeclared top-level readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  const allowedSemantic = new Set([
    'kind',
    'version',
    'predecessorSuccessorChecker',
    'predecessorProofChecker',
    'proofChecker',
    'readinessChecker',
    'ProofDAG',
  ]);
  const unexpectedSemantic = Object.keys(input.SemanticKernel)
    .filter((key) => !allowedSemantic.has(key));
  if (unexpectedSemantic.length !== 0) {
    return validationReject0(
      ['SemanticKernel', unexpectedSemantic[0]],
      'LedgerInd successor rejects caller-supplied semantic readiness assertions',
      { unexpectedFields: unexpectedSemantic.sort() },
    );
  }

  return validationAccept0({
    kind: 'KImplSemanticLedgerIndSuccessorShape0NF',
    purpose: input.Purpose,
  });
}

function validateRuleUniverse0() {
  const legacy = [...KERNEL_RULES0];
  const semantic = [...SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0];
  if (!sameCanonical0(legacy, semantic)) {
    return validationReject0(
      ['SemanticKernel', 'requiredRules'],
      'LedgerInd semantic required-rule universe must match the legacy KImpl universe',
      { legacyRules: legacy, semanticRules: semantic },
    );
  }

  return validationAccept0({
    kind: 'KImplSemanticLedgerIndRuleUniverse0NF',
    ruleCount: legacy.length,
    rules: legacy,
  });
}

function validatePredecessorBoundary0(nf) {
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
        ['PredecessorSuccessor', 'NF', field],
        'DAGInd predecessor successor did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }

  return validationAccept0({
    kind: 'KImplLedgerIndPredecessorBoundary0NF',
    ...expected,
  });
}

function extractNodes0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0(
      { kind: 'KImplLedgerIndProofInput0NF', form: 'array', nodeCount: input.length },
      { nodes: input },
    );
  }

  if (!isPlainObject0(input)) {
    return validationReject0(
      ['SemanticKernel', 'ProofDAG'],
      'semantic proof DAG must be an array or object',
      { actual: typeof input },
    );
  }

  const nodes = input.nodes ?? input.ProofDAG ?? input.proofDAG;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['SemanticKernel', 'ProofDAG', 'nodes'],
      'semantic proof DAG must provide a nodes array',
      { actual: typeof nodes },
    );
  }

  return validationAcceptWith0(
    { kind: 'KImplLedgerIndProofInput0NF', form: 'object', nodeCount: nodes.length },
    { nodes },
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
      : SEMANTIC_KERNEL_REQUIRED_RULES_LEDGERIND0.filter(
        (rule) => !SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0.includes(rule),
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

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckGlobalProofDAG0,
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckKBundleSemanticFinalTheoremReadiness0,
  CheckKBundleSemanticSuccessor0,
  KBUNDLE_SEMANTIC_SUCCESSOR_PURPOSES0,
  makeKBundleSemanticSuccessor0,
} from './pcc-kbundle-semantic-successor0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_DAG_SEMANTIC_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_SEMANTIC_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  legacyGlobalDAGAcceptanceIsStructuralOnly: true,
  legacyFinalNodesQuarantinedUntilSemanticGateAccepts: true,
  semanticReadinessRootBindsComputedKBundleDigest: true,
  finalTheoremRequiresKBundleFinalReadiness: true,
  finalTheoremRequiresSemanticGlobalNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_SEMANTIC_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticCheckerBinding0',
  version: CHECKER_VERSION,
  semanticKBundleChecker: 'CheckKBundleSemanticSuccessor0',
  semanticKBundleFinalChecker: 'CheckKBundleSemanticFinalTheoremReadiness0',
  legacyGlobalDAGChecker: 'CheckGlobalProofDAG0',
});

export function makeGlobalProofDAGSemanticSuccessor0({
  KBundle = makeKBundleSemanticSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_SEMANTIC_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGSemanticSuccessor0 Purpose must be one of ${GLOBAL_DAG_SEMANTIC_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }

  return {
    kind: 'GlobalProofDAGSemanticSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KBundle,
    LegacyGlobalProofDAG,
    Binding: { ...GLOBAL_DAG_SEMANTIC_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_SEMANTIC_SUCCESSOR_POLICY0 },
  };
}

/**
 * Development-facing successor global-DAG checker. It preserves all legacy
 * structural checks but quarantines every legacy final node behind a computed
 * semantic gate rooted in the successor KBundle record.
 */
export async function CheckGlobalProofDAGSemanticSuccessor0(input) {
  return checkGlobalSemanticInternal0(input, {
    checker: 'CheckGlobalProofDAGSemanticSuccessor0',
    requiredPurpose: null,
  });
}

/**
 * Explicit final-theorem global-DAG gate. It rejects until both the successor
 * KBundle and the global theorem nodes have semantic derivations.
 */
export async function CheckGlobalProofDAGSemanticFinalTheoremReadiness0(input) {
  return checkGlobalSemanticInternal0(input, {
    checker: 'CheckGlobalProofDAGSemanticFinalTheoremReadiness0',
    requiredPurpose: 'final-theorem',
  });
}

async function checkGlobalSemanticInternal0(input, {
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
      reason: 'semantic global-DAG final readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGSemanticPurpose0NF',
    purpose,
  }));

  const developmentBundleInput = {
    ...input.KBundle,
    Purpose: 'development',
  };
  const developmentBundleCall = await callChecker0(
    'CheckKBundleSemanticSuccessor0',
    () => CheckKBundleSemanticSuccessor0(developmentBundleInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundleSemanticSuccessor0',
    developmentBundleCall.ok && developmentBundleCall.record.tag === 'accept',
    developmentBundleCall.ok
      ? developmentBundleCall.record
      : developmentBundleCall.witness,
  ));

  if (!developmentBundleCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundle.exception`,
      path: ['KBundle'],
      witness: developmentBundleCall.witness,
      ledger,
    });
  }

  const developmentBundleRecord = developmentBundleCall.record;
  if (developmentBundleRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundle`,
      path: ['KBundle'],
      witness: {
        reason: 'development semantic KBundle rejected',
        inner: compactReject0(developmentBundleRecord),
      },
      ledger,
    });
  }

  const developmentBundleNF = developmentBundleRecord.NF
    ?? developmentBundleRecord.nf
    ?? {};
  const bundleBoundary = validateDevelopmentBundleBoundary0(
    developmentBundleNF,
  );
  ledger.push(makeLedgerEntry0(
    'semanticKBundleDevelopmentBoundary',
    bundleBoundary.ok,
    bundleBoundary.nf ?? bundleBoundary.witness,
  ));
  if (!bundleBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticKBundleDevelopmentBoundary`,
      bundleBoundary,
      ledger,
    );
  }

  const finalBundleInput = {
    ...input.KBundle,
    Purpose: 'final-theorem',
  };
  const finalBundleCall = await callChecker0(
    'CheckKBundleSemanticFinalTheoremReadiness0',
    () => CheckKBundleSemanticFinalTheoremReadiness0(finalBundleInput),
  );
  if (!finalBundleCall.ok) {
    ledger.push(makeLedgerEntry0(
      'CheckKBundleSemanticFinalTheoremReadiness0',
      false,
      finalBundleCall.witness,
    ));
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundleFinal.exception`,
      path: ['KBundle'],
      witness: finalBundleCall.witness,
      ledger,
    });
  }

  const finalBundleRecord = finalBundleCall.record;
  const kBundleFinalReady = isFinalReadyAccept0(finalBundleRecord);
  ledger.push(makeLedgerEntry0(
    'CheckKBundleSemanticFinalTheoremReadiness0',
    kBundleFinalReady,
    finalBundleRecord,
  ));

  const legacyDAGCall = await callChecker0(
    'CheckGlobalProofDAG0',
    () => CheckGlobalProofDAG0(input.LegacyGlobalProofDAG),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAG0',
    legacyDAGCall.ok && legacyDAGCall.record.tag === 'accept',
    legacyDAGCall.ok ? legacyDAGCall.record : legacyDAGCall.witness,
  ));

  if (!legacyDAGCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyGlobalDAG.exception`,
      path: ['LegacyGlobalProofDAG'],
      witness: legacyDAGCall.witness,
      ledger,
    });
  }

  const legacyDAGRecord = legacyDAGCall.record;
  if (legacyDAGRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.legacyGlobalDAG`,
      path: ['LegacyGlobalProofDAG'],
      witness: {
        reason: 'legacy global proof DAG structural checker rejected',
        inner: compactReject0(legacyDAGRecord),
      },
      ledger,
    });
  }

  const overlay = validateAndBuildSemanticOverlay0({
    dag: input.LegacyGlobalProofDAG,
    bundleNF: developmentBundleNF,
  });
  ledger.push(makeLedgerEntry0(
    'semanticOverlay',
    overlay.ok,
    overlay.nf ?? overlay.witness,
  ));
  if (!overlay.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticOverlay`,
      overlay,
      ledger,
    );
  }

  const gate = makeComputedGlobalGate0({
    developmentBundleRecord,
    developmentBundleNF,
    finalBundleRecord,
    kBundleFinalReady,
    legacyDAGRecord,
    overlay: overlay.nf,
  });
  ledger.push(makeLedgerEntry0(
    'computedGlobalSemanticGate',
    gate.finalTheoremReady,
    gate,
  ));

  if (purpose === 'final-theorem' && !gate.finalTheoremReady) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticReadiness`,
      path: ['ComputedGlobalGate'],
      witness: {
        reason: 'successor global proof DAG is not ready for final-theorem use',
        blockers: gate.blockers,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        semanticKBundleFinalProbe: compactRecord0(finalBundleRecord),
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && gate.finalTheoremReady;
  const legacyDAGNF = legacyDAGRecord.NF ?? legacyDAGRecord.nf ?? {};

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGSemanticSuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: finalTheoremReady ? 'final-theorem-ready' : 'development-only',

      semanticKBundleDevelopmentAccepted: true,
      semanticKBundleDevelopmentChecker: developmentBundleRecord.checker,
      semanticKBundleDevelopmentDigest: developmentBundleRecord.Digest
        ?? developmentBundleRecord.digest,
      semanticKBundleDevelopmentOnly: true,
      semanticKBundlePublicTheoremEmissionAllowed: false,
      semanticKBundleComputedReadinessDigest:
        developmentBundleNF.computedReadinessDigest ?? null,

      semanticKBundleFinalChecker: finalBundleRecord.checker,
      semanticKBundleFinalProbeAccepted: finalBundleRecord.tag === 'accept',
      semanticKBundleFinalProbeDigest: finalBundleRecord.Digest
        ?? finalBundleRecord.digest,
      kBundleFinalReady,

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: legacyDAGRecord.checker,
      legacyGlobalDAGDigest: legacyDAGRecord.Digest ?? legacyDAGRecord.digest,
      legacyGlobalDAGNodeCount: legacyDAGNF.nodeCount ?? null,
      legacyGlobalDAGSemanticStatus: 'structural-only',

      semanticOverlay: overlay.nf,
      semanticOverlayDigest: digestCanonical0(overlay.nf),
      computedGlobalGate: gate,
      computedGlobalGateDigest: digestCanonical0(gate),

      legacyFinalNodesStructurallyAccepted: true,
      legacyFinalNodesQuarantined: !finalTheoremReady,
      activeFinalNodeIds: finalTheoremReady
        ? [...gate.requiredFinalNodeIds]
        : [],
      quarantinedFinalNodeIds: finalTheoremReady
        ? []
        : [...gate.quarantinedFinalNodeIds],

      developmentOnly: !finalTheoremReady,
      finalTheoremReady,
      publicTheoremEmissionAllowed: finalTheoremReady,
      finalTheoremRequiresComputedSemanticGate: true,
      bindingDigest: digestCanonical0(input.Binding),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function validateAndBuildSemanticOverlay0({ dag, bundleNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for semantic overlay',
      { actual: typeof nodes },
    );
  }

  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  const supportedRules = Array.isArray(bundleNF.semanticKImplSupportedRules)
    ? [...bundleNF.semanticKImplSupportedRules]
    : [];
  const missingRules = Array.isArray(bundleNF.semanticKImplMissingRules)
    ? [...bundleNF.semanticKImplMissingRules]
    : [];

  for (const rule of [...supportedRules, ...missingRules]) {
    if (!nodeById.has(`K.${rule}`)) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'kernel', rule],
        'semantic overlay requires a legacy kernel coordinate for every required primitive rule',
        { rule },
      );
    }
  }

  const requiredFinalNodeIds = [...GLOBAL_DAG_REQUIRED_FINALS0];
  for (const id of requiredFinalNodeIds) {
    const node = nodeById.get(id);
    if (node === undefined || node.nodeKind !== 'final') {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'final', id],
        'semantic overlay requires every legacy final coordinate as a quarantined final node',
        { id, actualKind: node?.nodeKind ?? null },
      );
    }
  }

  const semanticKernelNodeIds = supportedRules.map((rule) => `K.${rule}`);
  const blockedKernelNodeIds = missingRules.map((rule) => `K.${rule}`);
  const structuralOnlyNodeIds = nodes
    .filter((node) => !semanticKernelNodeIds.includes(node.id))
    .map((node) => node.id);

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticOverlay0NF',
    semanticKBundleDigest: bundleNF.computedReadinessDigest ?? null,
    semanticKernelNodeIds,
    blockedKernelNodeIds,
    structuralOnlyNodeIds,
    requiredFinalNodeIds,
    semanticKernelNodeCount: semanticKernelNodeIds.length,
    blockedKernelNodeCount: blockedKernelNodeIds.length,
    structuralOnlyNodeCount: structuralOnlyNodeIds.length,
    globalSemanticNodeDerivationsReady: false,
  });
}

function makeComputedGlobalGate0({
  developmentBundleRecord,
  developmentBundleNF,
  finalBundleRecord,
  kBundleFinalReady,
  legacyDAGRecord,
  overlay,
}) {
  const legacyDAGDigest = legacyDAGRecord.Digest ?? legacyDAGRecord.digest ?? null;
  const bundleDevelopmentDigest = developmentBundleRecord.Digest
    ?? developmentBundleRecord.digest
    ?? null;
  const bundleFinalDigest = finalBundleRecord.Digest
    ?? finalBundleRecord.digest
    ?? null;

  const nodes = [
    {
      id: 'Gate.KBundle.DevelopmentAcceptance',
      premises: [],
      ready: true,
      digest: bundleDevelopmentDigest,
    },
    {
      id: 'Gate.KBundle.FinalReadiness',
      premises: ['Gate.KBundle.DevelopmentAcceptance'],
      ready: kBundleFinalReady,
      digest: bundleFinalDigest,
    },
    {
      id: 'Gate.GlobalDAG.StructuralAcceptance',
      premises: [],
      ready: true,
      digest: legacyDAGDigest,
    },
    {
      id: 'Gate.GlobalDAG.SemanticNodeDerivations',
      premises: [
        'Gate.KBundle.DevelopmentAcceptance',
        'Gate.GlobalDAG.StructuralAcceptance',
      ],
      ready: overlay.globalSemanticNodeDerivationsReady === true,
      digest: digestCanonical0(overlay),
    },
  ];

  const finalReady = kBundleFinalReady
    && overlay.globalSemanticNodeDerivationsReady === true;
  nodes.push({
    id: 'Gate.FinalTheorem.Readiness',
    premises: [
      'Gate.KBundle.FinalReadiness',
      'Gate.GlobalDAG.SemanticNodeDerivations',
    ],
    ready: finalReady,
    digest: digestCanonical0({
      kBundleFinalReady,
      globalSemanticNodeDerivationsReady:
        overlay.globalSemanticNodeDerivationsReady === true,
    }),
  });

  const blockers = [
    {
      coordinate: 'KBundle.FinalReadiness',
      ready: kBundleFinalReady,
      reason: kBundleFinalReady
        ? null
        : 'successor KBundle semantic readiness remains blocked',
      digest: bundleFinalDigest,
    },
    {
      coordinate: 'GlobalDAG.SemanticNodeDerivations',
      ready: overlay.globalSemanticNodeDerivationsReady === true,
      reason: overlay.globalSemanticNodeDerivationsReady === true
        ? null
        : 'legacy kernel, Sigma, reflection, package, and final nodes have not been migrated to semantic derivations',
      digest: digestCanonical0(overlay),
    },
  ];

  return Object.freeze({
    kind: 'GlobalProofDAGComputedSemanticGate0',
    version: CHECKER_VERSION,
    semanticKBundleComputedReadinessDigest:
      developmentBundleNF.computedReadinessDigest ?? null,
    nodes: Object.freeze(nodes.map((node) => Object.freeze({
      ...node,
      premises: Object.freeze([...node.premises]),
    }))),
    blockers: Object.freeze(blockers.map((entry) => Object.freeze(entry))),
    blockerCoordinates: Object.freeze(
      blockers.filter((entry) => !entry.ready).map((entry) => entry.coordinate),
    ),
    requiredFinalNodeIds: Object.freeze([...overlay.requiredFinalNodeIds]),
    quarantinedFinalNodeIds: Object.freeze([...overlay.requiredFinalNodeIds]),
    legacyFinalNodesStructurallyAccepted: true,
    legacyFinalNodesSemanticallyActive: finalReady,
    finalTheoremReady: finalReady,
    publicTheoremEmissionAllowed: finalReady,
  });
}

function validateShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'semantic global-DAG input must be an object', {
      actual: typeof input,
    });
  }

  if (input.kind !== 'GlobalProofDAGSemanticSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic global-DAG kind must be GlobalProofDAGSemanticSuccessor0',
      { actual: input.kind },
    );
  }

  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic global-DAG version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }

  if (!GLOBAL_DAG_SEMANTIC_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic global-DAG Purpose is unsupported',
      {
        actual: input.Purpose,
        supportedPurposes: [...GLOBAL_DAG_SEMANTIC_SUCCESSOR_PURPOSES0],
      },
    );
  }

  for (const field of [
    'KBundle',
    'LegacyGlobalProofDAG',
    'Binding',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic global-DAG input is missing a required field',
        { field },
      );
    }
  }

  if (!isPlainObject0(input.KBundle)) {
    return validationReject0(
      ['KBundle'],
      'semantic global-DAG KBundle must be an object',
      { actual: typeof input.KBundle },
    );
  }

  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic global-DAG input KBundle must remain development-purpose; final readiness is recomputed internally',
      { actual: input.KBundle.Purpose },
    );
  }

  if (!KBUNDLE_SEMANTIC_SUCCESSOR_PURPOSES0.includes(input.KBundle.Purpose)) {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic global-DAG KBundle Purpose is unsupported',
      { actual: input.KBundle.Purpose },
    );
  }

  if (!isPlainObject0(input.LegacyGlobalProofDAG)) {
    return validationReject0(
      ['LegacyGlobalProofDAG'],
      'semantic global-DAG must include a legacy global DAG object',
      { actual: typeof input.LegacyGlobalProofDAG },
    );
  }

  if (!isPlainObject0(input.Binding)
      || !sameCanonical0(input.Binding, GLOBAL_DAG_SEMANTIC_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'semantic global-DAG checker binding must match the executable checker boundary',
      {
        expected: GLOBAL_DAG_SEMANTIC_SUCCESSOR_BINDING0,
        actual: input.Binding,
      },
    );
  }

  if (!isPlainObject0(input.Policy)
      || !sameCanonical0(input.Policy, GLOBAL_DAG_SEMANTIC_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic global-DAG release policy must match the fail-closed policy',
      {
        expected: GLOBAL_DAG_SEMANTIC_SUCCESSOR_POLICY0,
        actual: input.Policy,
      },
    );
  }

  const allowed = new Set([
    'kind',
    'version',
    'Purpose',
    'KBundle',
    'LegacyGlobalProofDAG',
    'Binding',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'semantic global-DAG rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticSuccessorShape0NF',
    purpose: input.Purpose,
  });
}

function validateDevelopmentBundleBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    legacyBundleAccepted: true,
    semanticKImplDevelopmentAccepted: true,
  };

  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['KBundle', 'NF', field],
        'semantic KBundle did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticKBundleDevelopmentBoundary0NF',
    ...expected,
  });
}

function isFinalReadyAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return (
    record?.tag === 'accept'
    && nf?.finalTheoremReady === true
    && nf?.publicTheoremEmissionAllowed === true
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

function compactReject0(record) {
  return {
    checker: record?.checker ?? null,
    coord: record?.Coord ?? record?.coord ?? null,
    path: record?.Path ?? record?.path ?? null,
    witness: record?.Witness ?? record?.witness ?? null,
    digest: record?.Digest ?? record?.digest ?? null,
  };
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

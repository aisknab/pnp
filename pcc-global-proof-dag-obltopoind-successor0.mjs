import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGLedgerIndSuccessor0,
  makeGlobalProofDAGLedgerIndSuccessor0,
} from './pcc-global-proof-dag-ledgerind-successor0.mjs';

import {
  makeKBundleLedgerIndSuccessor0,
} from './pcc-kbundle-ledgerind-successor0.mjs';

import {
  CheckKBundleOblTopoIndFinalTheoremReadiness0,
  CheckKBundleOblTopoIndSuccessor0,
  makeKBundleOblTopoIndSuccessor0,
} from './pcc-kbundle-obltopoind-successor0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0,
} from './pcc-kernel-ledgerind-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticOblTopoIndReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorGlobalGateMustRemainDevelopmentOnly: true,
  predecessorGlobalGateCannotImplyOblTopoIndReadiness: true,
  legacyGlobalDAGAcceptanceIsStructuralOnly: true,
  legacyFinalNodesQuarantinedUntilSemanticGateAccepts: true,
  semanticReadinessRootBindsComputedKBundleDigest: true,
  finalTheoremRequiresKBundleFinalReadiness: true,
  finalTheoremRequiresSemanticGlobalNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticOblTopoIndCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGLedgerIndSuccessor0',
  semanticKBundleChecker: 'CheckKBundleOblTopoIndSuccessor0',
  semanticKBundleFinalChecker: 'CheckKBundleOblTopoIndFinalTheoremReadiness0',
});

export function makeGlobalProofDAGOblTopoIndSuccessor0({
  KBundle = makeKBundleOblTopoIndSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGOblTopoIndSuccessor0 Purpose must be one of ${GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }

  return {
    kind: 'GlobalProofDAGSemanticOblTopoIndSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KBundle,
    LegacyGlobalProofDAG,
    Binding: { ...GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_POLICY0 },
  };
}

/**
 * Development-facing global gate after OblTopoInd. The LedgerInd predecessor
 * global gate is rerun over the filtered five-rule bundle, then the expanded
 * KBundle is checked and rebound into a fresh semantic overlay. Legacy final
 * nodes remain quarantined.
 */
export async function CheckGlobalProofDAGOblTopoIndSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGOblTopoIndSuccessor0',
    requiredPurpose: null,
  });
}

/**
 * Explicit final-theorem global gate. It rejects until both the OblTopoInd
 * KBundle and every global theorem coordinate have semantic derivations.
 */
export async function CheckGlobalProofDAGOblTopoIndFinalTheoremReadiness0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGOblTopoIndFinalTheoremReadiness0',
    requiredPurpose: 'final-theorem',
  });
}

async function checkGlobalInternal0(input, {
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
      reason: 'OblTopoInd semantic global-DAG final readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGOblTopoIndPurpose0NF',
    purpose,
  }));

  const fullNodes = extractNodes0(
    input.KBundle.SemanticKImpl?.SemanticKernel?.ProofDAG,
  );
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_LEDGERIND0.includes(node?.RuleName),
  );
  const predecessorBundle = makeKBundleLedgerIndSuccessor0({
    KImpl: input.KBundle.SemanticKImpl.KImpl,
    SemanticProofDAG: makeSemanticProofDAG0(predecessorNodes),
    K0: input.KBundle.K0,
    PSigma: input.KBundle.PSigma,
    ReflectionRegistry: input.KBundle.ReflectionRegistry,
    Purpose: 'development',
  });
  const predecessorGlobalInput = makeGlobalProofDAGLedgerIndSuccessor0({
    KBundle: predecessorBundle,
    LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
    Purpose: 'development',
  });

  const predecessorGlobalCall = await callChecker0(
    'CheckGlobalProofDAGLedgerIndSuccessor0',
    () => CheckGlobalProofDAGLedgerIndSuccessor0(predecessorGlobalInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGLedgerIndSuccessor0',
    predecessorGlobalCall.ok && predecessorGlobalCall.record.tag === 'accept',
    predecessorGlobalCall.ok
      ? predecessorGlobalCall.record
      : predecessorGlobalCall.witness,
  ));

  if (!predecessorGlobalCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorGlobal.exception`,
      path: ['PredecessorGlobal'],
      witness: predecessorGlobalCall.witness,
      ledger,
    });
  }

  const predecessorGlobalRecord = predecessorGlobalCall.record;
  if (predecessorGlobalRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorGlobal`,
      path: ['PredecessorGlobal'],
      witness: {
        reason: 'LedgerInd predecessor global gate rejected the five-rule semantic base',
        predecessorNodeIds: predecessorNodes.map((node) => node?.id ?? null),
        inner: compactReject0(predecessorGlobalRecord),
      },
      ledger,
    });
  }

  const predecessorGlobalNF = predecessorGlobalRecord.NF
    ?? predecessorGlobalRecord.nf
    ?? {};
  const predecessorBoundary = validatePredecessorGlobalBoundary0(
    predecessorGlobalNF,
  );
  ledger.push(makeLedgerEntry0(
    'predecessorGlobalDevelopmentBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.predecessorGlobalDevelopmentBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const developmentBundleInput = {
    ...input.KBundle,
    Purpose: 'development',
  };
  const developmentBundleCall = await callChecker0(
    'CheckKBundleOblTopoIndSuccessor0',
    () => CheckKBundleOblTopoIndSuccessor0(developmentBundleInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundleOblTopoIndSuccessor0',
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
        reason: 'OblTopoInd development semantic KBundle rejected',
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
    'CheckKBundleOblTopoIndFinalTheoremReadiness0',
    () => CheckKBundleOblTopoIndFinalTheoremReadiness0(finalBundleInput),
  );
  if (!finalBundleCall.ok) {
    ledger.push(makeLedgerEntry0(
      'CheckKBundleOblTopoIndFinalTheoremReadiness0',
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
    'CheckKBundleOblTopoIndFinalTheoremReadiness0',
    kBundleFinalReady,
    finalBundleRecord,
  ));

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
    predecessorGlobalRecord,
    predecessorGlobalNF,
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
        reason: 'OblTopoInd successor global proof DAG is not ready for final-theorem use',
        blockers: gate.blockers,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        semanticKBundleFinalProbe: compactRecord0(finalBundleRecord),
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && gate.finalTheoremReady;

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGSemanticOblTopoIndSuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: finalTheoremReady ? 'final-theorem-ready' : 'development-only',

      predecessorGlobalAccepted: true,
      predecessorGlobalChecker: predecessorGlobalRecord.checker,
      predecessorGlobalDigest: predecessorGlobalRecord.Digest
        ?? predecessorGlobalRecord.digest,
      predecessorGlobalDevelopmentOnly: true,
      predecessorGlobalPublicTheoremEmissionAllowed: false,
      predecessorGlobalFinalNodesQuarantined: true,
      predecessorGlobalSemanticKernelNodeIds:
        predecessorGlobalNF.semanticOverlay?.semanticKernelNodeIds ?? [],

      semanticKBundleDevelopmentAccepted: true,
      semanticKBundleDevelopmentChecker: developmentBundleRecord.checker,
      semanticKBundleDevelopmentDigest: developmentBundleRecord.Digest
        ?? developmentBundleRecord.digest,
      semanticKBundleDevelopmentOnly: true,
      semanticKBundlePublicTheoremEmissionAllowed: false,
      semanticKBundleComputedReadinessDigest:
        developmentBundleNF.computedReadinessDigest ?? null,
      semanticKBundleSupportedRules:
        developmentBundleNF.semanticKImplSupportedRules ?? [],
      semanticKBundleMissingRules:
        developmentBundleNF.semanticKImplMissingRules ?? [],

      semanticKBundleFinalChecker: finalBundleRecord.checker,
      semanticKBundleFinalProbeAccepted: finalBundleRecord.tag === 'accept',
      semanticKBundleFinalProbeDigest: finalBundleRecord.Digest
        ?? finalBundleRecord.digest,
      kBundleFinalReady,

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: predecessorGlobalNF.legacyGlobalDAGChecker ?? null,
      legacyGlobalDAGDigest: predecessorGlobalNF.legacyGlobalDAGDigest ?? null,
      legacyGlobalDAGNodeCount:
        predecessorGlobalNF.legacyGlobalDAGNodeCount ?? null,
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
      'legacy global DAG must expose Nodes for OblTopoInd semantic overlay',
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

  const expectedSupportedRules = [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
    'LedgerInd',
    'OblTopoInd',
  ];
  if (!sameCanonical0(supportedRules, expectedSupportedRules)) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplSupportedRules'],
      'OblTopoInd global overlay requires the exact expanded semantic rule set',
      { expected: expectedSupportedRules, actual: supportedRules },
    );
  }

  for (const rule of [...supportedRules, ...missingRules]) {
    if (!nodeById.has(`K.${rule}`)) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'kernel', rule],
        'OblTopoInd semantic overlay requires a legacy kernel coordinate for every required primitive rule',
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
        'OblTopoInd semantic overlay requires every legacy final coordinate as a quarantined final node',
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
    kind: 'GlobalProofDAGSemanticOblTopoIndOverlay0NF',
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
  predecessorGlobalRecord,
  predecessorGlobalNF,
  overlay,
}) {
  const predecessorGlobalDigest = predecessorGlobalRecord.Digest
    ?? predecessorGlobalRecord.digest
    ?? null;
  const bundleDevelopmentDigest = developmentBundleRecord.Digest
    ?? developmentBundleRecord.digest
    ?? null;
  const bundleFinalDigest = finalBundleRecord.Digest
    ?? finalBundleRecord.digest
    ?? null;

  const nodes = [
    {
      id: 'Gate.PredecessorGlobal.DevelopmentAcceptance',
      premises: [],
      ready: true,
      digest: predecessorGlobalDigest,
    },
    {
      id: 'Gate.KBundle.OblTopoIndDevelopmentAcceptance',
      premises: ['Gate.PredecessorGlobal.DevelopmentAcceptance'],
      ready: true,
      digest: bundleDevelopmentDigest,
    },
    {
      id: 'Gate.KBundle.OblTopoIndFinalReadiness',
      premises: ['Gate.KBundle.OblTopoIndDevelopmentAcceptance'],
      ready: kBundleFinalReady,
      digest: bundleFinalDigest,
    },
    {
      id: 'Gate.GlobalDAG.StructuralAcceptance',
      premises: ['Gate.PredecessorGlobal.DevelopmentAcceptance'],
      ready: predecessorGlobalNF.legacyGlobalDAGAccepted === true,
      digest: predecessorGlobalNF.legacyGlobalDAGDigest ?? null,
    },
    {
      id: 'Gate.GlobalDAG.SemanticNodeDerivations',
      premises: [
        'Gate.KBundle.OblTopoIndDevelopmentAcceptance',
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
      'Gate.KBundle.OblTopoIndFinalReadiness',
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
      coordinate: 'KBundle.OblTopoIndFinalReadiness',
      ready: kBundleFinalReady,
      reason: kBundleFinalReady
        ? null
        : 'OblTopoInd successor KBundle semantic readiness remains blocked',
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
    kind: 'GlobalProofDAGComputedSemanticOblTopoIndGate0',
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
    return validationReject0([], 'OblTopoInd semantic global-DAG input must be an object', {
      actual: typeof input,
    });
  }

  if (input.kind !== 'GlobalProofDAGSemanticOblTopoIndSuccessor0') {
    return validationReject0(
      ['kind'],
      'OblTopoInd semantic global-DAG kind must be GlobalProofDAGSemanticOblTopoIndSuccessor0',
      { actual: input.kind },
    );
  }

  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `OblTopoInd semantic global-DAG version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }

  if (!GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'OblTopoInd semantic global-DAG Purpose is unsupported',
      {
        actual: input.Purpose,
        supportedPurposes: [...GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_PURPOSES0],
      },
    );
  }

  for (const field of ['KBundle', 'LegacyGlobalProofDAG', 'Binding', 'Policy']) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'OblTopoInd semantic global-DAG input is missing a required field',
        { field },
      );
    }
  }

  if (!isPlainObject0(input.KBundle)) {
    return validationReject0(
      ['KBundle'],
      'OblTopoInd semantic global-DAG KBundle must be an object',
      { actual: typeof input.KBundle },
    );
  }

  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'OblTopoInd semantic global-DAG input KBundle must remain development-purpose; final readiness is recomputed internally',
      { actual: input.KBundle.Purpose },
    );
  }

  if (!isPlainObject0(input.LegacyGlobalProofDAG)) {
    return validationReject0(
      ['LegacyGlobalProofDAG'],
      'OblTopoInd semantic global-DAG must include a legacy global DAG object',
      { actual: typeof input.LegacyGlobalProofDAG },
    );
  }

  if (!isPlainObject0(input.Binding)
      || !sameCanonical0(input.Binding, GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'OblTopoInd semantic global-DAG checker binding must match the executable checker boundary',
      {
        expected: GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_BINDING0,
        actual: input.Binding,
      },
    );
  }

  if (!isPlainObject0(input.Policy)
      || !sameCanonical0(input.Policy, GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'OblTopoInd semantic global-DAG release policy must match the fail-closed policy',
      {
        expected: GLOBAL_DAG_OBLTOPOIND_SUCCESSOR_POLICY0,
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
      'OblTopoInd semantic global-DAG rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticOblTopoIndSuccessorShape0NF',
    purpose: input.Purpose,
  });
}

function validatePredecessorGlobalBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    semanticKBundleDevelopmentAccepted: true,
    legacyGlobalDAGAccepted: true,
    legacyFinalNodesQuarantined: true,
  };

  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', field],
        'LedgerInd predecessor global gate did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }

  const expectedNodeIds = [
    'K.Eq',
    'K.Subst',
    'K.Record',
    'K.DAGInd',
    'K.LedgerInd',
  ];
  if (!sameCanonical0(nf.semanticOverlay?.semanticKernelNodeIds, expectedNodeIds)) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'semanticKernelNodeIds'],
      'LedgerInd predecessor global semantic overlay mismatch',
      {
        expected: expectedNodeIds,
        actual: nf.semanticOverlay?.semanticKernelNodeIds,
      },
    );
  }

  if (!Array.isArray(nf.activeFinalNodeIds) || nf.activeFinalNodeIds.length !== 0) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'activeFinalNodeIds'],
      'LedgerInd predecessor global gate must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }

  return validationAccept0({
    kind: 'GlobalProofDAGOblTopoIndPredecessorBoundary0NF',
    ...expected,
    semanticKernelNodeIds: expectedNodeIds,
  });
}

function validateDevelopmentBundleBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    semanticKImplDevelopmentAccepted: true,
    legacyBundleAccepted: true,
  };

  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['KBundle', 'NF', field],
        'OblTopoInd semantic KBundle did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }

  const expectedRules = [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
    'LedgerInd',
    'OblTopoInd',
  ];
  if (!sameCanonical0(nf.semanticKImplSupportedRules, expectedRules)) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplSupportedRules'],
      'OblTopoInd semantic KBundle supported-rule set mismatch',
      { expected: expectedRules, actual: nf.semanticKImplSupportedRules },
    );
  }

  return validationAccept0({
    kind: 'GlobalProofDAGOblTopoIndKBundleDevelopmentBoundary0NF',
    ...expected,
    semanticKImplSupportedRules: expectedRules,
  });
}

function extractNodes0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0(
      { kind: 'GlobalProofDAGOblTopoIndProofInput0NF', form: 'array', nodeCount: input.length },
      { nodes: input },
    );
  }

  if (!isPlainObject0(input)) {
    return validationReject0(
      ['KBundle', 'SemanticKImpl', 'SemanticKernel', 'ProofDAG'],
      'semantic proof DAG must be an array or object',
      { actual: typeof input },
    );
  }

  const nodes = input.nodes ?? input.ProofDAG ?? input.proofDAG;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['KBundle', 'SemanticKImpl', 'SemanticKernel', 'ProofDAG', 'nodes'],
      'semantic proof DAG must provide a nodes array',
      { actual: typeof nodes },
    );
  }

  return validationAcceptWith0(
    { kind: 'GlobalProofDAGOblTopoIndProofInput0NF', form: 'object', nodeCount: nodes.length },
    { nodes },
  );
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

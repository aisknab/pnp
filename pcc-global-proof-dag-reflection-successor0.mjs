import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGSigmaSuccessor0,
  makeGlobalProofDAGSigmaSuccessor0,
} from './pcc-global-proof-dag-sigma-successor0.mjs';

import {
  makeKBundleSigmaSuccessor0,
} from './pcc-kbundle-sigma-successor0.mjs';

import {
  CheckKBundleReflectionFinalTheoremReadiness0,
  CheckKBundleReflectionSuccessor0,
  makeKBundleReflectionSuccessor0,
} from './pcc-kbundle-reflection-successor0.mjs';

import {
  SEMANTIC_REFLECTION_REQUIRED_CHECKERS0,
} from './pcc-reflection-semantic0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
} from './pcc-kernel-finiterel-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

const COMPLETE_KERNEL_NODE_IDS0 = Object.freeze(
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0.map((rule) => `K.${rule}`),
);

const SEMANTIC_SIGMA_NODE_IDS0 = Object.freeze([
  'Sigma.V53',
  'Sigma.V54',
]);

const SEMANTIC_REFLECTION_NODE_IDS0 = Object.freeze(
  SEMANTIC_REFLECTION_REQUIRED_CHECKERS0.map(
    (checker) => `Reflection.${checker}`,
  ),
);

export const GLOBAL_DAG_REFLECTION_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_REFLECTION_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticReflectionReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorGlobalGateMustRemainDevelopmentOnly: true,
  predecessorGlobalGateCannotImplyReflectionReadiness: true,
  legacyGlobalDAGAcceptanceIsStructuralOnly: true,
  sigmaNodesRetainSemanticDerivationBindings: true,
  reflectionNodesBindSemanticRefinementDigests: true,
  boundedExecutableReflectionRefinementsOnly: true,
  unrestrictedCheckerSoundnessNotClaimed: true,
  legacyFinalNodesQuarantinedUntilSemanticGateAccepts: true,
  semanticReadinessRootBindsComputedKBundleDigest: true,
  finalTheoremRequiresKBundleFinalReadiness: true,
  finalTheoremRequiresSemanticGlobalNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_REFLECTION_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticReflectionCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGSigmaSuccessor0',
  semanticKBundleChecker: 'CheckKBundleReflectionSuccessor0',
  semanticKBundleFinalChecker:
    'CheckKBundleReflectionFinalTheoremReadiness0',
});

export function makeGlobalProofDAGReflectionSuccessor0({
  KBundle = makeKBundleReflectionSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_REFLECTION_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGReflectionSuccessor0 Purpose must be one of ${GLOBAL_DAG_REFLECTION_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGSemanticReflectionSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KBundle,
    LegacyGlobalProofDAG,
    Binding: { ...GLOBAL_DAG_REFLECTION_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_REFLECTION_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGReflectionSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGReflectionSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGReflectionFinalTheoremReadiness0(
  input,
) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGReflectionFinalTheoremReadiness0',
    requiredPurpose: 'final-theorem',
  });
}

async function checkGlobalInternal0(input, { checker, requiredPurpose }) {
  const ledger = [];
  const shape = validateShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  if (requiredPurpose !== null && input.Purpose !== requiredPurpose) {
    const witness = {
      reason: 'semantic reflection global-DAG final readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGReflectionPurpose0NF',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0.includes(
      node?.RuleName,
    ),
  );
  const predecessorBundle = makeKBundleSigmaSuccessor0({
    KImpl: input.KBundle.SemanticKImpl.KImpl,
    SemanticProofDAG: makeSemanticProofDAG0(predecessorNodes),
    K0: input.KBundle.K0,
    K0SemanticConformance: input.KBundle.K0SemanticConformance,
    PSigma: input.KBundle.PSigma,
    SigmaSemanticDerivations: input.KBundle.SigmaSemanticDerivations,
    ReflectionRegistry: input.KBundle.ReflectionRegistry,
    Purpose: 'development',
  });
  const predecessorGlobalInput = makeGlobalProofDAGSigmaSuccessor0({
    KBundle: predecessorBundle,
    LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
    Purpose: 'development',
  });
  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGSigmaSuccessor0',
    () => CheckGlobalProofDAGSigmaSuccessor0(predecessorGlobalInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGSigmaSuccessor0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorGlobal.exception`,
      path: ['PredecessorGlobal'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  const predecessorRecord = predecessorCall.record;
  if (predecessorRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorGlobal`,
      path: ['PredecessorGlobal'],
      witness: {
        reason: 'semantic Sigma predecessor global gate rejected before reflection upgrade',
        predecessorNodeIds: predecessorNodes.map((node) => node?.id ?? null),
        inner: compactRecord0(predecessorRecord),
      },
      ledger,
    });
  }
  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessorGlobalBoundary0(predecessorNF);
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

  const developmentCall = await callChecker0(
    'CheckKBundleReflectionSuccessor0',
    () => CheckKBundleReflectionSuccessor0({
      ...input.KBundle,
      Purpose: 'development',
    }),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundleReflectionSuccessor0',
    developmentCall.ok && developmentCall.record.tag === 'accept',
    developmentCall.ok ? developmentCall.record : developmentCall.witness,
  ));
  if (!developmentCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundle.exception`,
      path: ['KBundle'],
      witness: developmentCall.witness,
      ledger,
    });
  }
  const developmentRecord = developmentCall.record;
  if (developmentRecord.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundle`,
      path: ['KBundle'],
      witness: {
        reason: 'semantic reflection development KBundle rejected',
        inner: compactRecord0(developmentRecord),
      },
      ledger,
    });
  }
  const developmentNF = developmentRecord.NF ?? developmentRecord.nf ?? {};
  const bundleBoundary = validateDevelopmentBundleBoundary0(developmentNF);
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

  const finalCall = await callChecker0(
    'CheckKBundleReflectionFinalTheoremReadiness0',
    () => CheckKBundleReflectionFinalTheoremReadiness0({
      ...input.KBundle,
      Purpose: 'final-theorem',
    }),
  );
  if (!finalCall.ok) {
    ledger.push(makeLedgerEntry0(
      'CheckKBundleReflectionFinalTheoremReadiness0',
      false,
      finalCall.witness,
    ));
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundleFinal.exception`,
      path: ['KBundle'],
      witness: finalCall.witness,
      ledger,
    });
  }
  const finalRecord = finalCall.record;
  const kBundleFinalReady = isFinalReadyAccept0(finalRecord);
  ledger.push(makeLedgerEntry0(
    'CheckKBundleReflectionFinalTheoremReadiness0',
    kBundleFinalReady,
    finalRecord,
  ));
  if (!kBundleFinalReady) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticKBundleFinal`,
      path: ['KBundle'],
      witness: {
        reason: 'semantic reflection KBundle final-readiness probe did not accept',
        inner: compactRecord0(finalRecord),
      },
      ledger,
    });
  }

  const overlay = validateAndBuildSemanticOverlay0({
    dag: input.LegacyGlobalProofDAG,
    bundleNF: developmentNF,
    predecessorNF,
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
    developmentBundleRecord: developmentRecord,
    developmentBundleNF: developmentNF,
    finalBundleRecord: finalRecord,
    predecessorGlobalRecord: predecessorRecord,
    predecessorGlobalNF: predecessorNF,
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
        reason: 'semantic reflection global proof DAG is not ready for final-theorem use',
        blockers: gate.blockers,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        semanticKBundleFinalProbe: compactRecord0(finalRecord),
      },
      ledger,
    });
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && gate.finalTheoremReady;
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGSemanticReflectionSuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: finalTheoremReady ? 'final-theorem-ready' : 'development-only',

      predecessorGlobalAccepted: true,
      predecessorGlobalChecker: predecessorRecord.checker,
      predecessorGlobalDigest:
        predecessorRecord.Digest ?? predecessorRecord.digest,
      predecessorGlobalDevelopmentOnly: true,
      predecessorGlobalPublicTheoremEmissionAllowed: false,
      predecessorGlobalFinalNodesQuarantined: true,
      predecessorGlobalSemanticKernelNodeIds:
        predecessorNF.semanticOverlay?.semanticKernelNodeIds ?? [],
      predecessorGlobalSemanticSigmaNodeIds:
        predecessorNF.semanticOverlay?.semanticSigmaNodeIds ?? [],
      predecessorSemanticK0ConformanceReady: true,
      predecessorSemanticSigmaReady: true,
      predecessorSemanticReflectionReady: false,

      semanticKBundleDevelopmentAccepted: true,
      semanticKBundleDevelopmentChecker: developmentRecord.checker,
      semanticKBundleDevelopmentDigest:
        developmentRecord.Digest ?? developmentRecord.digest,
      semanticKBundleDevelopmentOnly: true,
      semanticKBundlePublicTheoremEmissionAllowed: false,
      semanticKBundleComputedReadinessDigest:
        developmentNF.computedReadinessDigest ?? null,
      semanticKBundleSupportedRules:
        developmentNF.semanticKImplSupportedRules ?? [],
      semanticKBundleMissingRules:
        developmentNF.semanticKImplMissingRules ?? [],
      semanticK0ConformanceReady:
        developmentNF.semanticK0ConformanceReady === true,
      semanticSigmaReady: developmentNF.semanticSigmaReady === true,
      semanticReflectionReady:
        developmentNF.semanticReflectionReady === true,
      semanticReflectionCheckers:
        developmentNF.semanticReflectionCheckers ?? [],
      semanticReflectionRefinementDigests:
        developmentNF.semanticReflectionRefinementDigests ?? [],
      boundedExecutableReflectionRefinementsOnly: true,
      unrestrictedCheckerSoundnessNotClaimed: true,

      semanticKBundleFinalChecker: finalRecord.checker,
      semanticKBundleFinalProbeAccepted: true,
      semanticKBundleFinalProbeDigest:
        finalRecord.Digest ?? finalRecord.digest,
      kBundleFinalReady: true,

      legacyGlobalDAGAccepted: true,
      legacyGlobalDAGChecker: predecessorNF.legacyGlobalDAGChecker ?? null,
      legacyGlobalDAGDigest: predecessorNF.legacyGlobalDAGDigest ?? null,
      legacyGlobalDAGNodeCount: predecessorNF.legacyGlobalDAGNodeCount ?? null,
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

function validateAndBuildSemanticOverlay0({ dag, bundleNF, predecessorNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for semantic reflection overlay',
      { actual: typeof nodes },
    );
  }

  const supportedRules = Array.isArray(bundleNF.semanticKImplSupportedRules)
    ? [...bundleNF.semanticKImplSupportedRules]
    : [];
  if (!sameCanonical0(
    supportedRules,
    SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
  )) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplSupportedRules'],
      'semantic reflection global overlay requires the exact complete primitive rule set',
      { actual: supportedRules },
    );
  }
  if (!sameCanonical0(bundleNF.semanticKImplMissingRules, [])) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplMissingRules'],
      'semantic reflection global overlay requires an empty primitive missing-rule set',
      { actual: bundleNF.semanticKImplMissingRules },
    );
  }
  for (const [field, value] of Object.entries({
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
  })) {
    if (bundleNF[field] !== value) {
      return validationReject0(
        ['KBundle', 'NF', field],
        'semantic reflection global overlay requires all KBundle semantic surfaces ready',
        { field, expected: value, actual: bundleNF[field] },
      );
    }
  }

  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  for (const rule of supportedRules) {
    if (!nodeById.has(`K.${rule}`)) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'kernel', rule],
        'semantic reflection overlay requires a legacy kernel coordinate for every primitive rule',
        { rule },
      );
    }
  }

  const predecessorSigmaBindings =
    predecessorNF.semanticOverlay?.semanticSigmaBindings;
  if (!Array.isArray(predecessorSigmaBindings)
      || predecessorSigmaBindings.length !== SEMANTIC_SIGMA_NODE_IDS0.length) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'semanticSigmaBindings'],
      'semantic reflection overlay requires the predecessor Sigma derivation bindings',
      { actual: predecessorSigmaBindings },
    );
  }
  const semanticSigmaBindings = predecessorSigmaBindings.map((entry) => ({
    ...entry,
  }));

  const refinementByChecker = new Map(
    (bundleNF.semanticReflectionRefinementDigests ?? []).map((entry) => [
      entry.checker,
      entry,
    ]),
  );
  const semanticReflectionBindings = [];
  for (const reflectedChecker of SEMANTIC_REFLECTION_REQUIRED_CHECKERS0) {
    const nodeId = `Reflection.${reflectedChecker}`;
    const node = nodeById.get(nodeId);
    if (node === undefined || node.nodeKind !== 'reflection') {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'reflection', reflectedChecker],
        'semantic reflection overlay requires every legacy reflection coordinate as a reflection node',
        { reflectedChecker, actualKind: node?.nodeKind ?? null },
      );
    }
    if (!sameCanonical0(node.premises, ['K.Record', 'K.Transport'])) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'reflection', reflectedChecker, 'premises'],
        'semantic reflection node must retain the exact Record and Transport prerequisites',
        {
          reflectedChecker,
          expected: ['K.Record', 'K.Transport'],
          actual: node.premises,
        },
      );
    }
    if (node.conclusion?.tag !== 'ReflectionAccepted0'
        || node.conclusion?.checker !== reflectedChecker) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'reflection', reflectedChecker, 'conclusion'],
        'semantic reflection node conclusion must match its checker coordinate',
        { reflectedChecker, actual: node.conclusion },
      );
    }
    const refinement = refinementByChecker.get(reflectedChecker);
    if (refinement === undefined) {
      return validationReject0(
        ['KBundle', 'NF', 'semanticReflectionRefinementDigests', reflectedChecker],
        'semantic reflection overlay is missing a checked refinement digest',
        { reflectedChecker },
      );
    }
    semanticReflectionBindings.push(Object.freeze({
      checker: reflectedChecker,
      nodeId,
      nodeDigest: node.Digest ?? digestCanonical0(node),
      refinementDigest: refinement.digest,
      registryEntryDigest: refinement.registryEntryDigest,
      checkerContractDigest: refinement.checkerContractDigest,
      positiveRecordDigest: refinement.positiveRecordDigest,
      negativeRecordDigest: refinement.negativeRecordDigest,
      conclusionDigest: refinement.conclusionDigest,
      scope: 'bounded-executable-refinement-surface',
      unrestrictedCheckerSoundnessNotClaimed: true,
    }));
  }

  const requiredFinalNodeIds = [...GLOBAL_DAG_REQUIRED_FINALS0];
  for (const id of requiredFinalNodeIds) {
    const node = nodeById.get(id);
    if (node === undefined || node.nodeKind !== 'final') {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'final', id],
        'semantic reflection overlay requires every legacy final coordinate as a quarantined final node',
        { id, actualKind: node?.nodeKind ?? null },
      );
    }
  }

  const semanticKernelNodeIds = supportedRules.map((rule) => `K.${rule}`);
  const semanticNodeIds = [
    ...semanticKernelNodeIds,
    ...SEMANTIC_SIGMA_NODE_IDS0,
    ...SEMANTIC_REFLECTION_NODE_IDS0,
  ];
  const structuralOnlyNodeIds = nodes
    .filter((node) => !semanticNodeIds.includes(node.id))
    .map((node) => node.id);

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticReflectionOverlay0NF',
    semanticKBundleDigest: bundleNF.computedReadinessDigest ?? null,
    semanticKernelNodeIds,
    blockedKernelNodeIds: [],
    semanticSigmaNodeIds: [...SEMANTIC_SIGMA_NODE_IDS0],
    blockedSigmaNodeIds: [],
    semanticSigmaBindings,
    semanticReflectionNodeIds: [...SEMANTIC_REFLECTION_NODE_IDS0],
    blockedReflectionNodeIds: [],
    semanticReflectionBindings,
    semanticNodeIds,
    structuralOnlyNodeIds,
    requiredFinalNodeIds,
    semanticKernelNodeCount: semanticKernelNodeIds.length,
    semanticSigmaNodeCount: SEMANTIC_SIGMA_NODE_IDS0.length,
    semanticReflectionNodeCount: SEMANTIC_REFLECTION_NODE_IDS0.length,
    semanticNodeCount: semanticNodeIds.length,
    structuralOnlyNodeCount: structuralOnlyNodeIds.length,
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    boundedExecutableReflectionRefinementsOnly: true,
    unrestrictedCheckerSoundnessNotClaimed: true,
    globalSemanticNodeDerivationsReady: false,
  });
}

function makeComputedGlobalGate0({
  developmentBundleRecord,
  developmentBundleNF,
  finalBundleRecord,
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
    makeGateNode0(
      'Gate.PredecessorGlobal.DevelopmentAcceptance',
      [],
      true,
      predecessorGlobalDigest,
    ),
    makeGateNode0(
      'Gate.KBundle.ReflectionDevelopmentAcceptance',
      ['Gate.PredecessorGlobal.DevelopmentAcceptance'],
      true,
      bundleDevelopmentDigest,
    ),
    makeGateNode0(
      'Gate.KBundle.ReflectionFinalReadiness',
      ['Gate.KBundle.ReflectionDevelopmentAcceptance'],
      true,
      bundleFinalDigest,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.StructuralAcceptance',
      ['Gate.PredecessorGlobal.DevelopmentAcceptance'],
      predecessorGlobalNF.legacyGlobalDAGAccepted === true,
      predecessorGlobalNF.legacyGlobalDAGDigest ?? null,
    ),
    makeGateNode0(
      'Gate.GlobalDAG.SemanticNodeDerivations',
      [
        'Gate.KBundle.ReflectionFinalReadiness',
        'Gate.GlobalDAG.StructuralAcceptance',
      ],
      overlay.globalSemanticNodeDerivationsReady === true,
      digestCanonical0(overlay),
    ),
  ];
  const finalReady = overlay.globalSemanticNodeDerivationsReady === true;
  nodes.push(makeGateNode0(
    'Gate.FinalTheorem.Readiness',
    [
      'Gate.KBundle.ReflectionFinalReadiness',
      'Gate.GlobalDAG.SemanticNodeDerivations',
    ],
    finalReady,
    digestCanonical0({
      kBundleFinalReady: true,
      globalSemanticNodeDerivationsReady:
        overlay.globalSemanticNodeDerivationsReady === true,
    }),
  ));
  const blockers = [
    Object.freeze({
      coordinate: 'KBundle.ReflectionFinalReadiness',
      ready: true,
      reason: null,
      digest: bundleFinalDigest,
      boundedExecutableReflectionRefinementsOnly: true,
      unrestrictedCheckerSoundnessNotClaimed: true,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.SemanticNodeDerivations',
      ready: overlay.globalSemanticNodeDerivationsReady === true,
      reason: overlay.globalSemanticNodeDerivationsReady === true
        ? null
        : 'legacy row, package, bounds, mode, import, no-min, and final nodes have not been migrated to semantic derivations',
      digest: digestCanonical0(overlay),
    }),
  ];
  return Object.freeze({
    kind: 'GlobalProofDAGComputedSemanticReflectionGate0',
    version: CHECKER_VERSION,
    semanticKBundleComputedReadinessDigest:
      developmentBundleNF.computedReadinessDigest ?? null,
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    boundedExecutableReflectionRefinementsOnly: true,
    unrestrictedCheckerSoundnessNotClaimed: true,
    nodes: Object.freeze(nodes),
    blockers: Object.freeze(blockers),
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
    return validationReject0(
      [],
      'semantic reflection global-DAG input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalProofDAGSemanticReflectionSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic reflection global-DAG kind must be GlobalProofDAGSemanticReflectionSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic reflection global-DAG version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!GLOBAL_DAG_REFLECTION_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic reflection global-DAG Purpose is unsupported',
      { actual: input.Purpose },
    );
  }
  for (const field of ['KBundle', 'LegacyGlobalProofDAG', 'Binding', 'Policy']) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic reflection global-DAG input is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.KBundle)) {
    return validationReject0(
      ['KBundle'],
      'semantic reflection global-DAG KBundle must be an object',
      { actual: typeof input.KBundle },
    );
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic reflection global-DAG input KBundle must remain development-purpose; final readiness is recomputed internally',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!isPlainObject0(input.LegacyGlobalProofDAG)) {
    return validationReject0(
      ['LegacyGlobalProofDAG'],
      'semantic reflection global-DAG must include a legacy global DAG object',
      { actual: typeof input.LegacyGlobalProofDAG },
    );
  }
  if (!sameCanonical0(input.Binding, GLOBAL_DAG_REFLECTION_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'semantic reflection global-DAG checker binding must match the executable checker boundary',
      { expected: GLOBAL_DAG_REFLECTION_SUCCESSOR_BINDING0, actual: input.Binding },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_DAG_REFLECTION_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic reflection global-DAG release policy must match the fail-closed policy',
      { expected: GLOBAL_DAG_REFLECTION_SUCCESSOR_POLICY0, actual: input.Policy },
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
      'semantic reflection global-DAG rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGSemanticReflectionSuccessorShape0NF',
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
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: false,
    legacyGlobalDAGAccepted: true,
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', field],
        'semantic Sigma predecessor global gate did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'activeFinalNodeIds'],
      'semantic Sigma predecessor global gate must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }
  if (!sameCanonical0(
    nf.semanticOverlay?.semanticKernelNodeIds,
    COMPLETE_KERNEL_NODE_IDS0,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'semanticKernelNodeIds'],
      'semantic Sigma predecessor global semantic-kernel node set mismatch',
      { actual: nf.semanticOverlay?.semanticKernelNodeIds },
    );
  }
  if (!sameCanonical0(
    nf.semanticOverlay?.semanticSigmaNodeIds,
    SEMANTIC_SIGMA_NODE_IDS0,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'semanticSigmaNodeIds'],
      'semantic Sigma predecessor global semantic-Sigma node set mismatch',
      { actual: nf.semanticOverlay?.semanticSigmaNodeIds },
    );
  }
  if (!sameCanonical0(nf.semanticOverlay?.blockedKernelNodeIds, [])
      || !sameCanonical0(nf.semanticOverlay?.blockedSigmaNodeIds, [])) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'semantic Sigma predecessor global must expose empty primitive and Sigma blocker sets',
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGReflectionPredecessorBoundary0NF',
    ...expected,
    activeFinalNodeIds: [],
    semanticKernelNodeIds: [...COMPLETE_KERNEL_NODE_IDS0],
    semanticSigmaNodeIds: [...SEMANTIC_SIGMA_NODE_IDS0],
  });
}

function validateDevelopmentBundleBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    semanticKImplDevelopmentAccepted: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    semanticReflectionSoundnessSurfaceReady: true,
    legacyBundleAccepted: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['KBundle', 'NF', field],
        'semantic reflection KBundle did not preserve its development-purpose boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!sameCanonical0(
    nf.semanticKImplSupportedRules,
    SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
  )) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplSupportedRules'],
      'semantic reflection KBundle supported-rule set mismatch',
      { actual: nf.semanticKImplSupportedRules },
    );
  }
  if (!sameCanonical0(nf.semanticKImplMissingRules, [])) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplMissingRules'],
      'semantic reflection KBundle must expose an empty primitive missing-rule set',
      { actual: nf.semanticKImplMissingRules },
    );
  }
  if (!sameCanonical0(nf.semanticReflectionCheckers, SEMANTIC_REFLECTION_REQUIRED_CHECKERS0)) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticReflectionCheckers'],
      'semantic reflection KBundle checker coverage mismatch',
      { actual: nf.semanticReflectionCheckers },
    );
  }
  if (!sameCanonical0(nf.computedReadiness?.blockerCoordinates, [])) {
    return validationReject0(
      ['KBundle', 'NF', 'computedReadiness', 'blockerCoordinates'],
      'semantic reflection KBundle must expose no remaining bundle blocker',
      { actual: nf.computedReadiness?.blockerCoordinates },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGReflectionKBundleBoundary0NF',
    ...expected,
    semanticKImplSupportedRules:
      [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
    semanticKImplMissingRules: [],
    semanticReflectionCheckers:
      [...SEMANTIC_REFLECTION_REQUIRED_CHECKERS0],
  });
}

function extractNodes0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0({
      kind: 'GlobalProofDAGReflectionProofInput0NF',
      form: 'array',
      nodeCount: input.length,
    }, { nodes: input });
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
  return validationAcceptWith0({
    kind: 'GlobalProofDAGReflectionProofInput0NF',
    form: 'object',
    nodeCount: nodes.length,
  }, { nodes });
}

function isFinalReadyAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.finalTheoremReady === true
    && nf?.publicTheoremEmissionAllowed === true;
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

function makeGateNode0(id, premises, ready, digest) {
  return Object.freeze({
    id,
    premises: Object.freeze([...premises]),
    ready,
    digest,
  });
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
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

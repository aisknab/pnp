import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGFiniteRelSuccessor0,
  makeGlobalProofDAGFiniteRelSuccessor0,
} from './pcc-global-proof-dag-finiterel-successor0.mjs';

import {
  makeKBundleFiniteRelSuccessor0,
} from './pcc-kbundle-finiterel-successor0.mjs';

import {
  CheckKBundleK0ConformanceFinalTheoremReadiness0,
  CheckKBundleK0ConformanceSuccessor0,
  makeKBundleK0ConformanceSuccessor0,
} from './pcc-kbundle-k0conformance-successor0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0,
} from './pcc-kernel-finiterel-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

const COMPLETE_KERNEL_NODE_IDS0 = Object.freeze(
  SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0.map(
    (rule) => `K.${rule}`,
  ),
);

export const GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticK0ConformanceReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorGlobalGateMustRemainDevelopmentOnly: true,
  predecessorGlobalGateCannotImplyK0ConformanceReadiness: true,
  legacyGlobalDAGAcceptanceIsStructuralOnly: true,
  legacyFinalNodesQuarantinedUntilSemanticGateAccepts: true,
  semanticReadinessRootBindsComputedKBundleDigest: true,
  finalTheoremRequiresKBundleFinalReadiness: true,
  finalTheoremRequiresSemanticGlobalNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticK0ConformanceCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGFiniteRelSuccessor0',
  semanticKBundleChecker: 'CheckKBundleK0ConformanceSuccessor0',
  semanticKBundleFinalChecker:
    'CheckKBundleK0ConformanceFinalTheoremReadiness0',
});

export function makeGlobalProofDAGK0ConformanceSuccessor0({
  KBundle = makeKBundleK0ConformanceSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGK0ConformanceSuccessor0 Purpose must be one of ${GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }

  return {
    kind: 'GlobalProofDAGSemanticK0ConformanceSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KBundle,
    LegacyGlobalProofDAG,
    Binding: { ...GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGK0ConformanceSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGK0ConformanceSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGK0ConformanceFinalTheoremReadiness0(
  input,
) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGK0ConformanceFinalTheoremReadiness0',
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
      reason: 'semantic K0 conformance global-DAG final readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGK0ConformancePurpose0NF',
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
  const predecessorBundle = makeKBundleFiniteRelSuccessor0({
    KImpl: input.KBundle.SemanticKImpl.KImpl,
    SemanticProofDAG: makeSemanticProofDAG0(predecessorNodes),
    K0: input.KBundle.K0,
    PSigma: input.KBundle.PSigma,
    ReflectionRegistry: input.KBundle.ReflectionRegistry,
    Purpose: 'development',
  });
  const predecessorGlobalInput = makeGlobalProofDAGFiniteRelSuccessor0({
    KBundle: predecessorBundle,
    LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
    Purpose: 'development',
  });

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGFiniteRelSuccessor0',
    () => CheckGlobalProofDAGFiniteRelSuccessor0(predecessorGlobalInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGFiniteRelSuccessor0',
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
        reason: 'FiniteRel predecessor global gate rejected the complete primitive semantic base',
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
    'CheckKBundleK0ConformanceSuccessor0',
    () => CheckKBundleK0ConformanceSuccessor0({
      ...input.KBundle,
      Purpose: 'development',
    }),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundleK0ConformanceSuccessor0',
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
        reason: 'semantic K0 conformance development KBundle rejected',
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
    'CheckKBundleK0ConformanceFinalTheoremReadiness0',
    () => CheckKBundleK0ConformanceFinalTheoremReadiness0({
      ...input.KBundle,
      Purpose: 'final-theorem',
    }),
  );
  if (!finalCall.ok) {
    ledger.push(makeLedgerEntry0(
      'CheckKBundleK0ConformanceFinalTheoremReadiness0',
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
    'CheckKBundleK0ConformanceFinalTheoremReadiness0',
    kBundleFinalReady,
    finalRecord,
  ));

  const overlay = validateAndBuildSemanticOverlay0({
    dag: input.LegacyGlobalProofDAG,
    bundleNF: developmentNF,
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
    kBundleFinalReady,
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
        reason: 'semantic K0 conformance global proof DAG is not ready for final-theorem use',
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
      kind: 'GlobalProofDAGSemanticK0ConformanceSuccessor0NF',
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
      semanticKImplFinalReady:
        developmentNF.computedReadiness?.semanticKImplFinalReady === true,

      semanticKBundleFinalChecker: finalRecord.checker,
      semanticKBundleFinalProbeAccepted: finalRecord.tag === 'accept',
      semanticKBundleFinalProbeDigest: finalRecord.Digest ?? finalRecord.digest,
      kBundleFinalReady,

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

function validateAndBuildSemanticOverlay0({ dag, bundleNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for semantic K0 conformance overlay',
      { actual: typeof nodes },
    );
  }

  const supportedRules = Array.isArray(bundleNF.semanticKImplSupportedRules)
    ? [...bundleNF.semanticKImplSupportedRules]
    : [];
  const missingRules = Array.isArray(bundleNF.semanticKImplMissingRules)
    ? [...bundleNF.semanticKImplMissingRules]
    : [];
  if (!sameCanonical0(supportedRules, SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0)) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplSupportedRules'],
      'semantic K0 conformance global overlay requires the exact complete primitive rule set',
      {
        expected: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
        actual: supportedRules,
      },
    );
  }
  if (missingRules.length !== 0) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplMissingRules'],
      'semantic K0 conformance global overlay requires an empty primitive missing-rule set',
      { actual: missingRules },
    );
  }
  if (bundleNF.semanticK0ConformanceReady !== true) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticK0ConformanceReady'],
      'semantic K0 conformance global overlay requires accepted K0 semantic conformance',
      { actual: bundleNF.semanticK0ConformanceReady },
    );
  }

  const nodeById = new Map(nodes.map((node) => [node.id, node]));
  for (const rule of supportedRules) {
    if (!nodeById.has(`K.${rule}`)) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'kernel', rule],
        'semantic K0 conformance overlay requires a legacy kernel coordinate for every primitive rule',
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
        'semantic K0 conformance overlay requires every legacy final coordinate as a quarantined final node',
        { id, actualKind: node?.nodeKind ?? null },
      );
    }
  }

  const semanticKernelNodeIds = supportedRules.map((rule) => `K.${rule}`);
  const structuralOnlyNodeIds = nodes
    .filter((node) => !semanticKernelNodeIds.includes(node.id))
    .map((node) => node.id);

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticK0ConformanceOverlay0NF',
    semanticKBundleDigest: bundleNF.computedReadinessDigest ?? null,
    semanticKernelNodeIds,
    blockedKernelNodeIds: [],
    structuralOnlyNodeIds,
    requiredFinalNodeIds,
    semanticKernelNodeCount: semanticKernelNodeIds.length,
    blockedKernelNodeCount: 0,
    structuralOnlyNodeCount: structuralOnlyNodeIds.length,
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: false,
    semanticReflectionReady: false,
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
    makeGateNode0(
      'Gate.PredecessorGlobal.DevelopmentAcceptance',
      [],
      true,
      predecessorGlobalDigest,
    ),
    makeGateNode0(
      'Gate.KBundle.K0ConformanceDevelopmentAcceptance',
      ['Gate.PredecessorGlobal.DevelopmentAcceptance'],
      true,
      bundleDevelopmentDigest,
    ),
    makeGateNode0(
      'Gate.KBundle.K0ConformanceFinalReadiness',
      ['Gate.KBundle.K0ConformanceDevelopmentAcceptance'],
      kBundleFinalReady,
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
        'Gate.KBundle.K0ConformanceDevelopmentAcceptance',
        'Gate.GlobalDAG.StructuralAcceptance',
      ],
      overlay.globalSemanticNodeDerivationsReady === true,
      digestCanonical0(overlay),
    ),
  ];

  const finalReady = kBundleFinalReady
    && overlay.globalSemanticNodeDerivationsReady === true;
  nodes.push(makeGateNode0(
    'Gate.FinalTheorem.Readiness',
    [
      'Gate.KBundle.K0ConformanceFinalReadiness',
      'Gate.GlobalDAG.SemanticNodeDerivations',
    ],
    finalReady,
    digestCanonical0({
      kBundleFinalReady,
      globalSemanticNodeDerivationsReady:
        overlay.globalSemanticNodeDerivationsReady === true,
    }),
  ));

  const blockers = [
    Object.freeze({
      coordinate: 'KBundle.K0ConformanceFinalReadiness',
      ready: kBundleFinalReady,
      reason: kBundleFinalReady
        ? null
        : 'semantic K0 conformance KBundle readiness remains blocked by Sigma and reflection surfaces',
      digest: bundleFinalDigest,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.SemanticNodeDerivations',
      ready: overlay.globalSemanticNodeDerivationsReady === true,
      reason: overlay.globalSemanticNodeDerivationsReady === true
        ? null
        : 'legacy Sigma, reflection, row, package, and final nodes have not been migrated to semantic derivations',
      digest: digestCanonical0(overlay),
    }),
  ];

  return Object.freeze({
    kind: 'GlobalProofDAGComputedSemanticK0ConformanceGate0',
    version: CHECKER_VERSION,
    semanticKBundleComputedReadinessDigest:
      developmentBundleNF.computedReadinessDigest ?? null,
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: overlay.semanticK0ConformanceReady === true,
    semanticSigmaReady: false,
    semanticReflectionReady: false,
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
      'semantic K0 conformance global-DAG input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalProofDAGSemanticK0ConformanceSuccessor0') {
    return validationReject0(
      ['kind'],
      'semantic K0 conformance global-DAG kind must be GlobalProofDAGSemanticK0ConformanceSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `semantic K0 conformance global-DAG version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  if (!GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'semantic K0 conformance global-DAG Purpose is unsupported',
      {
        actual: input.Purpose,
        supportedPurposes: [...GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_PURPOSES0],
      },
    );
  }
  for (const field of ['KBundle', 'LegacyGlobalProofDAG', 'Binding', 'Policy']) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'semantic K0 conformance global-DAG input is missing a required field',
        { field },
      );
    }
  }
  if (!isPlainObject0(input.KBundle)) {
    return validationReject0(
      ['KBundle'],
      'semantic K0 conformance global-DAG KBundle must be an object',
      { actual: typeof input.KBundle },
    );
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'semantic K0 conformance global-DAG input KBundle must remain development-purpose; final readiness is recomputed internally',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!isPlainObject0(input.LegacyGlobalProofDAG)) {
    return validationReject0(
      ['LegacyGlobalProofDAG'],
      'semantic K0 conformance global-DAG must include a legacy global DAG object',
      { actual: typeof input.LegacyGlobalProofDAG },
    );
  }
  if (!isPlainObject0(input.Binding)
      || !sameCanonical0(input.Binding, GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'semantic K0 conformance global-DAG checker binding must match the executable checker boundary',
      {
        expected: GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_BINDING0,
        actual: input.Binding,
      },
    );
  }
  if (!isPlainObject0(input.Policy)
      || !sameCanonical0(input.Policy, GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'semantic K0 conformance global-DAG release policy must match the fail-closed policy',
      {
        expected: GLOBAL_DAG_K0CONFORMANCE_SUCCESSOR_POLICY0,
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
      'semantic K0 conformance global-DAG rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticK0ConformanceSuccessorShape0NF',
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
        'FiniteRel predecessor global gate did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'activeFinalNodeIds'],
      'FiniteRel predecessor global gate must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }
  if (!sameCanonical0(
    nf.semanticOverlay?.semanticKernelNodeIds,
    COMPLETE_KERNEL_NODE_IDS0,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'semanticKernelNodeIds'],
      'FiniteRel predecessor global semantic-kernel node set mismatch',
      {
        expected: COMPLETE_KERNEL_NODE_IDS0,
        actual: nf.semanticOverlay?.semanticKernelNodeIds,
      },
    );
  }
  if (!sameCanonical0(nf.semanticOverlay?.blockedKernelNodeIds, [])) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'blockedKernelNodeIds'],
      'FiniteRel predecessor global must expose an empty primitive blocked-kernel set',
      { expected: [], actual: nf.semanticOverlay?.blockedKernelNodeIds },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGK0ConformancePredecessorBoundary0NF',
    ...expected,
    activeFinalNodeIds: [],
    semanticKernelNodeIds: [...COMPLETE_KERNEL_NODE_IDS0],
    blockedKernelNodeIds: [],
  });
}

function validateDevelopmentBundleBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    semanticKImplDevelopmentAccepted: true,
    semanticConformanceReady: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: false,
    semanticReflectionReady: false,
    legacyBundleAccepted: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['KBundle', 'NF', field],
        'semantic K0 conformance KBundle did not preserve its development-only boundary',
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
      'semantic K0 conformance KBundle supported-rule set mismatch',
      {
        expected: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
        actual: nf.semanticKImplSupportedRules,
      },
    );
  }
  if (!sameCanonical0(nf.semanticKImplMissingRules, [])) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplMissingRules'],
      'semantic K0 conformance KBundle must expose an empty primitive missing-rule set',
      { expected: [], actual: nf.semanticKImplMissingRules },
    );
  }
  return validationAccept0({
    kind: 'GlobalProofDAGK0ConformanceKBundleBoundary0NF',
    ...expected,
    semanticKImplSupportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_FINITEREL0],
    semanticKImplMissingRules: [],
  });
}

function extractNodes0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0(
      {
        kind: 'GlobalProofDAGK0ConformanceProofInput0NF',
        form: 'array',
        nodeCount: input.length,
      },
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
    {
      kind: 'GlobalProofDAGK0ConformanceProofInput0NF',
      form: 'object',
      nodeCount: nodes.length,
    },
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
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGDPIndSuccessor0,
  makeGlobalProofDAGDPIndSuccessor0,
} from './pcc-global-proof-dag-dpind-successor0.mjs';

import {
  makeKBundleDPIndSuccessor0,
} from './pcc-kbundle-dpind-successor0.mjs';

import {
  CheckKBundleHallFinalTheoremReadiness0,
  CheckKBundleHallSuccessor0,
  makeKBundleHallSuccessor0,
} from './pcc-kbundle-hall-successor0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0,
} from './pcc-kernel-dpind-semantic0.mjs';

import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0,
} from './pcc-kernel-hall-semantic0.mjs';

import {
  makeSemanticProofDAG0,
} from './pcc-kernel-semantic0.mjs';

const CHECKER_VERSION = 0;

const PREDECESSOR_NODE_IDS0 = Object.freeze(
  SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0.map((rule) => `K.${rule}`),
);

export const GLOBAL_DAG_HALL_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_HALL_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticHallReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorGlobalGateMustRemainDevelopmentOnly: true,
  predecessorGlobalGateCannotImplyHallReadiness: true,
  legacyGlobalDAGAcceptanceIsStructuralOnly: true,
  legacyFinalNodesQuarantinedUntilSemanticGateAccepts: true,
  semanticReadinessRootBindsComputedKBundleDigest: true,
  finalTheoremRequiresKBundleFinalReadiness: true,
  finalTheoremRequiresSemanticGlobalNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_HALL_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticHallCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGDPIndSuccessor0',
  semanticKBundleChecker: 'CheckKBundleHallSuccessor0',
  semanticKBundleFinalChecker: 'CheckKBundleHallFinalTheoremReadiness0',
});

export function makeGlobalProofDAGHallSuccessor0({
  KBundle = makeKBundleHallSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_HALL_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGHallSuccessor0 Purpose must be one of ${GLOBAL_DAG_HALL_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }

  return {
    kind: 'GlobalProofDAGSemanticHallSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KBundle,
    LegacyGlobalProofDAG,
    Binding: { ...GLOBAL_DAG_HALL_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_HALL_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGHallSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGHallSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGHallFinalTheoremReadiness0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGHallFinalTheoremReadiness0',
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
      reason: 'Hall semantic global-DAG final readiness requires a final-theorem purpose record',
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
    kind: 'GlobalProofDAGHallPurpose0NF',
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
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_DPIND0.includes(node?.RuleName),
  );
  const predecessorBundle = makeKBundleDPIndSuccessor0({
    KImpl: input.KBundle.SemanticKImpl.KImpl,
    SemanticProofDAG: makeSemanticProofDAG0(predecessorNodes),
    K0: input.KBundle.K0,
    PSigma: input.KBundle.PSigma,
    ReflectionRegistry: input.KBundle.ReflectionRegistry,
    Purpose: 'development',
  });
  const predecessorGlobalInput = makeGlobalProofDAGDPIndSuccessor0({
    KBundle: predecessorBundle,
    LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
    Purpose: 'development',
  });

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGDPIndSuccessor0',
    () => CheckGlobalProofDAGDPIndSuccessor0(predecessorGlobalInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGDPIndSuccessor0',
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
        reason: 'DPInd predecessor global gate rejected the nine-rule semantic base',
        predecessorNodeIds: predecessorNodes.map((node) => node?.id ?? null),
        inner: compactReject0(predecessorRecord),
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

  const developmentBundleInput = {
    ...input.KBundle,
    Purpose: 'development',
  };
  const developmentCall = await callChecker0(
    'CheckKBundleHallSuccessor0',
    () => CheckKBundleHallSuccessor0(developmentBundleInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckKBundleHallSuccessor0',
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
        reason: 'Hall development semantic KBundle rejected',
        inner: compactReject0(developmentRecord),
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

  const finalBundleInput = {
    ...input.KBundle,
    Purpose: 'final-theorem',
  };
  const finalCall = await callChecker0(
    'CheckKBundleHallFinalTheoremReadiness0',
    () => CheckKBundleHallFinalTheoremReadiness0(finalBundleInput),
  );
  if (!finalCall.ok) {
    ledger.push(makeLedgerEntry0(
      'CheckKBundleHallFinalTheoremReadiness0',
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
    'CheckKBundleHallFinalTheoremReadiness0',
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
        reason: 'Hall successor global proof DAG is not ready for final-theorem use',
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
      kind: 'GlobalProofDAGSemanticHallSuccessor0NF',
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
      'legacy global DAG must expose Nodes for Hall semantic overlay',
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

  if (!sameCanonical0(supportedRules, SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0)) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplSupportedRules'],
      'Hall global overlay requires the exact expanded semantic rule set',
      {
        expected: [...SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0],
        actual: supportedRules,
      },
    );
  }

  for (const rule of [...supportedRules, ...missingRules]) {
    if (!nodeById.has(`K.${rule}`)) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', 'kernel', rule],
        'Hall semantic overlay requires a legacy kernel coordinate for every required primitive rule',
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
        'Hall semantic overlay requires every legacy final coordinate as a quarantined final node',
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
    kind: 'GlobalProofDAGSemanticHallOverlay0NF',
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
      id: 'Gate.KBundle.HallDevelopmentAcceptance',
      premises: ['Gate.PredecessorGlobal.DevelopmentAcceptance'],
      ready: true,
      digest: bundleDevelopmentDigest,
    },
    {
      id: 'Gate.KBundle.HallFinalReadiness',
      premises: ['Gate.KBundle.HallDevelopmentAcceptance'],
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
        'Gate.KBundle.HallDevelopmentAcceptance',
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
      'Gate.KBundle.HallFinalReadiness',
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
      coordinate: 'KBundle.HallFinalReadiness',
      ready: kBundleFinalReady,
      reason: kBundleFinalReady
        ? null
        : 'Hall successor KBundle semantic readiness remains blocked',
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
    kind: 'GlobalProofDAGComputedSemanticHallGate0',
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
    return validationReject0(
      [],
      'Hall semantic global-DAG input must be an object',
      { actual: typeof input },
    );
  }

  if (input.kind !== 'GlobalProofDAGSemanticHallSuccessor0') {
    return validationReject0(
      ['kind'],
      'Hall semantic global-DAG kind must be GlobalProofDAGSemanticHallSuccessor0',
      { actual: input.kind },
    );
  }

  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `Hall semantic global-DAG version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }

  if (!GLOBAL_DAG_HALL_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return validationReject0(
      ['Purpose'],
      'Hall semantic global-DAG Purpose is unsupported',
      {
        actual: input.Purpose,
        supportedPurposes: [...GLOBAL_DAG_HALL_SUCCESSOR_PURPOSES0],
      },
    );
  }

  for (const field of ['KBundle', 'LegacyGlobalProofDAG', 'Binding', 'Policy']) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'Hall semantic global-DAG input is missing a required field',
        { field },
      );
    }
  }

  if (!isPlainObject0(input.KBundle)) {
    return validationReject0(
      ['KBundle'],
      'Hall semantic global-DAG KBundle must be an object',
      { actual: typeof input.KBundle },
    );
  }

  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'Hall semantic global-DAG input KBundle must remain development-purpose; final readiness is recomputed internally',
      { actual: input.KBundle.Purpose },
    );
  }

  if (!isPlainObject0(input.LegacyGlobalProofDAG)) {
    return validationReject0(
      ['LegacyGlobalProofDAG'],
      'Hall semantic global-DAG must include a legacy global DAG object',
      { actual: typeof input.LegacyGlobalProofDAG },
    );
  }

  if (!isPlainObject0(input.Binding)
      || !sameCanonical0(input.Binding, GLOBAL_DAG_HALL_SUCCESSOR_BINDING0)) {
    return validationReject0(
      ['Binding'],
      'Hall semantic global-DAG checker binding must match the executable checker boundary',
      {
        expected: GLOBAL_DAG_HALL_SUCCESSOR_BINDING0,
        actual: input.Binding,
      },
    );
  }

  if (!isPlainObject0(input.Policy)
      || !sameCanonical0(input.Policy, GLOBAL_DAG_HALL_SUCCESSOR_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'Hall semantic global-DAG release policy must match the fail-closed policy',
      {
        expected: GLOBAL_DAG_HALL_SUCCESSOR_POLICY0,
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
      'Hall semantic global-DAG rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }

  return validationAccept0({
    kind: 'GlobalProofDAGSemanticHallSuccessorShape0NF',
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
        'DPInd predecessor global gate did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }

  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'activeFinalNodeIds'],
      'DPInd predecessor global gate must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }

  if (!sameCanonical0(
    nf.semanticOverlay?.semanticKernelNodeIds,
    PREDECESSOR_NODE_IDS0,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'semanticKernelNodeIds'],
      'DPInd predecessor global semantic-kernel node set mismatch',
      {
        expected: PREDECESSOR_NODE_IDS0,
        actual: nf.semanticOverlay?.semanticKernelNodeIds,
      },
    );
  }

  return validationAccept0({
    kind: 'GlobalProofDAGHallPredecessorBoundary0NF',
    ...expected,
    activeFinalNodeIds: [],
    semanticKernelNodeIds: [...PREDECESSOR_NODE_IDS0],
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
        'Hall semantic KBundle did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }

  if (!sameCanonical0(
    nf.semanticKImplSupportedRules,
    SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0,
  )) {
    return validationReject0(
      ['KBundle', 'NF', 'semanticKImplSupportedRules'],
      'Hall semantic KBundle supported-rule set mismatch',
      {
        expected: [...SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0],
        actual: nf.semanticKImplSupportedRules,
      },
    );
  }

  return validationAccept0({
    kind: 'GlobalProofDAGHallKBundleBoundary0NF',
    ...expected,
    semanticKImplSupportedRules: [...SEMANTIC_KERNEL_SUPPORTED_RULES_HALL0],
  });
}

function extractNodes0(input) {
  if (Array.isArray(input)) {
    return validationAcceptWith0(
      {
        kind: 'GlobalProofDAGHallProofInput0NF',
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
      kind: 'GlobalProofDAGHallProofInput0NF',
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

import { digestCanonical0, stableStringify0 } from './pcc-verifier-frag0.mjs';
import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';
import {
  CheckGlobalProofDAGIntArithSuccessor0,
  makeGlobalProofDAGIntArithSuccessor0,
} from './pcc-global-proof-dag-intarith-successor0.mjs';
import {
  makeKBundleIntArithSuccessor0,
} from './pcc-kbundle-intarith-successor0.mjs';
import {
  CheckKBundleTransportFinalTheoremReadiness0,
  CheckKBundleTransportSuccessor0,
  makeKBundleTransportSuccessor0,
} from './pcc-kbundle-transport-successor0.mjs';
import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0,
} from './pcc-kernel-intarith-semantic0.mjs';
import {
  SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0,
} from './pcc-kernel-transport-semantic0.mjs';
import { makeSemanticProofDAG0 } from './pcc-kernel-semantic0.mjs';

const VERSION = 0;
const PREDECESSOR_NODE_IDS0 = Object.freeze(
  SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0.map((rule) => `K.${rule}`),
);

export const GLOBAL_DAG_TRANSPORT_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_TRANSPORT_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticTransportReleasePolicy0',
  version: VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  predecessorGlobalGateMustRemainDevelopmentOnly: true,
  predecessorGlobalGateCannotImplyTransportReadiness: true,
  legacyGlobalDAGAcceptanceIsStructuralOnly: true,
  legacyFinalNodesQuarantinedUntilSemanticGateAccepts: true,
  semanticReadinessRootBindsComputedKBundleDigest: true,
  finalTheoremRequiresKBundleFinalReadiness: true,
  finalTheoremRequiresSemanticGlobalNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_TRANSPORT_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticTransportCheckerBinding0',
  version: VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGIntArithSuccessor0',
  semanticKBundleChecker: 'CheckKBundleTransportSuccessor0',
  semanticKBundleFinalChecker:
    'CheckKBundleTransportFinalTheoremReadiness0',
});

export function makeGlobalProofDAGTransportSuccessor0({
  KBundle = makeKBundleTransportSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_TRANSPORT_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGTransportSuccessor0 Purpose must be one of ${GLOBAL_DAG_TRANSPORT_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGSemanticTransportSuccessor0',
    version: VERSION,
    Purpose,
    KBundle,
    LegacyGlobalProofDAG,
    Binding: { ...GLOBAL_DAG_TRANSPORT_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_TRANSPORT_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGTransportSuccessor0(input) {
  return checkGlobal0(input, 'CheckGlobalProofDAGTransportSuccessor0', null);
}

export async function CheckGlobalProofDAGTransportFinalTheoremReadiness0(
  input,
) {
  return checkGlobal0(
    input,
    'CheckGlobalProofDAGTransportFinalTheoremReadiness0',
    'final-theorem',
  );
}

async function checkGlobal0(input, checker, requiredPurpose) {
  const ledger = [];
  const shape = validateShape0(input);
  push0(ledger, 'shape', shape.ok, shape.nf ?? shape.witness);
  if (!shape.ok) return rejectValidation0(checker, `${checker}.input`, shape, ledger);

  if (requiredPurpose !== null && input.Purpose !== requiredPurpose) {
    return reject0(checker, `${checker}.purpose`, ['Purpose'], {
      reason: 'Transport semantic global-DAG final readiness requires a final-theorem purpose record',
      requiredPurpose,
      actualPurpose: input.Purpose,
    }, ledger);
  }
  const purpose = requiredPurpose ?? input.Purpose;
  push0(ledger, 'purpose', true, { purpose });

  const proof = extractNodes0(
    input.KBundle.SemanticKImpl?.SemanticKernel?.ProofDAG,
  );
  push0(ledger, 'proofDAGShape', proof.ok, proof.nf ?? proof.witness);
  if (!proof.ok) {
    return rejectValidation0(checker, `${checker}.proofDAGShape`, proof, ledger);
  }

  const predecessorNodes = proof.nodes.filter(
    (node) => SEMANTIC_KERNEL_SUPPORTED_RULES_INTARITH0.includes(
      node?.RuleName,
    ),
  );
  const predecessorBundle = makeKBundleIntArithSuccessor0({
    KImpl: input.KBundle.SemanticKImpl.KImpl,
    SemanticProofDAG: makeSemanticProofDAG0(predecessorNodes),
    K0: input.KBundle.K0,
    PSigma: input.KBundle.PSigma,
    ReflectionRegistry: input.KBundle.ReflectionRegistry,
    Purpose: 'development',
  });
  const predecessorInput = makeGlobalProofDAGIntArithSuccessor0({
    KBundle: predecessorBundle,
    LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
    Purpose: 'development',
  });
  const predecessorCall = await call0(
    'CheckGlobalProofDAGIntArithSuccessor0',
    () => CheckGlobalProofDAGIntArithSuccessor0(predecessorInput),
  );
  push0(
    ledger,
    'CheckGlobalProofDAGIntArithSuccessor0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  );
  if (!predecessorCall.ok) {
    return reject0(
      checker,
      `${checker}.predecessorGlobal.exception`,
      ['PredecessorGlobal'],
      predecessorCall.witness,
      ledger,
    );
  }
  if (predecessorCall.record.tag !== 'accept') {
    return reject0(checker, `${checker}.predecessorGlobal`, ['PredecessorGlobal'], {
      reason: 'IntArith predecessor global gate rejected the thirteen-rule semantic base',
      predecessorNodeIds: predecessorNodes.map((node) => node?.id ?? null),
      inner: compact0(predecessorCall.record),
    }, ledger);
  }
  const predecessorRecord = predecessorCall.record;
  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessor0(predecessorNF);
  push0(
    ledger,
    'predecessorGlobalDevelopmentBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  );
  if (!predecessorBoundary.ok) {
    return rejectValidation0(
      checker,
      `${checker}.predecessorGlobalDevelopmentBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const developmentCall = await call0(
    'CheckKBundleTransportSuccessor0',
    () => CheckKBundleTransportSuccessor0({
      ...input.KBundle,
      Purpose: 'development',
    }),
  );
  push0(
    ledger,
    'CheckKBundleTransportSuccessor0',
    developmentCall.ok && developmentCall.record.tag === 'accept',
    developmentCall.ok ? developmentCall.record : developmentCall.witness,
  );
  if (!developmentCall.ok) {
    return reject0(
      checker,
      `${checker}.semanticKBundle.exception`,
      ['KBundle'],
      developmentCall.witness,
      ledger,
    );
  }
  if (developmentCall.record.tag !== 'accept') {
    return reject0(checker, `${checker}.semanticKBundle`, ['KBundle'], {
      reason: 'Transport development semantic KBundle rejected',
      inner: compact0(developmentCall.record),
    }, ledger);
  }
  const developmentRecord = developmentCall.record;
  const developmentNF = developmentRecord.NF ?? developmentRecord.nf ?? {};
  const bundleBoundary = validateDevelopmentBundle0(developmentNF);
  push0(
    ledger,
    'semanticKBundleDevelopmentBoundary',
    bundleBoundary.ok,
    bundleBoundary.nf ?? bundleBoundary.witness,
  );
  if (!bundleBoundary.ok) {
    return rejectValidation0(
      checker,
      `${checker}.semanticKBundleDevelopmentBoundary`,
      bundleBoundary,
      ledger,
    );
  }

  const finalCall = await call0(
    'CheckKBundleTransportFinalTheoremReadiness0',
    () => CheckKBundleTransportFinalTheoremReadiness0({
      ...input.KBundle,
      Purpose: 'final-theorem',
    }),
  );
  if (!finalCall.ok) {
    return reject0(
      checker,
      `${checker}.semanticKBundleFinal.exception`,
      ['KBundle'],
      finalCall.witness,
      ledger,
    );
  }
  const finalRecord = finalCall.record;
  const kBundleFinalReady = finalReady0(finalRecord);
  push0(
    ledger,
    'CheckKBundleTransportFinalTheoremReadiness0',
    kBundleFinalReady,
    finalRecord,
  );

  const overlay = buildOverlay0(input.LegacyGlobalProofDAG, developmentNF);
  push0(ledger, 'semanticOverlay', overlay.ok, overlay.nf ?? overlay.witness);
  if (!overlay.ok) {
    return rejectValidation0(checker, `${checker}.semanticOverlay`, overlay, ledger);
  }
  const gate = makeGate0(
    predecessorRecord,
    predecessorNF,
    developmentRecord,
    developmentNF,
    finalRecord,
    kBundleFinalReady,
    overlay.nf,
  );
  push0(ledger, 'computedGlobalSemanticGate', gate.finalTheoremReady, gate);

  if (purpose === 'final-theorem' && !gate.finalTheoremReady) {
    return reject0(
      checker,
      `${checker}.semanticReadiness`,
      ['ComputedGlobalGate'],
      {
        reason: 'Transport successor global proof DAG is not ready for final-theorem use',
        blockers: gate.blockers,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        semanticKBundleFinalProbe: compact0(finalRecord),
      },
      ledger,
    );
  }

  const finalTheoremReady = purpose === 'final-theorem'
    && gate.finalTheoremReady;
  return accept0(checker, {
    kind: 'GlobalProofDAGSemanticTransportSuccessor0NF',
    checker,
    version: VERSION,
    purpose,
    status: finalTheoremReady ? 'final-theorem-ready' : 'development-only',
    predecessorGlobalAccepted: true,
    predecessorGlobalChecker: predecessorRecord.checker,
    predecessorGlobalDigest: digestOf0(predecessorRecord),
    predecessorGlobalDevelopmentOnly: true,
    predecessorGlobalPublicTheoremEmissionAllowed: false,
    predecessorGlobalFinalNodesQuarantined: true,
    predecessorGlobalSemanticKernelNodeIds:
      predecessorNF.semanticOverlay?.semanticKernelNodeIds ?? [],
    semanticKBundleDevelopmentAccepted: true,
    semanticKBundleDevelopmentChecker: developmentRecord.checker,
    semanticKBundleDevelopmentDigest: digestOf0(developmentRecord),
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
    semanticKBundleFinalProbeDigest: digestOf0(finalRecord),
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
    activeFinalNodeIds: finalTheoremReady ? [...gate.requiredFinalNodeIds] : [],
    quarantinedFinalNodeIds: finalTheoremReady
      ? []
      : [...gate.quarantinedFinalNodeIds],
    developmentOnly: !finalTheoremReady,
    finalTheoremReady,
    publicTheoremEmissionAllowed: finalTheoremReady,
    finalTheoremRequiresComputedSemanticGate: true,
    bindingDigest: digestCanonical0(input.Binding),
    policyDigest: digestCanonical0(input.Policy),
  }, ledger);
}

function buildOverlay0(dag, bundleNF) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) {
    return invalid0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'legacy global DAG must expose Nodes for Transport semantic overlay',
      { actual: typeof nodes },
    );
  }
  const supportedRules = Array.isArray(bundleNF.semanticKImplSupportedRules)
    ? [...bundleNF.semanticKImplSupportedRules]
    : [];
  const missingRules = Array.isArray(bundleNF.semanticKImplMissingRules)
    ? [...bundleNF.semanticKImplMissingRules]
    : [];
  if (!same0(supportedRules, SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0)) {
    return invalid0(
      ['KBundle', 'NF', 'semanticKImplSupportedRules'],
      'Transport global overlay requires the exact expanded semantic rule set',
      {
        expected: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0],
        actual: supportedRules,
      },
    );
  }
  const byId = new Map(nodes.map((node) => [node.id, node]));
  for (const rule of [...supportedRules, ...missingRules]) {
    if (!byId.has(`K.${rule}`)) {
      return invalid0(
        ['LegacyGlobalProofDAG', 'Nodes', 'kernel', rule],
        'Transport semantic overlay requires a legacy kernel coordinate for every required primitive rule',
        { rule },
      );
    }
  }
  const requiredFinalNodeIds = [...GLOBAL_DAG_REQUIRED_FINALS0];
  for (const id of requiredFinalNodeIds) {
    if (byId.get(id)?.nodeKind !== 'final') {
      return invalid0(
        ['LegacyGlobalProofDAG', 'Nodes', 'final', id],
        'Transport semantic overlay requires every legacy final coordinate as a quarantined final node',
        { id, actualKind: byId.get(id)?.nodeKind ?? null },
      );
    }
  }
  const semanticKernelNodeIds = supportedRules.map((rule) => `K.${rule}`);
  const blockedKernelNodeIds = missingRules.map((rule) => `K.${rule}`);
  const structuralOnlyNodeIds = nodes
    .filter((node) => !semanticKernelNodeIds.includes(node.id))
    .map((node) => node.id);
  return valid0({
    kind: 'GlobalProofDAGSemanticTransportOverlay0NF',
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

function makeGate0(
  predecessorRecord,
  predecessorNF,
  developmentRecord,
  developmentNF,
  finalRecord,
  kBundleFinalReady,
  overlay,
) {
  const predecessorDigest = digestOf0(predecessorRecord);
  const developmentDigest = digestOf0(developmentRecord);
  const finalDigest = digestOf0(finalRecord);
  const nodes = [
    gateNode0('Gate.PredecessorGlobal.DevelopmentAcceptance', [], true, predecessorDigest),
    gateNode0(
      'Gate.KBundle.TransportDevelopmentAcceptance',
      ['Gate.PredecessorGlobal.DevelopmentAcceptance'],
      true,
      developmentDigest,
    ),
    gateNode0(
      'Gate.KBundle.TransportFinalReadiness',
      ['Gate.KBundle.TransportDevelopmentAcceptance'],
      kBundleFinalReady,
      finalDigest,
    ),
    gateNode0(
      'Gate.GlobalDAG.StructuralAcceptance',
      ['Gate.PredecessorGlobal.DevelopmentAcceptance'],
      predecessorNF.legacyGlobalDAGAccepted === true,
      predecessorNF.legacyGlobalDAGDigest ?? null,
    ),
    gateNode0(
      'Gate.GlobalDAG.SemanticNodeDerivations',
      [
        'Gate.KBundle.TransportDevelopmentAcceptance',
        'Gate.GlobalDAG.StructuralAcceptance',
      ],
      overlay.globalSemanticNodeDerivationsReady === true,
      digestCanonical0(overlay),
    ),
  ];
  const finalReady = kBundleFinalReady
    && overlay.globalSemanticNodeDerivationsReady === true;
  nodes.push(gateNode0(
    'Gate.FinalTheorem.Readiness',
    [
      'Gate.KBundle.TransportFinalReadiness',
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
      coordinate: 'KBundle.TransportFinalReadiness',
      ready: kBundleFinalReady,
      reason: kBundleFinalReady
        ? null
        : 'Transport successor KBundle semantic readiness remains blocked',
      digest: finalDigest,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.SemanticNodeDerivations',
      ready: overlay.globalSemanticNodeDerivationsReady === true,
      reason: overlay.globalSemanticNodeDerivationsReady === true
        ? null
        : 'legacy kernel, Sigma, reflection, package, and final nodes have not been migrated to semantic derivations',
      digest: digestCanonical0(overlay),
    }),
  ];
  return Object.freeze({
    kind: 'GlobalProofDAGComputedSemanticTransportGate0',
    version: VERSION,
    semanticKBundleComputedReadinessDigest:
      developmentNF.computedReadinessDigest ?? null,
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
  if (!plain0(input)) {
    return invalid0([], 'Transport semantic global-DAG input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'GlobalProofDAGSemanticTransportSuccessor0') {
    return invalid0(
      ['kind'],
      'Transport semantic global-DAG kind must be GlobalProofDAGSemanticTransportSuccessor0',
      { actual: input.kind },
    );
  }
  if (input.version !== VERSION) {
    return invalid0(['version'], `Transport semantic global-DAG version must be ${VERSION}`, {
      actual: input.version,
    });
  }
  if (!GLOBAL_DAG_TRANSPORT_SUCCESSOR_PURPOSES0.includes(input.Purpose)) {
    return invalid0(['Purpose'], 'Transport semantic global-DAG Purpose is unsupported', {
      actual: input.Purpose,
      supportedPurposes: [...GLOBAL_DAG_TRANSPORT_SUCCESSOR_PURPOSES0],
    });
  }
  if (!plain0(input.KBundle)) {
    return invalid0(['KBundle'], 'Transport semantic global-DAG KBundle must be an object', {
      actual: typeof input.KBundle,
    });
  }
  if (input.KBundle.Purpose !== 'development') {
    return invalid0(
      ['KBundle', 'Purpose'],
      'Transport semantic global-DAG input KBundle must remain development-purpose; final readiness is recomputed internally',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!plain0(input.LegacyGlobalProofDAG)) {
    return invalid0(
      ['LegacyGlobalProofDAG'],
      'Transport semantic global-DAG must include a legacy global DAG object',
      { actual: typeof input.LegacyGlobalProofDAG },
    );
  }
  if (!same0(input.Binding, GLOBAL_DAG_TRANSPORT_SUCCESSOR_BINDING0)) {
    return invalid0(
      ['Binding'],
      'Transport semantic global-DAG checker binding must match the executable checker boundary',
      { expected: GLOBAL_DAG_TRANSPORT_SUCCESSOR_BINDING0, actual: input.Binding },
    );
  }
  if (!same0(input.Policy, GLOBAL_DAG_TRANSPORT_SUCCESSOR_POLICY0)) {
    return invalid0(
      ['Policy'],
      'Transport semantic global-DAG release policy must match the fail-closed policy',
      { expected: GLOBAL_DAG_TRANSPORT_SUCCESSOR_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind', 'version', 'Purpose', 'KBundle',
    'LegacyGlobalProofDAG', 'Binding', 'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return invalid0(
      [unexpected[0]],
      'Transport semantic global-DAG rejects caller-supplied readiness assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return valid0({
    kind: 'GlobalProofDAGSemanticTransportSuccessorShape0NF',
    purpose: input.Purpose,
  });
}

function validatePredecessor0(nf) {
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
      return invalid0(
        ['PredecessorGlobal', 'NF', field],
        'IntArith predecessor global gate did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0) {
    return invalid0(
      ['PredecessorGlobal', 'NF', 'activeFinalNodeIds'],
      'IntArith predecessor global gate must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }
  if (!same0(
    nf.semanticOverlay?.semanticKernelNodeIds,
    PREDECESSOR_NODE_IDS0,
  )) {
    return invalid0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'semanticKernelNodeIds'],
      'IntArith predecessor global semantic-kernel node set mismatch',
      {
        expected: PREDECESSOR_NODE_IDS0,
        actual: nf.semanticOverlay?.semanticKernelNodeIds,
      },
    );
  }
  return valid0({ ...expected, semanticKernelNodeIds: [...PREDECESSOR_NODE_IDS0] });
}

function validateDevelopmentBundle0(nf) {
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
      return invalid0(
        ['KBundle', 'NF', field],
        'Transport semantic KBundle did not preserve its development-only boundary',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!same0(
    nf.semanticKImplSupportedRules,
    SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0,
  )) {
    return invalid0(
      ['KBundle', 'NF', 'semanticKImplSupportedRules'],
      'Transport semantic KBundle supported-rule set mismatch',
      {
        expected: [...SEMANTIC_KERNEL_SUPPORTED_RULES_TRANSPORT0],
        actual: nf.semanticKImplSupportedRules,
      },
    );
  }
  return valid0({ ...expected });
}

function extractNodes0(input) {
  if (Array.isArray(input)) return { ...valid0({ form: 'array' }), nodes: input };
  if (!plain0(input)) {
    return invalid0(
      ['KBundle', 'SemanticKImpl', 'SemanticKernel', 'ProofDAG'],
      'semantic proof DAG must be an array or object',
      { actual: typeof input },
    );
  }
  const nodes = input.nodes ?? input.ProofDAG ?? input.proofDAG;
  if (!Array.isArray(nodes)) {
    return invalid0(
      ['KBundle', 'SemanticKImpl', 'SemanticKernel', 'ProofDAG', 'nodes'],
      'semantic proof DAG must provide a nodes array',
      { actual: typeof nodes },
    );
  }
  return { ...valid0({ form: 'object', nodeCount: nodes.length }), nodes };
}

async function call0(name, thunk) {
  try {
    const record = await thunk();
    if (!plain0(record) || !['accept', 'reject'].includes(record.tag)) {
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

function finalReady0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && nf?.finalTheoremReady === true
    && nf?.publicTheoremEmissionAllowed === true;
}

function gateNode0(id, premises, ready, digest) {
  return Object.freeze({ id, premises: Object.freeze([...premises]), ready, digest });
}

function push0(ledger, phase, ok, material) {
  ledger.push({
    phase,
    status: ok ? 'pass' : 'fail',
    digest: digestCanonical0(material ?? null),
  });
}

function accept0(checker, nf, ledger) {
  const digest = digestCanonical0(nf);
  return {
    tag: 'accept', kind: 'accept', checker, version: VERSION,
    NF: nf, Digest: digest, Ledger: ledger,
    nf, digest, ledger,
  };
}

function rejectValidation0(checker, coord, result, ledger) {
  return reject0(checker, coord, result.path, result.witness, ledger);
}

function reject0(checker, coord, path, witness, ledger) {
  const nf = {
    kind: `${checker}RejectNF`, checker, version: VERSION,
    coord, path, witness, ledger,
  };
  const digest = digestCanonical0(nf);
  return {
    tag: 'reject', kind: 'reject', checker, version: VERSION,
    Coord: coord, Path: path, Witness: witness, Digest: digest, Ledger: ledger,
    coord, path, witness, digest, ledger,
  };
}

function valid0(nf) {
  return { ok: true, nf };
}

function invalid0(path, reason, details = {}) {
  return { ok: false, path, witness: { reason, ...(details ?? {}) } };
}

function compact0(record) {
  return {
    tag: record?.tag ?? null,
    checker: record?.checker ?? null,
    coord: record?.Coord ?? record?.coord ?? null,
    path: record?.Path ?? record?.path ?? null,
    witness: record?.Witness ?? record?.witness ?? null,
    digest: digestOf0(record),
  };
}

function digestOf0(record) {
  return record?.Digest ?? record?.digest ?? null;
}

function same0(left, right) {
  return stableStringify0(left) === stableStringify0(right);
}

function plain0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return false;
  }
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

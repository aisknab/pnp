import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGFinalPrefixSuccessor0,
  makeGlobalProofDAGFinalPrefixSuccessor0,
} from './pcc-global-proof-dag-final-prefix-successor0.mjs';

import {
  makeGlobalInfrastructureSemanticSuite0,
} from './pcc-global-infrastructure-semantic0.mjs';

import {
  makeKBundleReflectionSuccessor0,
} from './pcc-kbundle-reflection-successor0.mjs';

import {
  makeSyntheticRowPack0,
} from './pcc-rows0.mjs';

import {
  makeSyntheticRowFamG0,
} from './pcc-gpack0.mjs';

import {
  makeGlobalRowSemanticSuite0,
} from './pcc-global-row-semantic0.mjs';

import {
  makeSyntheticLocalPackages0,
} from './pcc-local-packages0.mjs';

import {
  makeGlobalPackageSemanticSuite0,
} from './pcc-global-package-semantic0.mjs';

import {
  makeGlobalFinalPrefixPCCPack0,
  makeGlobalFinalPrefixSemanticSuite0,
} from './pcc-global-final-prefix-contract0.mjs';

import {
  CheckGlobalFinalSATSemantic0,
  GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  GLOBAL_FINAL_SAT_NODE_ID0,
  GLOBAL_FINAL_SAT_SEMANTIC_SCOPE0,
  makeGlobalFinalSATSemanticInput0,
  makeGlobalFinalSATSemanticSuite0,
} from './pcc-global-final-sat-semantic0.mjs';

const CHECKER_VERSION = 0;
const GLOBAL_FINAL_PREFIX_NODE_IDS0 = Object.freeze([
  'Final.PackageSoundness',
  'Final.GeneratedPackageSufficiency',
]);

export const GLOBAL_DAG_FINAL_SAT_SUCCESSOR_PURPOSES0 = Object.freeze([
  'development',
  'final-theorem',
]);

export const GLOBAL_DAG_FINAL_SAT_SUCCESSOR_POLICY0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticFinalSATReleasePolicy0',
  version: CHECKER_VERSION,
  semanticKBundleInputMustRemainDevelopmentPurpose: true,
  finalPrefixPredecessorMustRemainDevelopmentOnly: true,
  finalPrefixPredecessorCannotImplyPublicFinalReadiness: true,
  finalSATRefinementMustBeComputed: true,
  finalSATNodeBindsSemanticRefinementDigest: true,
  boundedExecutableSATReductionRefinementOnly: true,
  unrestrictedSATReductionSoundnessNotClaimed: true,
  complexityImplicationRemainsBlocked: true,
  allFinalNodesRemainPubliclyQuarantinedUntilComplexityReady: true,
  finalTheoremRequiresCompleteGlobalSemanticNodeDerivations: true,
  publicTheoremEmissionRequiresGlobalFinalReadiness: true,
  callerReadinessAssertionsForbidden: true,
});

export const GLOBAL_DAG_FINAL_SAT_SUCCESSOR_BINDING0 = Object.freeze({
  kind: 'GlobalProofDAGSemanticFinalSATCheckerBinding0',
  version: CHECKER_VERSION,
  predecessorGlobalChecker: 'CheckGlobalProofDAGFinalPrefixSuccessor0',
  semanticFinalSATChecker: 'CheckGlobalFinalSATSemantic0',
});

export function makeGlobalProofDAGFinalSATSuccessor0({
  KBundle = makeKBundleReflectionSuccessor0(),
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  InfrastructureSemanticDerivations = makeGlobalInfrastructureSemanticSuite0({
    LegacyGlobalProofDAG,
  }),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
  RowSemanticDerivations = makeGlobalRowSemanticSuite0({
    LegacyGlobalProofDAG,
    RowPack,
    RowFamG,
  }),
  LocalPackages = makeSyntheticLocalPackages0(),
  PackageSemanticDerivations = makeGlobalPackageSemanticSuite0({
    LegacyGlobalProofDAG,
    LocalPackages,
  }),
  PCCPack = makeGlobalFinalPrefixPCCPack0({
    LegacyGlobalProofDAG,
    RowPack,
    RowFamG,
    LocalPackages,
  }),
  FinalPrefixSemanticDerivations = makeGlobalFinalPrefixSemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
  }),
  FinalSATSemanticDerivations = makeGlobalFinalSATSemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
  }),
  Purpose = 'development',
} = {}) {
  if (!GLOBAL_DAG_FINAL_SAT_SUCCESSOR_PURPOSES0.includes(Purpose)) {
    throw new TypeError(
      `makeGlobalProofDAGFinalSATSuccessor0 Purpose must be one of ${GLOBAL_DAG_FINAL_SAT_SUCCESSOR_PURPOSES0.join(', ')}`,
    );
  }
  return {
    kind: 'GlobalProofDAGSemanticFinalSATSuccessor0',
    version: CHECKER_VERSION,
    Purpose,
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations,
    RowPack,
    RowFamG,
    RowSemanticDerivations,
    LocalPackages,
    PackageSemanticDerivations,
    PCCPack,
    FinalPrefixSemanticDerivations,
    FinalSATSemanticDerivations,
    Binding: { ...GLOBAL_DAG_FINAL_SAT_SUCCESSOR_BINDING0 },
    Policy: { ...GLOBAL_DAG_FINAL_SAT_SUCCESSOR_POLICY0 },
  };
}

export async function CheckGlobalProofDAGFinalSATSuccessor0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGFinalSATSuccessor0',
    requiredPurpose: null,
  });
}

export async function CheckGlobalProofDAGFinalSATFinalTheoremReadiness0(input) {
  return checkGlobalInternal0(input, {
    checker: 'CheckGlobalProofDAGFinalSATFinalTheoremReadiness0',
    requiredPurpose: 'final-theorem',
  });
}

async function checkGlobalInternal0(input, { checker, requiredPurpose }) {
  const ledger = [];
  const shape = validateShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);

  if (requiredPurpose !== null && input.Purpose !== requiredPurpose) {
    const witness = {
      reason: 'semantic final SAT global readiness requires a final-theorem purpose record',
      requiredPurpose,
      actualPurpose: input.Purpose,
    };
    ledger.push(makeLedgerEntry0('purpose', false, witness));
    return makeRejectRecord0({ checker, coord: `${checker}.purpose`, path: ['Purpose'], witness, ledger });
  }

  const purpose = requiredPurpose ?? input.Purpose;
  ledger.push(makeLedgerEntry0('purpose', true, {
    kind: 'GlobalProofDAGFinalSATPurpose0NF',
    purpose,
  }));

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGFinalPrefixSuccessor0',
    () => CheckGlobalProofDAGFinalPrefixSuccessor0(
      makeGlobalProofDAGFinalPrefixSuccessor0({
        KBundle: input.KBundle,
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        InfrastructureSemanticDerivations: input.InfrastructureSemanticDerivations,
        RowPack: input.RowPack,
        RowFamG: input.RowFamG,
        RowSemanticDerivations: input.RowSemanticDerivations,
        LocalPackages: input.LocalPackages,
        PackageSemanticDerivations: input.PackageSemanticDerivations,
        PCCPack: input.PCCPack,
        FinalPrefixSemanticDerivations: input.FinalPrefixSemanticDerivations,
        Purpose: 'development',
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGFinalPrefixSuccessor0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({ checker, coord: `${checker}.predecessorGlobal.exception`, path: ['PredecessorGlobal'], witness: predecessorCall.witness, ledger });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.predecessorGlobal`,
      path: ['PredecessorGlobal'],
      witness: {
        reason: 'semantic final-prefix predecessor global gate rejected before final SAT upgrade',
        inner: compactRecord0(predecessorCall.record),
      },
      ledger,
    });
  }
  const predecessorRecord = predecessorCall.record;
  const predecessorNF = predecessorRecord.NF ?? predecessorRecord.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0('predecessorFinalPrefixBoundary', predecessorBoundary.ok, predecessorBoundary.nf ?? predecessorBoundary.witness));
  if (!predecessorBoundary.ok) return makeRejectFromValidation0(checker, `${checker}.predecessorFinalPrefixBoundary`, predecessorBoundary, ledger);

  const satCall = await callChecker0(
    'CheckGlobalFinalSATSemantic0',
    () => CheckGlobalFinalSATSemantic0(
      makeGlobalFinalSATSemanticInput0({
        KBundle: input.KBundle,
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        InfrastructureSemanticDerivations: input.InfrastructureSemanticDerivations,
        RowPack: input.RowPack,
        RowFamG: input.RowFamG,
        RowSemanticDerivations: input.RowSemanticDerivations,
        LocalPackages: input.LocalPackages,
        PackageSemanticDerivations: input.PackageSemanticDerivations,
        PCCPack: input.PCCPack,
        FinalPrefixSemanticDerivations: input.FinalPrefixSemanticDerivations,
        SemanticFinalSAT: input.FinalSATSemanticDerivations,
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalFinalSATSemantic0',
    satCall.ok && satCall.record.tag === 'accept',
    satCall.ok ? satCall.record : satCall.witness,
  ));
  if (!satCall.ok) return makeRejectRecord0({ checker, coord: `${checker}.semanticFinalSAT.exception`, path: ['FinalSATSemanticDerivations'], witness: satCall.witness, ledger });
  if (satCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticFinalSAT`,
      path: ['FinalSATSemanticDerivations'],
      witness: {
        reason: 'bounded semantic final SAT refinement checker rejected',
        inner: compactRecord0(satCall.record),
      },
      ledger,
    });
  }
  const satRecord = satCall.record;
  const satNF = satRecord.NF ?? satRecord.nf ?? {};
  const satBoundary = validateSATBoundary0(satNF);
  ledger.push(makeLedgerEntry0('semanticFinalSATBoundary', satBoundary.ok, satBoundary.nf ?? satBoundary.witness));
  if (!satBoundary.ok) return makeRejectFromValidation0(checker, `${checker}.semanticFinalSATBoundary`, satBoundary, ledger);

  const overlay = buildFinalSATOverlay0({ dag: input.LegacyGlobalProofDAG, predecessorNF, satNF });
  ledger.push(makeLedgerEntry0('semanticFinalSATOverlay', overlay.ok, overlay.nf ?? overlay.witness));
  if (!overlay.ok) return makeRejectFromValidation0(checker, `${checker}.semanticOverlay`, overlay, ledger);

  const gate = makeComputedGate0({ predecessorRecord, predecessorNF, satRecord, overlay: overlay.nf });
  ledger.push(makeLedgerEntry0('computedGlobalSemanticGate', gate.finalTheoremReady, gate));

  if (purpose === 'final-theorem' && !gate.finalTheoremReady) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticReadiness`,
      path: ['ComputedGlobalGate'],
      witness: {
        reason: 'semantic final SAT global successor is not ready for final-theorem use',
        blockers: gate.blockers,
        semanticallyRefinedFinalNodeIds: gate.semanticallyRefinedFinalNodeIds,
        remainingBlockedFinalNodeIds: gate.remainingBlockedFinalNodeIds,
        quarantinedFinalNodeIds: gate.quarantinedFinalNodeIds,
        complexityClassImplicationNotClaimed: true,
      },
      ledger,
    });
  }

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalProofDAGSemanticFinalSATSuccessor0NF',
      checker,
      version: CHECKER_VERSION,
      purpose,
      status: 'development-only',
      predecessorGlobalAccepted: true,
      predecessorGlobalChecker: predecessorRecord.checker,
      predecessorGlobalDigest: predecessorRecord.Digest ?? predecessorRecord.digest,
      predecessorGlobalDevelopmentOnly: true,
      predecessorGlobalPublicTheoremEmissionAllowed: false,
      predecessorGlobalFinalPrefixReady: true,
      predecessorGlobalFinalSATReady: false,
      semanticKBundleFinalReady: predecessorNF.semanticKBundleFinalReady === true,
      semanticK0ConformanceReady: predecessorNF.semanticK0ConformanceReady === true,
      semanticSigmaReady: predecessorNF.semanticSigmaReady === true,
      semanticReflectionReady: predecessorNF.semanticReflectionReady === true,
      globalInfrastructureSemanticReady: predecessorNF.globalInfrastructureSemanticReady === true,
      globalRowDerivationsReady: predecessorNF.globalRowDerivationsReady === true,
      globalPackageDerivationsReady: predecessorNF.globalPackageDerivationsReady === true,
      globalFinalPrefixRefinementsReady: predecessorNF.globalFinalPrefixRefinementsReady === true,
      globalFinalSATSemanticChecker: satRecord.checker,
      globalFinalSATSemanticDigest: satRecord.Digest ?? satRecord.digest,
      globalFinalSATSemanticReady: true,
      globalFinalSATReductionDerivationReady: true,
      globalAcceptedPackageImpliesSATinPRefinementReady: true,
      globalFinalSATNodeId: GLOBAL_FINAL_SAT_NODE_ID0,
      globalFinalSATRefinementDigest: satNF.refinementDigest ?? satRecord.Digest ?? satRecord.digest,
      globalFinalSATRefinementDigests: [{
        nodeId: GLOBAL_FINAL_SAT_NODE_ID0,
        digest: satNF.refinementDigest ?? satRecord.Digest ?? satRecord.digest,
        globalNodeDigest: satNF.globalNodeDigest,
        finalIntegrationDigest: satNF.finalIntegrationDigest,
        satDecisionDigest: satNF.satDecisionDigest,
        satBoundsDigest: satNF.satBoundsDigest,
        checkerContractDigest: satNF.checkerContractDigest,
        conclusionDigest: satNF.conclusionDigest,
      }],
      boundedExecutableSATReductionRefinementOnly: true,
      unrestrictedSATReductionSoundnessNotClaimed: true,
      complexityClassImplicationNotClaimed: true,
      globalFinalComplexityImplicationReady: false,
      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      Scope: { ...GLOBAL_FINAL_SAT_SEMANTIC_SCOPE0 },
      semanticOverlay: overlay.nf,
      semanticOverlayDigest: digestCanonical0(overlay.nf),
      computedGlobalGate: gate,
      computedGlobalGateDigest: digestCanonical0(gate),
      semanticallyRefinedFinalNodeIds: gate.semanticallyRefinedFinalNodeIds,
      remainingBlockedFinalNodeIds: gate.remainingBlockedFinalNodeIds,
      legacyFinalNodesStructurallyAccepted: true,
      legacyFinalNodesQuarantined: true,
      semanticallyRefinedFinalNodesRemainPubliclyQuarantined: true,
      activeFinalNodeIds: [],
      quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
      developmentOnly: true,
      finalTheoremReady: false,
      publicTheoremEmissionAllowed: false,
      finalTheoremRequiresCompleteGlobalSemanticNodeDerivations: true,
      bindingDigest: digestCanonical0(input.Binding),
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function buildFinalSATOverlay0({ dag, predecessorNF, satNF }) {
  const nodes = dag?.Nodes;
  if (!Array.isArray(nodes)) return validationReject0(['LegacyGlobalProofDAG', 'Nodes'], 'legacy global DAG must expose Nodes for final SAT overlay', { actual: typeof nodes });
  const predecessorOverlay = predecessorNF.semanticOverlay;
  if (!isPlainObject0(predecessorOverlay) || predecessorOverlay.globalFinalPrefixRefinementsReady !== true || predecessorOverlay.globalFinalSATReductionDerivationReady !== false) {
    return validationReject0(['PredecessorGlobal', 'NF', 'semanticOverlay'], 'final SAT successor requires the semantic final-prefix predecessor overlay', { actual: predecessorOverlay });
  }
  const node = new Map(nodes.map((entry) => [entry.id, entry])).get(GLOBAL_FINAL_SAT_NODE_ID0);
  const nodeDigest = digestCanonical0(stripDigestFields0(node));
  if (!sameCanonical0(nodeDigest, satNF.globalNodeDigest)) {
    return validationReject0(['FinalSATSemanticDerivations', 'NF', 'globalNodeDigest'], 'final SAT semantic node digest mismatch', { expected: nodeDigest, actual: satNF.globalNodeDigest });
  }
  const semanticFinalSATBinding = Object.freeze({
    nodeId: GLOBAL_FINAL_SAT_NODE_ID0,
    nodeKind: 'final',
    globalNodeDigest: nodeDigest,
    refinementDigest: satNF.refinementDigest,
    dependencyNodeDigests: satNF.dependencyNodeDigests,
    finalIntegrationDigest: satNF.finalIntegrationDigest,
    satDecisionDigest: satNF.satDecisionDigest,
    satBoundsDigest: satNF.satBoundsDigest,
    checkerContractDigest: satNF.checkerContractDigest,
    conclusionDigest: satNF.conclusionDigest,
    scope: GLOBAL_FINAL_SAT_SEMANTIC_SCOPE0.scope,
    boundedExecutableSATReductionRefinement: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    publiclyActive: false,
  });
  const semanticFinalPrefixNodeIds = [...(predecessorOverlay.semanticFinalPrefixNodeIds ?? [])];
  const semanticNodeIds = [...(predecessorOverlay.semanticNodeIds ?? []), GLOBAL_FINAL_SAT_NODE_ID0];
  const structuralOnlyNodeIds = nodes.filter((entry) => !semanticNodeIds.includes(entry.id)).map((entry) => entry.id);
  return validationAccept0({
    kind: 'GlobalProofDAGSemanticFinalSATOverlay0NF',
    ...copyPriorOverlay0(predecessorOverlay),
    semanticFinalPrefixNodeIds,
    semanticFinalSATNodeIds: [GLOBAL_FINAL_SAT_NODE_ID0],
    semanticFinalNodeIds: [...semanticFinalPrefixNodeIds, GLOBAL_FINAL_SAT_NODE_ID0],
    semanticFinalSATBindings: [semanticFinalSATBinding],
    blockedFinalNodeIds: [GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
    blockedFinalImplicationNodeIds: [GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
    quarantinedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    semanticNodeIds,
    structuralOnlyNodeIds,
    requiredFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    globalFinalPrefixRefinementsReady: true,
    globalFinalSATReductionDerivationReady: true,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    semanticFinalSATNodeCount: 1,
    blockedFinalNodeCount: 1,
    semanticNodeCount: semanticNodeIds.length,
    structuralOnlyNodeCount: structuralOnlyNodeIds.length,
    boundedExecutableSATReductionRefinementOnly: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    semanticallyRefinedFinalNodesRemainPubliclyQuarantined: true,
  });
}

function copyPriorOverlay0(overlay) {
  return {
    semanticKBundleDigest: overlay.semanticKBundleDigest ?? null,
    semanticKernelNodeIds: [...(overlay.semanticKernelNodeIds ?? [])],
    blockedKernelNodeIds: [],
    semanticSigmaNodeIds: [...(overlay.semanticSigmaNodeIds ?? [])],
    blockedSigmaNodeIds: [],
    semanticSigmaBindings: overlay.semanticSigmaBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticReflectionNodeIds: [...(overlay.semanticReflectionNodeIds ?? [])],
    blockedReflectionNodeIds: [],
    semanticReflectionBindings: overlay.semanticReflectionBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticInfrastructureNodeIds: [...(overlay.semanticInfrastructureNodeIds ?? [])],
    blockedInfrastructureNodeIds: [],
    semanticInfrastructureBindings: overlay.semanticInfrastructureBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticRowNodeIds: [...(overlay.semanticRowNodeIds ?? [])],
    blockedRowNodeIds: [],
    semanticRowBindings: overlay.semanticRowBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticPackageNodeIds: [...(overlay.semanticPackageNodeIds ?? [])],
    blockedPackageNodeIds: [],
    semanticPackageBindings: overlay.semanticPackageBindings?.map((entry) => ({ ...entry })) ?? [],
    semanticFinalPrefixBindings: overlay.semanticFinalPrefixBindings?.map((entry) => ({ ...entry })) ?? [],
    primitiveSemanticRuleCoverageComplete: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowDerivationsReady: true,
    globalPackageDerivationsReady: true,
  };
}

function makeComputedGate0({ predecessorRecord, predecessorNF, satRecord, overlay }) {
  const blockers = [
    readyBlocker0('KBundle.ReflectionFinalReadiness', predecessorNF.semanticKBundleFinalProbeDigest ?? null),
    readyBlocker0('GlobalDAG.InfrastructureDerivations', predecessorNF.globalInfrastructureSemanticDigest ?? null),
    readyBlocker0('GlobalDAG.RowDerivations', predecessorNF.globalRowSemanticDigest ?? null),
    readyBlocker0('GlobalDAG.PackageDerivations', predecessorNF.globalPackageSemanticDigest ?? null),
    readyBlocker0('GlobalDAG.FinalPrefixRefinements', predecessorNF.globalFinalPrefixSemanticDigest ?? null),
    readyBlocker0('GlobalDAG.FinalSATReductionDerivation', satRecord.Digest ?? satRecord.digest, {
      boundedExecutableSATReductionRefinementOnly: true,
      unrestrictedSATReductionSoundnessNotClaimed: true,
    }),
    Object.freeze({
      coordinate: 'GlobalDAG.FinalComplexityImplication',
      ready: false,
      reason: 'the SAT-in-P-to-P-equals-NP complexity-class implication remains quarantined until independently represented',
      digest: digestCanonical0(GLOBAL_FINAL_COMPLEXITY_NODE_ID0),
    }),
  ];
  const nodes = [
    gateNode0('Gate.PredecessorFinalPrefix.DevelopmentAcceptance', [], true, predecessorRecord.Digest ?? predecessorRecord.digest),
    gateNode0('Gate.GlobalDAG.FinalSATReductionDerivation', ['Gate.GlobalDAG.FinalPrefixRefinements'], true, satRecord.Digest ?? satRecord.digest),
    gateNode0('Gate.GlobalDAG.FinalComplexityImplication', ['Gate.GlobalDAG.FinalSATReductionDerivation'], false, digestCanonical0(GLOBAL_FINAL_COMPLEXITY_NODE_ID0)),
    gateNode0('Gate.FinalTheorem.Readiness', ['Gate.GlobalDAG.FinalComplexityImplication'], false, digestCanonical0({ complexityReady: false })),
  ];
  return Object.freeze({
    kind: 'GlobalProofDAGComputedSemanticFinalSATGate0',
    version: CHECKER_VERSION,
    globalFinalSATReductionDerivationReady: true,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    nodes: Object.freeze(nodes),
    blockers: Object.freeze(blockers),
    blockerCoordinates: Object.freeze(blockers.filter((entry) => !entry.ready).map((entry) => entry.coordinate)),
    semanticallyRefinedFinalNodeIds: Object.freeze([...GLOBAL_FINAL_PREFIX_NODE_IDS0, GLOBAL_FINAL_SAT_NODE_ID0]),
    remainingBlockedFinalNodeIds: Object.freeze([GLOBAL_FINAL_COMPLEXITY_NODE_ID0]),
    requiredFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    quarantinedFinalNodeIds: Object.freeze([...GLOBAL_DAG_REQUIRED_FINALS0]),
    semanticFinalNodesPubliclyActive: false,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    overlayDigest: digestCanonical0(overlay),
  });
}

function gateNode0(id, premises, ready, digest) {
  return Object.freeze({ id, premises: Object.freeze([...premises]), ready, digest });
}

function readyBlocker0(coordinate, digest, extra = {}) {
  return Object.freeze({ coordinate, ready: true, reason: null, digest, ...extra });
}

function validateShape0(input) {
  if (!isPlainObject0(input)) return validationReject0([], 'semantic final SAT global successor input must be an object', { actual: typeof input });
  if (input.kind !== 'GlobalProofDAGSemanticFinalSATSuccessor0') return validationReject0(['kind'], 'semantic final SAT global successor kind must be GlobalProofDAGSemanticFinalSATSuccessor0', { actual: input.kind });
  if (input.version !== CHECKER_VERSION) return validationReject0(['version'], `semantic final SAT global successor version must be ${CHECKER_VERSION}`, { actual: input.version });
  if (!GLOBAL_DAG_FINAL_SAT_SUCCESSOR_PURPOSES0.includes(input.Purpose)) return validationReject0(['Purpose'], 'semantic final SAT global successor Purpose is unsupported', { actual: input.Purpose });
  const required = ['KBundle', 'LegacyGlobalProofDAG', 'InfrastructureSemanticDerivations', 'RowPack', 'RowFamG', 'RowSemanticDerivations', 'LocalPackages', 'PackageSemanticDerivations', 'PCCPack', 'FinalPrefixSemanticDerivations', 'FinalSATSemanticDerivations', 'Binding', 'Policy'];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) return validationReject0([field], 'semantic final SAT global successor is missing a required field', { field });
  }
  for (const field of required.slice(0, 11)) {
    if (!isPlainObject0(input[field])) return validationReject0([field], 'semantic final SAT global dependency surface must be an object', { field, actual: typeof input[field] });
  }
  if (input.KBundle.Purpose !== 'development') return validationReject0(['KBundle', 'Purpose'], 'semantic final SAT global input KBundle must remain development-purpose', { actual: input.KBundle.Purpose });
  if (!sameCanonical0(input.Binding, GLOBAL_DAG_FINAL_SAT_SUCCESSOR_BINDING0)) return validationReject0(['Binding'], 'semantic final SAT global checker binding mismatch', { expected: GLOBAL_DAG_FINAL_SAT_SUCCESSOR_BINDING0, actual: input.Binding });
  if (!sameCanonical0(input.Policy, GLOBAL_DAG_FINAL_SAT_SUCCESSOR_POLICY0)) return validationReject0(['Policy'], 'semantic final SAT global release policy must match the fail-closed policy', { expected: GLOBAL_DAG_FINAL_SAT_SUCCESSOR_POLICY0, actual: input.Policy });
  const allowed = new Set(['kind', 'version', 'Purpose', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) return validationReject0([unexpected[0]], 'semantic final SAT global successor rejects caller-supplied readiness assertions', { unexpectedFields: unexpected.sort() });
  return validationAccept0({ kind: 'GlobalProofDAGSemanticFinalSATSuccessorShape0NF', purpose: input.Purpose });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    status: 'development-only',
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    globalFinalPrefixRefinementsReady: true,
    globalFinalSATReductionDerivationReady: false,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) return validationReject0(['PredecessorGlobal', 'NF', field], 'final-prefix predecessor global boundary mismatch', { field, expected: value, actual: nf[field] });
  }
  if (!nf.remainingBlockedFinalNodeIds?.includes(GLOBAL_FINAL_SAT_NODE_ID0) || !sameCanonical0(nf.activeFinalNodeIds, [])) {
    return validationReject0(['PredecessorGlobal', 'NF'], 'final-prefix predecessor must block SAT final node and expose no active final node', { remainingBlockedFinalNodeIds: nf.remainingBlockedFinalNodeIds, activeFinalNodeIds: nf.activeFinalNodeIds });
  }
  return validationAccept0({ kind: 'GlobalProofDAGFinalSATPredecessorBoundary0NF', ...expected });
}

function validateSATBoundary0(nf) {
  const expected = {
    globalFinalSATSemanticReady: true,
    globalFinalSATReductionDerivationReady: true,
    globalAcceptedPackageImpliesSATinPRefinementReady: true,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    boundedExecutableSATReductionRefinementOnly: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    publicTheoremEmissionAllowed: false,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) return validationReject0(['FinalSATSemanticDerivations', 'NF', field], 'bounded final SAT semantic readiness boundary mismatch', { field, expected: value, actual: nf[field] });
  }
  if (nf.finalSATNodeId !== GLOBAL_FINAL_SAT_NODE_ID0 || nf.remainingFinalComplexityNodeId !== GLOBAL_FINAL_COMPLEXITY_NODE_ID0) {
    return validationReject0(['FinalSATSemanticDerivations', 'NF'], 'bounded final SAT node coverage mismatch', { finalSATNodeId: nf.finalSATNodeId, remainingFinalComplexityNodeId: nf.remainingFinalComplexityNodeId });
  }
  return validationAccept0({ kind: 'GlobalProofDAGFinalSATSemanticBoundary0NF', ...expected });
}

function stripDigestFields0(value) {
  if (!isPlainObject0(value)) return value;
  const out = {};
  for (const key of Object.keys(value).sort()) {
    if (key !== 'Digest' && key !== 'digest') out[key] = value[key];
  }
  return out;
}

async function callChecker0(name, thunk) {
  try {
    const record = await thunk();
    if (!isPlainObject0(record) || !['accept', 'reject'].includes(record.tag)) return { ok: false, witness: { reason: `${name} did not return a total accept/reject record`, actual: record } };
    return { ok: true, record };
  } catch (error) {
    return { ok: false, witness: { reason: `${name} threw instead of returning a reject record`, errorName: error?.name ?? null, errorMessage: error?.message ?? String(error) } };
  }
}

function compactRecord0(record) {
  return { tag: record?.tag ?? null, checker: record?.checker ?? null, coord: record?.Coord ?? record?.coord ?? null, path: record?.Path ?? record?.path ?? null, witness: record?.Witness ?? record?.witness ?? null, digest: record?.Digest ?? record?.digest ?? null };
}

function makeLedgerEntry0(phase, ok, material) {
  return { phase, status: ok ? 'pass' : 'fail', digest: digestCanonical0(material ?? null) };
}

function makeAcceptRecord0({ checker, nf, ledger }) {
  const digest = digestCanonical0(nf);
  return { tag: 'accept', kind: 'accept', checker, version: CHECKER_VERSION, NF: nf, Digest: digest, Ledger: ledger, nf, digest, ledger };
}

function makeRejectFromValidation0(checker, coord, result, ledger) {
  return makeRejectRecord0({ checker, coord, path: result.path, witness: result.witness, ledger });
}

function makeRejectRecord0({ checker, coord, path, witness, ledger }) {
  const nf = { kind: `${checker}RejectNF`, checker, version: CHECKER_VERSION, coord, path, witness, ledger };
  const digest = digestCanonical0(nf);
  return { tag: 'reject', kind: 'reject', checker, version: CHECKER_VERSION, Coord: coord, Path: path, Witness: witness, Digest: digest, Ledger: ledger, coord, path, witness, digest, ledger };
}

function validationAccept0(nf) {
  return { ok: true, nf };
}

function validationReject0(path, reason, details = {}) {
  return { ok: false, path, witness: { reason, ...(details ?? {}) } };
}

function sameCanonical0(left, right) {
  return stableStringify0(left) === stableStringify0(right);
}

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGFinalSATReductionSuccessor0,
  makeGlobalProofDAGFinalSATReductionSuccessor0,
} from './pcc-global-proof-dag-final-sat-reduction-successor0.mjs';

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
} from './pcc-global-final-prefix-semantic0.mjs';

import {
  makeGlobalFinalSATReductionSemanticSuite0,
} from './pcc-global-final-sat-reduction-semantic0.mjs';

import {
  CheckFinal0,
} from './pcc-final0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_FINAL_COMPLEXITY_NODE_ID0 =
  'Final.AcceptedPackageImpliesPEqualsNP';

export const GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0 =
  'Final.AcceptedPackageImpliesSATinP';

export const GLOBAL_FINAL_COMPLEXITY_SCOPE0 = Object.freeze({
  kind: 'GlobalFinalComplexitySemanticScope0',
  version: CHECKER_VERSION,
  scope: 'bounded-executable-final-complexity-implication-refinement',
  finalSATReductionPredecessorChecked: true,
  finalTheoremRecordReplayed: true,
  satInPDependencyChecked: true,
  npCompletenessAssumptionChecked: true,
  conditionalPublicClaimBoundaryChecked: true,
  premiseNegativeProbeChecked: true,
  unconditionalClaimNegativeProbeChecked: true,
  boundedExecutableComplexityImplicationOnly: true,
  unrestrictedComplexityImplicationSoundnessNotClaimed: true,
  publicTheoremEmissionNotAllowed: true,
});

export const GLOBAL_FINAL_COMPLEXITY_POLICY0 = Object.freeze({
  kind: 'GlobalFinalComplexitySemanticPolicy0',
  version: CHECKER_VERSION,
  requiresFinalSATReductionSuccessorAcceptance: true,
  requiresFinalTheoremAcceptance: true,
  requiresExactPCCPackSurfaceAlignment: true,
  requiresExactComplexityNodeContract: true,
  requiresSATinPPremise: true,
  requiresSATNPCompletenessPremise: true,
  requiresConditionalClaimBoundary: true,
  requiresPremiseNegativeProbe: true,
  requiresUnconditionalClaimNegativeProbe: true,
  bindsGlobalNodeDigest: true,
  bindsDependencyNodeDigest: true,
  bindsFinalTheoremDigest: true,
  bindsSourceImplicationDigest: true,
  bindsPositiveAndNegativeRecordDigests: true,
  callerReadinessAssertionsForbidden: true,
  boundedExecutableComplexityImplicationOnly: true,
  unrestrictedComplexityImplicationSoundnessNotClaimed: true,
  publicTheoremEmissionRemainsSeparate: true,
});

export const GLOBAL_FINAL_COMPLEXITY_CONTRACT0 = Object.freeze({
  kind: 'GlobalFinalComplexityCheckerContract0',
  version: CHECKER_VERSION,
  nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  nodeKind: 'final',
  label: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  premises: Object.freeze([GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0]),
  conclusionTag: 'FinalTheoremAccepted0',
  theorem: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  sourceImplicationId: 'PackageAcceptanceImpliesPEqualsNP',
  sourceConclusion: 'P = NP',
  requiredAssumptions: Object.freeze([
    'SAT in P',
    'SAT is NP-complete',
  ]),
  requiredFields: Object.freeze([
    'public',
    'conditionalOnPackageAcceptance',
    'usesSATinP',
    'noUnconditionalClaim',
  ]),
  finalTheoremChecker: 'CheckFinal0',
  boundedExecutableComplexityImplicationOnly: true,
  unrestrictedComplexityImplicationSoundnessNotClaimed: true,
});

export function makeGlobalFinalComplexitySemanticSuite0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  PCCPack = makeGlobalFinalPrefixPCCPack0({ LegacyGlobalProofDAG }),
} = {}) {
  const nodeById = new Map(
    (LegacyGlobalProofDAG?.Nodes ?? []).map((node) => [node?.id, node]),
  );
  return Object.freeze({
    kind: 'GlobalFinalComplexitySemanticSuite0',
    version: CHECKER_VERSION,
    suiteId: 'GlobalDAG.final-complexity.semantic.phase39',
    complexityBinding: makeComplexityBinding0({
      node: nodeById.get(GLOBAL_FINAL_COMPLEXITY_NODE_ID0) ?? null,
      dependencyNode:
        nodeById.get(GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0) ?? null,
      PCCPack,
    }),
    Scope: { ...GLOBAL_FINAL_COMPLEXITY_SCOPE0 },
    Policy: { ...GLOBAL_FINAL_COMPLEXITY_POLICY0 },
  });
}

export function makeGlobalFinalComplexitySemanticInput0({
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
  SATReductionSemanticDerivations = makeGlobalFinalSATReductionSemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
  }),
  ComplexitySemanticDerivations = makeGlobalFinalComplexitySemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
  }),
} = {}) {
  return Object.freeze({
    kind: 'GlobalFinalComplexitySemanticInput0',
    version: CHECKER_VERSION,
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
    SATReductionSemanticDerivations,
    ComplexitySemanticDerivations,
    Scope: { ...GLOBAL_FINAL_COMPLEXITY_SCOPE0 },
    Policy: { ...GLOBAL_FINAL_COMPLEXITY_POLICY0 },
  });
}

export async function CheckGlobalFinalComplexitySemantic0(input) {
  const checker = 'CheckGlobalFinalComplexitySemantic0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGFinalSATReductionSuccessor0',
    () => CheckGlobalProofDAGFinalSATReductionSuccessor0(
      makeGlobalProofDAGFinalSATReductionSuccessor0({
        KBundle: input.KBundle,
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        InfrastructureSemanticDerivations:
          input.InfrastructureSemanticDerivations,
        RowPack: input.RowPack,
        RowFamG: input.RowFamG,
        RowSemanticDerivations: input.RowSemanticDerivations,
        LocalPackages: input.LocalPackages,
        PackageSemanticDerivations: input.PackageSemanticDerivations,
        PCCPack: input.PCCPack,
        FinalPrefixSemanticDerivations:
          input.FinalPrefixSemanticDerivations,
        SATReductionSemanticDerivations:
          input.SATReductionSemanticDerivations,
        Purpose: 'development',
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGFinalSATReductionSuccessor0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalSATReductionPredecessor.exception`,
      path: ['SATReductionSemanticDerivations'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalSATReductionPredecessor`,
      path: ['SATReductionSemanticDerivations'],
      witness: {
        reason: 'complexity implication requires an accepted final SAT-reduction predecessor',
        inner: compactRecord0(predecessorCall.record),
      },
      ledger,
    });
  }
  const predecessorNF = predecessorCall.record.NF
    ?? predecessorCall.record.nf
    ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'finalSATReductionPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.finalSATReductionPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const finalCall = await callChecker0(
    'CheckFinal0',
    () => CheckFinal0(input.PCCPack.FinalTheorem),
  );
  ledger.push(makeLedgerEntry0(
    'CheckFinal0',
    finalCall.ok && isFinalTheoremAccept0(finalCall.record),
    finalCall.ok ? finalCall.record : finalCall.witness,
  ));
  if (!finalCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalTheorem.exception`,
      path: ['PCCPack', 'FinalTheorem'],
      witness: finalCall.witness,
      ledger,
    });
  }
  if (!isFinalTheoremAccept0(finalCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalTheorem`,
      path: ['PCCPack', 'FinalTheorem'],
      witness: {
        reason: 'complexity implication requires accepted final theorem metadata',
        inner: compactRecord0(finalCall.record),
      },
      ledger,
    });
  }

  const alignment = validatePackAlignment0(input);
  ledger.push(makeLedgerEntry0(
    'packSurfaceAlignment',
    alignment.ok,
    alignment.nf ?? alignment.witness,
  ));
  if (!alignment.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.packSurfaceAlignment`,
      alignment,
      ledger,
    );
  }

  const suite = validateSemanticSuite0(
    input.ComplexitySemanticDerivations,
    input.LegacyGlobalProofDAG,
    input.PCCPack,
  );
  ledger.push(makeLedgerEntry0(
    'semanticComplexitySuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticComplexitySuite`,
      suite,
      ledger,
    );
  }

  const nodeById = new Map(
    input.LegacyGlobalProofDAG.Nodes.map((node) => [node.id, node]),
  );
  const complexity = await deriveComplexityImplication0({
    node: nodeById.get(GLOBAL_FINAL_COMPLEXITY_NODE_ID0),
    dependencyNode:
      nodeById.get(GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0),
    binding: input.ComplexitySemanticDerivations.complexityBinding,
    pack: input.PCCPack,
    positiveRecord: finalCall.record,
    predecessorNF,
    globalBoundsExponent: input.LegacyGlobalProofDAG.BoundsLedger?.exponent,
  });
  ledger.push(makeLedgerEntry0(
    'finalComplexity.Final.AcceptedPackageImpliesPEqualsNP',
    complexity.ok,
    complexity.nf ?? complexity.witness,
  ));
  if (!complexity.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.finalComplexity.Final.AcceptedPackageImpliesPEqualsNP`,
      complexity,
      ledger,
    );
  }

  const finalNF = finalCall.record.NF ?? finalCall.record.nf ?? {};
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalFinalComplexitySemantic0NF',
      checker,
      version: CHECKER_VERSION,
      globalFinalComplexitySemanticReady: true,
      globalFinalComplexityImplicationReady: true,

      finalSATReductionPredecessorAccepted: true,
      finalSATReductionPredecessorChecker: predecessorCall.record.checker,
      finalSATReductionPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      globalFinalSATReductionDerivationReady:
        predecessorNF.globalFinalSATReductionDerivationReady === true,
      globalFinalPrefixRefinementsReady:
        predecessorNF.globalFinalPrefixRefinementsReady === true,
      globalPackageDerivationsReady:
        predecessorNF.globalPackageDerivationsReady === true,
      globalRowDerivationsReady:
        predecessorNF.globalRowDerivationsReady === true,
      globalInfrastructureSemanticReady:
        predecessorNF.globalInfrastructureSemanticReady === true,
      semanticKBundleFinalReady:
        predecessorNF.semanticKBundleFinalReady === true,

      finalTheoremAccepted: true,
      finalTheoremChecker: finalCall.record.checker,
      finalTheoremDigest: finalCall.record.Digest ?? finalCall.record.digest,
      finalTheoremNFKind: finalNF.kind,
      finalTheoremPublicStatement: finalNF.publicTheorem ?? null,
      finalTheoremExportedStatement: finalNF.exportedStatement ?? null,

      globalFinalComplexityNodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
      globalFinalComplexityDependencyNodeId:
        GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0,
      complexityImplicationDerivation: complexity.nf,
      complexityImplicationDerivationDigest: complexity.nf.derivationDigest,
      complexityImplicationBindingDigest: complexity.nf.bindingDigest,

      Scope: { ...GLOBAL_FINAL_COMPLEXITY_SCOPE0 },
      scopeDigest: digestCanonical0(input.Scope),
      boundedExecutableComplexityImplicationOnly: true,
      unrestrictedComplexityImplicationSoundnessNotClaimed: true,
      pEqualsNPPublicConclusionNotActivated: true,
      publicTheoremEmissionAllowed: false,

      globalFinalDerivationsReady: true,
      globalSemanticNodeDerivationsReady: true,
      publicTheoremEmissionReady: false,
      publicTheoremEmissionRemainsSeparate: true,
      callerReadinessAssertionsForbidden: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

async function deriveComplexityImplication0({
  node,
  dependencyNode,
  binding,
  pack,
  positiveRecord,
  predecessorNF,
  globalBoundsExponent,
}) {
  const nodeValidation = validateComplexityNode0({
    node,
    globalBoundsExponent,
  });
  if (!nodeValidation.ok) return nodeValidation;

  const dependency = validateComplexityDependency0({
    dependencyNode,
    predecessorNF,
  });
  if (!dependency.ok) return dependency;

  const source = validateComplexitySourceRecords0(pack);
  if (!source.ok) return source;

  const expectedBinding = makeComplexityBinding0({
    node,
    dependencyNode,
    PCCPack: pack,
  });
  if (!sameCanonical0(binding, expectedBinding)) {
    return validationReject0(
      ['ComplexitySemanticDerivations', 'complexityBinding'],
      'complexity binding must exactly match the final node, SAT-in-P dependency, final theorem, source implication, and checker contract',
      { expected: expectedBinding, actual: binding },
    );
  }

  const premiseProbe = await runFinalNegativeProbe0({
    finalTheorem: pack.FinalTheorem,
    probeName: 'MissingSATinPPremise',
    mutate: (value) => ({
      ...value,
      AcceptedPackageImpliesPEqualsNP: {
        ...value.AcceptedPackageImpliesPEqualsNP,
        assumptions: value.AcceptedPackageImpliesPEqualsNP.assumptions
          .filter((entry) => entry !== 'SAT in P'),
      },
    }),
  });
  if (!premiseProbe.ok) return premiseProbe;

  const boundaryProbe = await runFinalNegativeProbe0({
    finalTheorem: pack.FinalTheorem,
    probeName: 'UnconditionalClaimBoundary',
    mutate: (value) => ({
      ...value,
      AcceptedPackageImpliesPEqualsNP: {
        ...value.AcceptedPackageImpliesPEqualsNP,
        noUnconditionalClaim: false,
      },
    }),
  });
  if (!boundaryProbe.ok) return boundaryProbe;

  const conclusion = Object.freeze({
    kind: 'GlobalFinalComplexityConclusion0',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    dependency: GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0,
    finalTheoremAccepted: true,
    satInPPremiseChecked: true,
    npCompletenessPremiseChecked: true,
    conditionalClaimBoundaryChecked: true,
    premiseNegativeProbeRejected: true,
    unconditionalClaimNegativeProbeRejected: true,
    boundedExecutableComplexityImplication: true,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    publicPEqualsNPConclusionNotActivated: true,
  });
  const nf = {
    kind: 'GlobalFinalComplexityImplicationDerivation0NF',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    theorem: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    globalNodeDigest: expectedBinding.globalNodeDigest,
    dependencyNodeId: GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0,
    dependencyNodeDigest: expectedBinding.dependencyNodeDigest,
    dependencyRefinementDigest: dependency.nf.dependencyRefinementDigest,
    finalTheoremDigest: expectedBinding.finalTheoremDigest,
    satInPImplicationDigest: expectedBinding.satInPImplicationDigest,
    complexityImplicationDigest: expectedBinding.complexityImplicationDigest,
    finalPublicTheoremDigest: expectedBinding.finalPublicTheoremDigest,
    checkerContractDigest: expectedBinding.checkerContractDigest,
    bindingDigest: expectedBinding.bindingDigest,
    positiveRecordDigest: positiveRecord.Digest ?? positiveRecord.digest,
    premiseNegativeProbeDigest: premiseProbe.nf.recordDigest,
    unconditionalNegativeProbeDigest: boundaryProbe.nf.recordDigest,
    sourceAssumptions: source.nf.assumptions,
    sourceConclusion: source.nf.conclusion,
    conditionalOnPackageAcceptance: true,
    noUnconditionalClaim: true,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    boundedExecutableComplexityImplication: true,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    publicPEqualsNPConclusionNotActivated: true,
    ready: true,
  };
  return validationAccept0({
    ...nf,
    derivationDigest: digestCanonical0(nf),
  });
}

function makeComplexityBinding0({ node, dependencyNode, PCCPack }) {
  const base = Object.freeze({
    kind: 'GlobalFinalComplexitySemanticBinding0',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    globalNodeDigest: digestCanonical0(stripDigestFields0(node)),
    dependencyNodeId: GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0,
    dependencyNodeDigest: digestCanonical0(stripDigestFields0(dependencyNode)),
    finalTheoremDigest: digestCanonical0(PCCPack?.FinalTheorem ?? null),
    satInPImplicationDigest: digestCanonical0(
      PCCPack?.FinalTheorem?.AcceptedPackageImpliesSATinP ?? null,
    ),
    complexityImplicationDigest: digestCanonical0(
      PCCPack?.FinalTheorem?.AcceptedPackageImpliesPEqualsNP ?? null,
    ),
    finalPublicTheoremDigest: digestCanonical0(
      PCCPack?.FinalTheorem?.FinalPublicTheorem ?? null,
    ),
    checkerContractDigest: digestCanonical0(GLOBAL_FINAL_COMPLEXITY_CONTRACT0),
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

function validateComplexityNode0({ node, globalBoundsExponent }) {
  const contract = GLOBAL_FINAL_COMPLEXITY_CONTRACT0;
  if (!isPlainObject0(node)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'complexity final coordinate is missing its global node',
      { nodeId: contract.nodeId },
    );
  }
  if (node.id !== contract.nodeId
      || node.nodeKind !== contract.nodeKind
      || node.label !== contract.label) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'complexity global node identity, kind, or label mismatch',
      { contract, actual: node },
    );
  }
  if (!sameCanonical0(node.premises, contract.premises)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'premises'],
      'complexity global node premise list must exactly match its contract',
      { expected: contract.premises, actual: node.premises },
    );
  }
  if (!sameCanonical0(node.imports, [])
      || String(node.mode ?? 'Full').trim().toLowerCase() !== 'full'
      || !sameCanonical0(node.payload, {})
      || node.route !== null
      || node.rank !== null) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'complexity global node must retain empty imports/payload, Full mode, and null route/rank',
      {
        imports: node.imports,
        mode: node.mode,
        payload: node.payload,
        route: node.route,
        rank: node.rank,
      },
    );
  }
  if (node.conclusion?.tag !== contract.conclusionTag
      || node.conclusion?.theorem !== contract.theorem
      || Object.keys(node.conclusion).length !== 2) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'conclusion'],
      'complexity global node conclusion must exactly match its theorem coordinate',
      { expected: contract.theorem, actual: node.conclusion },
    );
  }
  if (!isPlainObject0(node.bounds)
      || node.bounds.polynomial !== true
      || !Number.isInteger(node.bounds.exponent)
      || node.bounds.exponent <= 0
      || !Number.isInteger(globalBoundsExponent)
      || node.bounds.exponent > globalBoundsExponent) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'bounds'],
      'complexity global node must carry a positive polynomial bound inside the global envelope',
      { globalBoundsExponent, actual: node.bounds },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexityNodeContract0NF',
    nodeId: contract.nodeId,
    exponent: node.bounds.exponent,
  });
}

function validateComplexityDependency0({ dependencyNode, predecessorNF }) {
  if (!isPlainObject0(dependencyNode)
      || dependencyNode.id !== GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0
      || dependencyNode.nodeKind !== 'final') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0],
      'complexity implication requires the exact SAT-in-P final predecessor node',
      { actual: dependencyNode },
    );
  }
  const binding = predecessorNF.semanticOverlay?.semanticFinalSATReductionBinding;
  if (!isPlainObject0(binding)
      || binding.nodeId !== GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0
      || !isDigest0(binding.derivationDigest)) {
    return validationReject0(
      ['FinalSATReductionPredecessor', 'semanticOverlay', 'semanticFinalSATReductionBinding'],
      'complexity implication requires the checked SAT-in-P semantic binding',
      { actual: binding },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexityDependency0NF',
    dependencyNodeId: GLOBAL_FINAL_COMPLEXITY_DEPENDENCY_NODE_ID0,
    dependencyRefinementDigest: binding.derivationDigest,
  });
}

function validateComplexitySourceRecords0(pack) {
  const finalTheorem = pack.FinalTheorem;
  const sat = finalTheorem?.AcceptedPackageImpliesSATinP;
  const complexity = finalTheorem?.AcceptedPackageImpliesPEqualsNP;
  const publicTheorem = finalTheorem?.FinalPublicTheorem;
  if (!isPlainObject0(finalTheorem)
      || !isPlainObject0(sat)
      || !isPlainObject0(complexity)
      || !isPlainObject0(publicTheorem)) {
    return validationReject0(
      ['PCCPack', 'FinalTheorem'],
      'complexity source surfaces must include final theorem, SAT-in-P implication, complexity implication, and public theorem records',
      {
        hasFinalTheorem: isPlainObject0(finalTheorem),
        hasSATinP: isPlainObject0(sat),
        hasComplexity: isPlainObject0(complexity),
        hasPublicTheorem: isPlainObject0(publicTheorem),
      },
    );
  }
  if (sat.conclusion !== 'SAT in P' || sat.polynomial !== true) {
    return validationReject0(
      ['PCCPack', 'FinalTheorem', 'AcceptedPackageImpliesSATinP'],
      'complexity implication requires a polynomial SAT-in-P predecessor source',
      { actual: sat },
    );
  }
  if (complexity.kind !== 'FinalImplication0'
      || complexity.id !== 'PackageAcceptanceImpliesPEqualsNP'
      || complexity.conclusion !== 'P = NP') {
    return validationReject0(
      ['PCCPack', 'FinalTheorem', 'AcceptedPackageImpliesPEqualsNP'],
      'complexity source implication identity or conclusion mismatch',
      { actual: complexity },
    );
  }
  for (const assumption of GLOBAL_FINAL_COMPLEXITY_CONTRACT0.requiredAssumptions) {
    if (!complexity.assumptions?.includes(assumption)) {
      return validationReject0(
        ['PCCPack', 'FinalTheorem', 'AcceptedPackageImpliesPEqualsNP', 'assumptions'],
        'complexity source implication is missing a required assumption',
        { assumption, actual: complexity.assumptions },
      );
    }
  }
  for (const field of GLOBAL_FINAL_COMPLEXITY_CONTRACT0.requiredFields) {
    if (complexity[field] !== true) {
      return validationReject0(
        ['PCCPack', 'FinalTheorem', 'AcceptedPackageImpliesPEqualsNP', field],
        'complexity source implication must retain its conditional public-claim boundary',
        { field, actual: complexity[field] },
      );
    }
  }
  if (publicTheorem.exportedStatement?.consequent !== 'P = NP'
      || publicTheorem.noClaimBeforeAccept !== true
      || publicTheorem.finalVerdict !== 'conditional') {
    return validationReject0(
      ['PCCPack', 'FinalTheorem', 'FinalPublicTheorem'],
      'final public theorem boundary must remain conditional and gated by package acceptance',
      { actual: publicTheorem },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexitySourceRecords0NF',
    assumptions: [...complexity.assumptions],
    conclusion: complexity.conclusion,
    publicTheorem: publicTheorem.theorem,
  });
}

async function runFinalNegativeProbe0({ finalTheorem, probeName, mutate }) {
  const record = await CheckFinal0(mutate(finalTheorem));
  if (record.tag !== 'reject') {
    return validationReject0(
      ['PCCPack', 'FinalTheorem', 'negativeProbe', probeName],
      'complexity negative final-theorem probe must reject',
      { actual: compactRecord0(record) },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexityNegativeProbe0NF',
    probeName,
    coord: record.Coord ?? record.coord,
    path: record.Path ?? record.path,
    recordDigest: record.Digest ?? record.digest,
  });
}

function validatePackAlignment0(input) {
  const pack = input.PCCPack;
  const checks = [
    ['GlobalProofDAG', pack.GlobalProofDAG, input.LegacyGlobalProofDAG],
    ['RowPack', pack.RowPack, input.RowPack],
    ['LocalPackages', pack.LocalPackages, input.LocalPackages],
    ['RowFamG', pack.RowFamG, input.RowFamG],
    ['GPack', pack.GPack, input.RowFamG?.GPack],
    [
      'FinalIntegration.GlobalProofDAG',
      pack.FinalIntegration?.GlobalProofDAG,
      input.LegacyGlobalProofDAG,
    ],
    [
      'FinalIntegration.GPack',
      pack.FinalIntegration?.GPack,
      input.RowFamG?.GPack,
    ],
    [
      'FinalTheorem.FinalIntegration',
      pack.FinalTheorem?.FinalIntegration,
      pack.FinalIntegration,
    ],
    [
      'RowFamFinal.FinalTheorem',
      pack.RowFamFinal?.FinalTheorem,
      pack.FinalTheorem,
    ],
  ];
  for (const [name, actual, expected] of checks) {
    if (!sameCanonical0(actual, expected)) {
      return validationReject0(
        ['PCCPack', ...name.split('.')],
        'complexity PCCPack surface must exactly align with the semantic predecessor inputs',
        {
          surface: name,
          expectedDigest: digestCanonical0(expected ?? null),
          actualDigest: digestCanonical0(actual ?? null),
        },
      );
    }
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexityPackAlignment0NF',
    alignedSurfaces: checks.map(([name]) => name),
  });
}

function validateSemanticSuite0(suite, dag, pack) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['ComplexitySemanticDerivations'],
      'complexity semantic suite must be an object',
      { actual: typeof suite },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'suiteId',
    'complexityBinding',
    'Scope',
    'Policy',
  ]);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['ComplexitySemanticDerivations', unexpected[0]],
      'complexity semantic suite rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (suite.kind !== 'GlobalFinalComplexitySemanticSuite0'
      || suite.version !== CHECKER_VERSION
      || typeof suite.suiteId !== 'string') {
    return validationReject0(
      ['ComplexitySemanticDerivations'],
      'complexity semantic suite shape mismatch',
      { actual: suite },
    );
  }
  if (!sameCanonical0(suite.Scope, GLOBAL_FINAL_COMPLEXITY_SCOPE0)
      || !sameCanonical0(suite.Policy, GLOBAL_FINAL_COMPLEXITY_POLICY0)) {
    return validationReject0(
      ['ComplexitySemanticDerivations'],
      'complexity semantic suite scope or policy mismatch',
      { actualScope: suite.Scope, actualPolicy: suite.Policy },
    );
  }
  const expected = makeGlobalFinalComplexitySemanticSuite0({
    LegacyGlobalProofDAG: dag,
    PCCPack: pack,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['ComplexitySemanticDerivations'],
      'complexity semantic suite must exactly match the computed final-node, SAT-in-P dependency, final-theorem, and checker bindings',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexitySemanticSuite0NF',
    suiteId: suite.suiteId,
    nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    bindingDigest: suite.complexityBinding.bindingDigest,
    scopeDigest: digestCanonical0(suite.Scope),
    policyDigest: digestCanonical0(suite.Policy),
  });
}

function validatePredecessorBoundary0(nf) {
  const expected = {
    status: 'development-only',
    developmentOnly: true,
    finalTheoremReady: false,
    publicTheoremEmissionAllowed: false,
    globalFinalSATReductionSemanticReady: true,
    globalFinalSATReductionDerivationReady: true,
    globalFinalPrefixRefinementsReady: true,
    globalPackageDerivationsReady: true,
    globalRowDerivationsReady: true,
    globalInfrastructureSemanticReady: true,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['FinalSATReductionPredecessor', 'NF', field],
        'final SAT-reduction predecessor boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0
      || !sameCanonical0(nf.quarantinedFinalNodeIds, GLOBAL_DAG_REQUIRED_FINALS0)
      || !nf.semanticOverlay?.blockedFinalNodeIds?.includes(
        GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
      )) {
    return validationReject0(
      ['FinalSATReductionPredecessor', 'NF', 'semanticOverlay'],
      'final SAT-reduction predecessor must keep complexity implication blocked and expose no active final node',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        blockedFinalNodeIds: nf.semanticOverlay?.blockedFinalNodeIds,
        quarantinedFinalNodeIds: nf.quarantinedFinalNodeIds,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexityPredecessorBoundary0NF',
    ...expected,
    activeFinalNodeIds: [],
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'global final-complexity semantic input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalFinalComplexitySemanticInput0') {
    return validationReject0(
      ['kind'],
      'global final-complexity semantic input kind must be GlobalFinalComplexitySemanticInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `global final-complexity semantic input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  for (const field of [
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'RowPack',
    'RowFamG',
    'RowSemanticDerivations',
    'LocalPackages',
    'PackageSemanticDerivations',
    'PCCPack',
    'FinalPrefixSemanticDerivations',
    'SATReductionSemanticDerivations',
    'ComplexitySemanticDerivations',
    'Scope',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'global final-complexity semantic input is missing a required field',
        { field },
      );
    }
  }
  for (const field of [
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'RowPack',
    'RowFamG',
    'RowSemanticDerivations',
    'LocalPackages',
    'PackageSemanticDerivations',
    'PCCPack',
    'FinalPrefixSemanticDerivations',
    'SATReductionSemanticDerivations',
    'ComplexitySemanticDerivations',
  ]) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'global final-complexity semantic dependency surface must be an object',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'global final-complexity semantic input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!Array.isArray(input.LegacyGlobalProofDAG.Nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'global final-complexity semantic input requires a global Nodes array',
    );
  }
  if (!sameCanonical0(input.Scope, GLOBAL_FINAL_COMPLEXITY_SCOPE0)) {
    return validationReject0(
      ['Scope'],
      'global final-complexity semantic scope must match the bounded fail-closed scope',
      { expected: GLOBAL_FINAL_COMPLEXITY_SCOPE0, actual: input.Scope },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_FINAL_COMPLEXITY_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'global final-complexity semantic policy must match the fail-closed policy',
      { expected: GLOBAL_FINAL_COMPLEXITY_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'KBundle',
    'LegacyGlobalProofDAG',
    'InfrastructureSemanticDerivations',
    'RowPack',
    'RowFamG',
    'RowSemanticDerivations',
    'LocalPackages',
    'PackageSemanticDerivations',
    'PCCPack',
    'FinalPrefixSemanticDerivations',
    'SATReductionSemanticDerivations',
    'ComplexitySemanticDerivations',
    'Scope',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'global final-complexity semantic checker rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexitySemanticInputShape0NF',
  });
}

function isFinalTheoremAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && record?.checker === 'CheckFinal0'
    && nf?.kind === 'FinalTheorem0NF';
}

function isDigest0(value) {
  return isPlainObject0(value)
    && value.alg === 'SHA256'
    && typeof value.hex === 'string'
    && /^[0-9a-f]{64}$/u.test(value.hex);
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

function isPlainObject0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

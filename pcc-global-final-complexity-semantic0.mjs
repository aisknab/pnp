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
  GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
  makeGlobalFinalSATReductionSemanticSuite0,
} from './pcc-global-final-sat-reduction-semantic0.mjs';

import {
  CheckFinal0,
} from './pcc-final0.mjs';

import {
  CheckComplexityBridge0,
  COMPLEXITY_BRIDGE_SCOPE0,
  CONDITIONAL_COMPLEXITY_CLAIM0,
  STANDARD_COMPLEXITY_BASIS0,
  makeComplexityBridgeInput0,
} from './pcc-complexity-bridge0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_FINAL_COMPLEXITY_NODE_ID0 =
  'Final.AcceptedPackageImpliesPEqualsNP';

export const GLOBAL_FINAL_COMPLEXITY_SCOPE0 = Object.freeze({
  kind: 'GlobalFinalComplexitySemanticScope0',
  version: CHECKER_VERSION,
  scope: 'guarded-final-complexity-refinement',
  finalSATReductionPredecessorChecked: true,
  finalTheoremRecordReplayed: true,
  satInPDependencyDigestBound: true,
  satNPCompletenessDependencyExplicit: true,
  pSubsetNPDependencyExplicit: true,
  polynomialReductionClosureExplicit: true,
  conditionalPublicBoundaryChecked: true,
  premiseRemovalNegativeProbeChecked: true,
  unconditionalClaimNegativeProbeChecked: true,
  guardedComplexityRefinementOnly: true,
  cookLevinFormalizationIncluded: false,
  unrestrictedComplexityImplicationSoundnessNotClaimed: true,
  unrestrictedSATReductionSoundnessNotClaimed: true,
  publicTheoremEmissionNotAllowed: true,
});

export const GLOBAL_FINAL_COMPLEXITY_POLICY0 = Object.freeze({
  kind: 'GlobalFinalComplexitySemanticPolicy0',
  version: CHECKER_VERSION,
  requiresFinalSATReductionSuccessorAcceptance: true,
  requiresExactPCCPackSurfaceAlignment: true,
  requiresFinalTheoremCheckerAcceptance: true,
  requiresExactFinalComplexityNodeContract: true,
  requiresSATReductionSemanticDependency: true,
  requiresExactStandardComplexityBasis: true,
  requiresExactConditionalSourceImplication: true,
  requiresExactConditionalPublicBoundary: true,
  requiresPremiseRemovalNegativeProbe: true,
  requiresUnconditionalClaimNegativeProbe: true,
  bindsGlobalNodeDigest: true,
  bindsSATReductionNodeAndDerivationDigests: true,
  bindsStandardBasisAndSourceDigests: true,
  bindsPositiveAndNegativeRecordDigests: true,
  callerReadinessAssertionsForbidden: true,
  guardedComplexityRefinementOnly: true,
  unrestrictedComplexityImplicationSoundnessNotClaimed: true,
  publicTheoremEmissionNotAllowed: true,
});

export const GLOBAL_FINAL_COMPLEXITY_CONTRACT0 = Object.freeze({
  kind: 'GlobalFinalComplexityCheckerContract0',
  version: CHECKER_VERSION,
  nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  nodeKind: 'final',
  label: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  premises: Object.freeze([GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0]),
  conclusionTag: 'FinalTheoremAccepted0',
  theorem: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
  sourceImplicationId: 'PackageAcceptanceImpliesPEqualsNP',
  sourceAssumptions: Object.freeze(['SAT in P', 'SAT is NP-complete']),
  sourceConclusion: 'P = NP',
  complexityBridgeChecker: 'CheckComplexityBridge0',
  finalTheoremChecker: 'CheckFinal0',
  guardedComplexityRefinementOnly: true,
  cookLevinFormalizationIncluded: false,
  unrestrictedComplexityImplicationSoundnessNotClaimed: true,
});

export function makeGlobalFinalComplexitySemanticSuite0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  PCCPack = makeGlobalFinalPrefixPCCPack0({ LegacyGlobalProofDAG }),
  SATReductionSemanticDerivations = makeGlobalFinalSATReductionSemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
  }),
  ComplexityBasis = STANDARD_COMPLEXITY_BASIS0,
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
        nodeById.get(GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0) ?? null,
      PCCPack,
      SATReductionSemanticDerivations,
      ComplexityBasis,
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
  ComplexityBasis = STANDARD_COMPLEXITY_BASIS0,
  ComplexitySemanticDerivations = makeGlobalFinalComplexitySemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
    SATReductionSemanticDerivations,
    ComplexityBasis,
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
    ComplexityBasis,
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
        reason: 'complexity refinement requires an accepted final SAT-reduction predecessor',
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
    finalCall.ok && isFinalAccept0(finalCall.record),
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
  if (!isFinalAccept0(finalCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalTheorem`,
      path: ['PCCPack', 'FinalTheorem'],
      witness: {
        reason: 'complexity refinement requires an accepted version-zero final theorem record',
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

  const suite = validateSemanticSuite0(input);
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

  const source = validateSourceRecords0(input.PCCPack.FinalTheorem);
  ledger.push(makeLedgerEntry0(
    'complexitySourceRecords',
    source.ok,
    source.nf ?? source.witness,
  ));
  if (!source.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.sourceRecords`,
      source,
      ledger,
    );
  }

  const nodeById = new Map(
    input.LegacyGlobalProofDAG.Nodes.map((node) => [node.id, node]),
  );
  const node = nodeById.get(GLOBAL_FINAL_COMPLEXITY_NODE_ID0);
  const dependencyNode = nodeById.get(GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0);
  const nodeValidation = validateComplexityNode0({
    node,
    globalBoundsExponent: input.LegacyGlobalProofDAG.BoundsLedger?.exponent,
  });
  ledger.push(makeLedgerEntry0(
    'finalComplexityNode',
    nodeValidation.ok,
    nodeValidation.nf ?? nodeValidation.witness,
  ));
  if (!nodeValidation.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.finalComplexity.${GLOBAL_FINAL_COMPLEXITY_NODE_ID0}`,
      nodeValidation,
      ledger,
    );
  }

  const dependency = validateSATReductionDependency0({
    dependencyNode,
    predecessorNF,
  });
  ledger.push(makeLedgerEntry0(
    'satReductionDependency',
    dependency.ok,
    dependency.nf ?? dependency.witness,
  ));
  if (!dependency.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.satReductionDependency`,
      dependency,
      ledger,
    );
  }

  const bridgeInput = makeComplexityBridgeInput0({
    sourceDerivationDigest: dependency.nf.sourceDerivationDigest,
    Basis: input.ComplexityBasis,
    Claim: CONDITIONAL_COMPLEXITY_CLAIM0,
  });
  const bridgeCall = await callChecker0(
    'CheckComplexityBridge0',
    () => CheckComplexityBridge0(bridgeInput),
  );
  ledger.push(makeLedgerEntry0(
    'CheckComplexityBridge0',
    bridgeCall.ok && bridgeCall.record.tag === 'accept',
    bridgeCall.ok ? bridgeCall.record : bridgeCall.witness,
  ));
  if (!bridgeCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.complexityBridge.exception`,
      path: ['ComplexityBasis'],
      witness: bridgeCall.witness,
      ledger,
    });
  }
  if (bridgeCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.complexityBridge`,
      path: ['ComplexityBasis'],
      witness: {
        reason: 'guarded standard complexity bridge rejected',
        inner: compactRecord0(bridgeCall.record),
      },
      ledger,
    });
  }

  const negativeProbes = await runComplexityNegativeProbes0({
    sourceDerivationDigest: dependency.nf.sourceDerivationDigest,
    Basis: input.ComplexityBasis,
  });
  ledger.push(makeLedgerEntry0(
    'complexityNegativeProbes',
    negativeProbes.ok,
    negativeProbes.nf ?? negativeProbes.witness,
  ));
  if (!negativeProbes.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.negativeProbes`,
      negativeProbes,
      ledger,
    );
  }

  const expectedBinding = makeComplexityBinding0({
    node,
    dependencyNode,
    PCCPack: input.PCCPack,
    SATReductionSemanticDerivations:
      input.SATReductionSemanticDerivations,
    ComplexityBasis: input.ComplexityBasis,
  });
  if (!sameCanonical0(
    input.ComplexitySemanticDerivations.complexityBinding,
    expectedBinding,
  )) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.complexityBinding`,
      path: ['ComplexitySemanticDerivations', 'complexityBinding'],
      witness: {
        reason: 'complexity binding must exactly match the final node, SAT-reduction dependency, standard basis, source implication, and conditional public boundary',
        expected: expectedBinding,
        actual: input.ComplexitySemanticDerivations.complexityBinding,
      },
      ledger,
    });
  }

  const bridgeNF = bridgeCall.record.NF ?? bridgeCall.record.nf ?? {};
  const conclusion = Object.freeze({
    kind: 'GlobalFinalComplexityRefinementConclusion0',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    predecessorNodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    satInPDependencyBound: true,
    satNPCompletenessDependencyChecked: true,
    npSubsetPDerived: true,
    pSubsetNPDerived: true,
    conditionalPEqualsNPDerived: true,
    noUnconditionalClaim: true,
    guardedComplexityRefinement: true,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    publicConclusionNotActivated: true,
  });
  const derivationBase = {
    kind: 'GlobalFinalComplexityDerivation0NF',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    theorem: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    globalNodeDigest: expectedBinding.globalNodeDigest,
    dependencyNodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    dependencyNodeDigest: expectedBinding.dependencyNodeDigest,
    dependencyDerivationDigest: dependency.nf.sourceDerivationDigest,
    satReductionBindingDigest: expectedBinding.satReductionBindingDigest,
    complexityBasisDigest: expectedBinding.complexityBasisDigest,
    sourceImplicationDigest: expectedBinding.sourceImplicationDigest,
    finalPublicTheoremDigest: expectedBinding.finalPublicTheoremDigest,
    checkerContractDigest: expectedBinding.checkerContractDigest,
    bindingDigest: expectedBinding.bindingDigest,
    finalTheoremRecordDigest: finalCall.record.Digest ?? finalCall.record.digest,
    complexityBridgeRecordDigest:
      bridgeCall.record.Digest ?? bridgeCall.record.digest,
    complexityBridgeDerivationDigest: bridgeNF.derivationDigest,
    premiseRemovalNegativeProbeDigest:
      negativeProbes.nf.premiseRemovalRecordDigest,
    unconditionalClaimNegativeProbeDigest:
      negativeProbes.nf.unconditionalClaimRecordDigest,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    guardedComplexityRefinement: true,
    cookLevinFormalizationIncluded: false,
    standardTheoremDependencyTrustRequired: true,
    unrestrictedComplexityImplicationSoundnessNotClaimed: true,
    publicConclusionNotActivated: true,
    ready: true,
  };
  const derivation = Object.freeze({
    ...derivationBase,
    derivationDigest: digestCanonical0(derivationBase),
  });

  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalFinalComplexitySemantic0NF',
      checker,
      version: CHECKER_VERSION,
      globalFinalComplexitySemanticReady: true,
      globalFinalComplexityImplicationRefinementReady: true,
      globalFinalComplexityImplicationReady: true,
      allGlobalFinalCoordinatesBoundedRefined: true,

      finalSATReductionPredecessorAccepted: true,
      finalSATReductionPredecessorChecker: predecessorCall.record.checker,
      finalSATReductionPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      globalFinalSATReductionDerivationReady: true,
      globalFinalPrefixRefinementsReady: true,
      globalPackageDerivationsReady: true,
      globalRowDerivationsReady: true,
      globalInfrastructureSemanticReady: true,
      semanticKBundleFinalReady:
        predecessorNF.semanticKBundleFinalReady === true,

      finalTheoremRecordAccepted: true,
      finalTheoremChecker: finalCall.record.checker,
      finalTheoremRecordDigest: finalCall.record.Digest ?? finalCall.record.digest,
      complexityBridgeAccepted: true,
      complexityBridgeChecker: bridgeCall.record.checker,
      complexityBridgeDigest: bridgeCall.record.Digest ?? bridgeCall.record.digest,
      complexityBasisDigest: digestCanonical0(input.ComplexityBasis),

      globalFinalComplexityNodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
      globalFinalSATReductionNodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
      complexityDerivation: derivation,
      complexityDerivationDigest: derivation.derivationDigest,
      complexityBindingDigest: expectedBinding.bindingDigest,

      Scope: { ...GLOBAL_FINAL_COMPLEXITY_SCOPE0 },
      scopeDigest: digestCanonical0(input.Scope),
      guardedComplexityRefinementOnly: true,
      cookLevinFormalizationIncluded: false,
      standardTheoremDependencyTrustRequired: true,
      unrestrictedComplexityImplicationSoundnessNotClaimed: true,
      unrestrictedSATReductionSoundnessNotClaimed: true,
      conditionalPublicBoundaryChecked: true,
      publicConclusionNotActivated: true,
      publicTheoremEmissionAllowed: false,

      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      unrestrictedFinalSoundnessReady: false,
      finalPublicationReadinessRequiresUnrestrictedSoundness: true,
      callerReadinessAssertionsForbidden: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

function makeComplexityBinding0({
  node,
  dependencyNode,
  PCCPack,
  SATReductionSemanticDerivations,
  ComplexityBasis,
}) {
  const base = Object.freeze({
    kind: 'GlobalFinalComplexitySemanticBinding0',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    globalNodeDigest: digestCanonical0(stripDigestFields0(node)),
    dependencyNodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    dependencyNodeDigest:
      digestCanonical0(stripDigestFields0(dependencyNode)),
    satReductionBindingDigest:
      SATReductionSemanticDerivations?.reductionBinding?.bindingDigest ?? null,
    complexityBasisDigest: digestCanonical0(ComplexityBasis ?? null),
    sourceImplicationDigest: digestCanonical0(
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

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'global final complexity semantic input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalFinalComplexitySemanticInput0') {
    return validationReject0(
      ['kind'],
      'global final complexity semantic input kind must be GlobalFinalComplexitySemanticInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `global final complexity semantic input version must be ${CHECKER_VERSION}`,
      { actual: input.version },
    );
  }
  const objectFields = [
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
    'ComplexityBasis',
    'ComplexitySemanticDerivations',
    'Scope',
    'Policy',
  ];
  for (const field of objectFields) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'global final complexity semantic input is missing a required field',
        { field },
      );
    }
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'global final complexity semantic dependency surface must be an object',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'global final complexity semantic input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!Array.isArray(input.LegacyGlobalProofDAG.Nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'global final complexity semantic input requires a global Nodes array',
    );
  }
  if (!sameCanonical0(input.Scope, GLOBAL_FINAL_COMPLEXITY_SCOPE0)) {
    return validationReject0(
      ['Scope'],
      'global final complexity semantic scope must match the guarded fail-closed scope',
      { expected: GLOBAL_FINAL_COMPLEXITY_SCOPE0, actual: input.Scope },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_FINAL_COMPLEXITY_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'global final complexity semantic policy must match the guarded fail-closed policy',
      { expected: GLOBAL_FINAL_COMPLEXITY_POLICY0, actual: input.Policy },
    );
  }
  const allowed = new Set(['kind', 'version', ...objectFields]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'global final complexity semantic checker rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexitySemanticInputShape0NF',
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
      || !sameCanonical0(
        nf.semanticOverlay?.blockedFinalNodeIds,
        [GLOBAL_FINAL_COMPLEXITY_NODE_ID0],
      )) {
    return validationReject0(
      ['FinalSATReductionPredecessor', 'NF', 'semanticOverlay'],
      'final SAT-reduction predecessor must keep exactly the complexity node blocked and expose no active final node',
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

function validateSemanticSuite0(input) {
  const suite = input.ComplexitySemanticDerivations;
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
      || typeof suite.suiteId !== 'string'
      || suite.suiteId.length === 0) {
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
    LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
    PCCPack: input.PCCPack,
    SATReductionSemanticDerivations:
      input.SATReductionSemanticDerivations,
    ComplexityBasis: input.ComplexityBasis,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['ComplexitySemanticDerivations'],
      'complexity semantic suite must exactly match the computed final-node, SAT-reduction, standard-basis, and conditional-boundary bindings',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexitySemanticSuite0NF',
    suiteId: suite.suiteId,
    nodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    bindingDigest: suite.complexityBinding.bindingDigest,
  });
}

function validateComplexityNode0({ node, globalBoundsExponent }) {
  const contract = GLOBAL_FINAL_COMPLEXITY_CONTRACT0;
  if (!isPlainObject0(node)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'final complexity coordinate is missing its global node',
      { nodeId: contract.nodeId },
    );
  }
  if (node.id !== contract.nodeId
      || node.nodeKind !== contract.nodeKind
      || node.label !== contract.label) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'final complexity global node identity, kind, or label mismatch',
      { contract, actual: node },
    );
  }
  if (!sameCanonical0(node.premises, contract.premises)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'premises'],
      'final complexity global node premise list must exactly match its SAT-reduction predecessor',
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
      'final complexity global node must retain empty imports/payload, Full mode, and null route/rank',
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
      'final complexity global node conclusion must exactly match its theorem coordinate',
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
      'final complexity global node must carry a positive polynomial bound inside the global envelope',
      { globalBoundsExponent, actual: node.bounds },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexityNodeContract0NF',
    nodeId: contract.nodeId,
    exponent: node.bounds.exponent,
  });
}

function validateSATReductionDependency0({ dependencyNode, predecessorNF }) {
  if (!isPlainObject0(dependencyNode)
      || dependencyNode.id !== GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0
      || dependencyNode.nodeKind !== 'final') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0],
      'final complexity refinement requires the exact SAT-reduction final predecessor node',
      { actual: dependencyNode },
    );
  }
  const binding = predecessorNF.semanticOverlay
    ?.semanticFinalSATReductionBinding;
  const derivation = predecessorNF.satReductionDerivation;
  if (!isPlainObject0(binding)
      || binding.nodeId !== GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0
      || !isDigest0(binding.derivationDigest)
      || !isPlainObject0(derivation)
      || derivation.ready !== true
      || !isDigest0(derivation.derivationDigest)) {
    return validationReject0(
      ['FinalSATReductionPredecessor', 'semanticOverlay', GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0],
      'final complexity refinement requires the accepted SAT-reduction semantic binding and derivation',
      { binding, derivation },
    );
  }
  if (!sameCanonical0(binding.derivationDigest, derivation.derivationDigest)) {
    return validationReject0(
      ['FinalSATReductionPredecessor', 'semanticOverlay', 'semanticFinalSATReductionBinding', 'derivationDigest'],
      'SAT-reduction semantic binding and derivation digest mismatch',
      {
        bindingDigest: binding.derivationDigest,
        derivationDigest: derivation.derivationDigest,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexitySATReductionDependency0NF',
    nodeId: GLOBAL_FINAL_SAT_REDUCTION_NODE_ID0,
    sourceDerivationDigest: derivation.derivationDigest,
    semanticBindingDigest: digestCanonical0(binding),
  });
}

function validateSourceRecords0(finalTheorem) {
  const implication = finalTheorem?.AcceptedPackageImpliesPEqualsNP;
  const publicTheorem = finalTheorem?.FinalPublicTheorem;
  if (!isPlainObject0(implication) || !isPlainObject0(publicTheorem)) {
    return validationReject0(
      ['PCCPack', 'FinalTheorem'],
      'complexity source records must include the final implication and conditional public theorem',
      {
        hasImplication: isPlainObject0(implication),
        hasPublicTheorem: isPlainObject0(publicTheorem),
      },
    );
  }
  const expectedImplication = {
    kind: 'FinalImplication0',
    id: 'PackageAcceptanceImpliesPEqualsNP',
    assumptions: ['SAT in P', 'SAT is NP-complete'],
    conclusion: 'P = NP',
    public: true,
    conditionalOnPackageAcceptance: true,
    usesSATinP: true,
    noUnconditionalClaim: true,
  };
  if (!sameCanonical0(implication, expectedImplication)) {
    return validationReject0(
      ['PCCPack', 'FinalTheorem', 'AcceptedPackageImpliesPEqualsNP'],
      'complexity source implication must exactly preserve both assumptions and the conditional claim boundary',
      { expected: expectedImplication, actual: implication },
    );
  }
  const expectedPublic = {
    kind: 'FinalPublicTheorem0',
    id: 'GeneratedPackageAcceptanceImpliesPEqualsNP',
    theorem: 'CheckPCCPackexp(GeneratePCCPack())=accept implies P = NP',
    publicConclusion: true,
    noClaimBeforeAccept: true,
    finalVerdict: 'conditional',
    exportedStatement: {
      antecedent: 'CheckPCCPackexp(GeneratePCCPack())=accept',
      consequent: 'P = NP',
    },
  };
  if (!sameCanonical0(publicTheorem, expectedPublic)) {
    return validationReject0(
      ['PCCPack', 'FinalTheorem', 'FinalPublicTheorem'],
      'final public theorem record must exactly retain the package-acceptance antecedent and no-claim-before-accept boundary',
      { expected: expectedPublic, actual: publicTheorem },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexitySourceRecords0NF',
    assumptions: [...expectedImplication.assumptions],
    conclusion: expectedImplication.conclusion,
    publicAntecedent: expectedPublic.exportedStatement.antecedent,
    noUnconditionalClaim: true,
  });
}

async function runComplexityNegativeProbes0({ sourceDerivationDigest, Basis }) {
  const base = makeComplexityBridgeInput0({
    sourceDerivationDigest,
    Basis,
    Claim: CONDITIONAL_COMPLEXITY_CLAIM0,
  });
  const premiseRemoval = await CheckComplexityBridge0({
    ...base,
    Claim: {
      ...base.Claim,
      assumptions: ['SAT is NP-complete'],
    },
  });
  if (premiseRemoval.tag !== 'reject'
      || premiseRemoval.checker !== 'CheckComplexityBridge0'
      || premiseRemoval.Coord !== 'CheckComplexityBridge0.Claim'
      || !sameCanonical0(premiseRemoval.Path, ['Claim', 'assumptions'])) {
    return validationReject0(
      ['ComplexityBasis', 'negativeProbe', 'premiseRemoval'],
      'complexity premise-removal probe must reject at the exact claim-assumption coordinate',
      { actual: compactRecord0(premiseRemoval) },
    );
  }
  const unconditional = await CheckComplexityBridge0({
    ...base,
    Claim: {
      ...base.Claim,
      noUnconditionalClaim: false,
    },
  });
  if (unconditional.tag !== 'reject'
      || unconditional.checker !== 'CheckComplexityBridge0'
      || unconditional.Coord !== 'CheckComplexityBridge0.Claim') {
    return validationReject0(
      ['ComplexityBasis', 'negativeProbe', 'unconditionalClaim'],
      'complexity unconditional-claim probe must reject at the guarded claim coordinate',
      { actual: compactRecord0(unconditional) },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalComplexityNegativeProbes0NF',
    premiseRemovalRecordDigest:
      premiseRemoval.Digest ?? premiseRemoval.digest,
    unconditionalClaimRecordDigest:
      unconditional.Digest ?? unconditional.digest,
  });
}

function isFinalAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && record?.checker === 'CheckFinal0'
    && nf?.kind === 'Final0NF';
}

function stripDigestFields0(value) {
  if (!isPlainObject0(value)) return value;
  const out = {};
  for (const key of Object.keys(value).sort()) {
    if (key !== 'Digest' && key !== 'digest') out[key] = value[key];
  }
  return out;
}

function isDigest0(value) {
  return isPlainObject0(value)
    && value.alg === 'SHA256'
    && typeof value.hex === 'string'
    && /^[0-9a-f]{64}$/u.test(value.hex);
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

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
  GLOBAL_FINAL_PREFIX_NODE_IDS0,
  makeGlobalFinalPrefixPCCPack0,
  makeGlobalFinalPrefixSemanticSuite0,
} from './pcc-global-final-prefix-contract0.mjs';

import {
  CheckFinalFrameworkMatch0,
  CheckFinalIntegration0,
  CheckSATBounds0,
  CheckSATDecision0,
} from './pcc-final-framework0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_FINAL_SAT_NODE_ID0 = 'Final.AcceptedPackageImpliesSATinP';
export const GLOBAL_FINAL_COMPLEXITY_NODE_ID0 = 'Final.AcceptedPackageImpliesPEqualsNP';

export const GLOBAL_FINAL_SAT_SEMANTIC_SCOPE0 = Object.freeze({
  kind: 'GlobalFinalSATSemanticScope0',
  version: CHECKER_VERSION,
  scope: 'bounded-executable-accepted-package-to-sat-in-p-refinement',
  finalPrefixPredecessorChecked: true,
  finalIntegrationCheckerReplayed: true,
  frameworkMatchCheckerReplayed: true,
  satDecisionCheckerReplayed: true,
  satBoundsCheckerReplayed: true,
  exactMinimumComparatorChecked: true,
  lockedNANDThresholdDependencyChecked: true,
  zeroSlackOracleDependencyChecked: true,
  generatedPackageDependencyChecked: true,
  positiveAndNegativeDecisionProbesChecked: true,
  boundedExecutableSATReductionRefinementOnly: true,
  unrestrictedSATReductionSoundnessNotClaimed: true,
  complexityClassImplicationNotClaimed: true,
  publicTheoremEmissionNotAllowed: true,
});

export const GLOBAL_FINAL_SAT_SEMANTIC_POLICY0 = Object.freeze({
  kind: 'GlobalFinalSATSemanticPolicy0',
  version: CHECKER_VERSION,
  requiresFinalPrefixPredecessorAcceptance: true,
  requiresFinalIntegrationAcceptance: true,
  requiresExactPackSurfaceAlignment: true,
  requiresExactFinalNodeContract: true,
  requiresExactFrameworkMatch: true,
  requiresExactSATDecisionRecord: true,
  requiresExactSATBoundsRecord: true,
  requiresDecisionNegativeProbe: true,
  requiresBoundsNegativeProbe: true,
  bindsGlobalNodeDigest: true,
  bindsDependencyNodeDigests: true,
  bindsIntegrationChildDigests: true,
  bindsPositiveAndNegativeRecordDigests: true,
  callerReadinessAssertionsForbidden: true,
  boundedExecutableSATReductionRefinementOnly: true,
  unrestrictedSATReductionSoundnessNotClaimed: true,
  complexityImplicationRemainsSeparate: true,
});

export const GLOBAL_FINAL_SAT_CONTRACT0 = Object.freeze({
  kind: 'GlobalFinalSATCheckerContract0',
  version: CHECKER_VERSION,
  nodeId: GLOBAL_FINAL_SAT_NODE_ID0,
  nodeKind: 'final',
  label: GLOBAL_FINAL_SAT_NODE_ID0,
  premises: Object.freeze([
    'Package.G.LockedNANDThreshold',
    'Package.O.ZeroSlackOracle',
    'Final.GeneratedPackageSufficiency',
  ]),
  conclusionTag: 'FinalTheoremAccepted0',
  theorem: GLOBAL_FINAL_SAT_NODE_ID0,
  positiveIntegrationChecker: 'CheckFinalIntegration0',
  positiveFrameworkChecker: 'CheckFinalFrameworkMatch0',
  positiveDecisionChecker: 'CheckSATDecision0',
  positiveBoundsChecker: 'CheckSATBounds0',
  decisionNegativeMutation: Object.freeze({
    path: Object.freeze(['SATDecision', 'DecisionRule', 'usesExactMinimum']),
    value: false,
  }),
  boundsNegativeMutation: Object.freeze({
    path: Object.freeze(['SATBounds', 'Bounds', 'polynomial']),
    value: false,
  }),
  comparator: 'minSize>baseline',
  residualSlackBound: 4,
  finalSATExponent: 42,
  boundedExecutableSATReductionRefinementOnly: true,
  unrestrictedSATReductionSoundnessNotClaimed: true,
});

export function makeGlobalFinalSATSemanticSuite0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  PCCPack = makeGlobalFinalPrefixPCCPack0({ LegacyGlobalProofDAG }),
} = {}) {
  const nodeById = new Map(
    (LegacyGlobalProofDAG?.Nodes ?? []).map((node) => [node?.id, node]),
  );
  return Object.freeze({
    kind: 'GlobalFinalSATSemanticSuite0',
    version: CHECKER_VERSION,
    suiteId: 'GlobalDAG.final-sat.semantic.phase38',
    refinement: makeFinalSATBinding0({
      node: nodeById.get(GLOBAL_FINAL_SAT_NODE_ID0) ?? null,
      dependencyNodes: GLOBAL_FINAL_SAT_CONTRACT0.premises.map(
        (id) => nodeById.get(id) ?? null,
      ),
      PCCPack,
    }),
    Scope: { ...GLOBAL_FINAL_SAT_SEMANTIC_SCOPE0 },
    Policy: { ...GLOBAL_FINAL_SAT_SEMANTIC_POLICY0 },
  });
}

export function makeGlobalFinalSATSemanticInput0({
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
  SemanticFinalSAT = makeGlobalFinalSATSemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
  }),
} = {}) {
  return Object.freeze({
    kind: 'GlobalFinalSATSemanticInput0',
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
    SemanticFinalSAT,
    Scope: { ...GLOBAL_FINAL_SAT_SEMANTIC_SCOPE0 },
    Policy: { ...GLOBAL_FINAL_SAT_SEMANTIC_POLICY0 },
  });
}

export async function CheckGlobalFinalSATSemantic0(input) {
  const checker = 'CheckGlobalFinalSATSemantic0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);

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
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalPrefixPredecessor.exception`,
      path: ['FinalPrefixSemanticDerivations'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalPrefixPredecessor`,
      path: ['FinalPrefixSemanticDerivations'],
      witness: {
        reason: 'final SAT refinement requires an accepted final-prefix predecessor',
        inner: compactRecord0(predecessorCall.record),
      },
      ledger,
    });
  }
  const predecessorNF = predecessorCall.record.NF ?? predecessorCall.record.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'finalPrefixPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.finalPrefixPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const integration = input.PCCPack.FinalIntegration;
  const integrationCall = await callChecker0(
    'CheckFinalIntegration0',
    () => CheckFinalIntegration0(integration),
  );
  ledger.push(makeLedgerEntry0(
    'CheckFinalIntegration0',
    integrationCall.ok && integrationCall.record.tag === 'accept',
    integrationCall.ok ? integrationCall.record : integrationCall.witness,
  ));
  if (!integrationCall.ok || integrationCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.finalIntegration`,
      path: ['PCCPack', 'FinalIntegration'],
      witness: {
        reason: 'final SAT refinement requires accepted final integration',
        inner: integrationCall.ok ? compactRecord0(integrationCall.record) : integrationCall.witness,
      },
      ledger,
    });
  }

  const frameworkCall = await callChecker0(
    'CheckFinalFrameworkMatch0',
    () => CheckFinalFrameworkMatch0(integration.FinalMatch),
  );
  const decisionCall = await callChecker0(
    'CheckSATDecision0',
    () => CheckSATDecision0(integration.SATDecision),
  );
  const boundsCall = await callChecker0(
    'CheckSATBounds0',
    () => CheckSATBounds0(integration.SATBounds),
  );
  for (const [name, call] of [
    ['CheckFinalFrameworkMatch0', frameworkCall],
    ['CheckSATDecision0', decisionCall],
    ['CheckSATBounds0', boundsCall],
  ]) {
    ledger.push(makeLedgerEntry0(
      name,
      call.ok && call.record.tag === 'accept',
      call.ok ? call.record : call.witness,
    ));
    if (!call.ok || call.record.tag !== 'accept') {
      return makeRejectRecord0({
        checker,
        coord: `${checker}.${name}`,
        path: ['PCCPack', 'FinalIntegration'],
        witness: {
          reason: 'final SAT child checker rejected during semantic refinement',
          child: name,
          inner: call.ok ? compactRecord0(call.record) : call.witness,
        },
        ledger,
      });
    }
  }

  const alignment = validatePackAlignment0(input);
  ledger.push(makeLedgerEntry0('packAlignment', alignment.ok, alignment.nf ?? alignment.witness));
  if (!alignment.ok) {
    return makeRejectFromValidation0(checker, `${checker}.packAlignment`, alignment, ledger);
  }

  const suite = validateSemanticSuite0(
    input.SemanticFinalSAT,
    input.LegacyGlobalProofDAG,
    input.PCCPack,
  );
  ledger.push(makeLedgerEntry0('semanticFinalSATSuite', suite.ok, suite.nf ?? suite.witness));
  if (!suite.ok) {
    return makeRejectFromValidation0(checker, `${checker}.semanticFinalSATSuite`, suite, ledger);
  }

  const nodeById = new Map(input.LegacyGlobalProofDAG.Nodes.map((node) => [node.id, node]));
  const node = nodeById.get(GLOBAL_FINAL_SAT_NODE_ID0);
  const nodeResult = validateFinalSATNode0({
    node,
    nodeById,
    predecessorNF,
    globalBoundsExponent: input.LegacyGlobalProofDAG.BoundsLedger?.exponent,
  });
  ledger.push(makeLedgerEntry0('finalSATNodeContract', nodeResult.ok, nodeResult.nf ?? nodeResult.witness));
  if (!nodeResult.ok) {
    return makeRejectFromValidation0(checker, `${checker}.finalSATNode`, nodeResult, ledger);
  }

  const source = validateDecisionAndBoundsSurface0(integration);
  ledger.push(makeLedgerEntry0('decisionAndBoundsSurface', source.ok, source.nf ?? source.witness));
  if (!source.ok) {
    return makeRejectFromValidation0(checker, `${checker}.decisionAndBoundsSurface`, source, ledger);
  }

  const decisionNegative = await runDecisionNegativeProbe0(integration.SATDecision);
  ledger.push(makeLedgerEntry0('negativeDecisionProbe', decisionNegative.ok, decisionNegative.nf ?? decisionNegative.witness));
  if (!decisionNegative.ok) {
    return makeRejectFromValidation0(checker, `${checker}.negativeDecisionProbe`, decisionNegative, ledger);
  }

  const boundsNegative = await runBoundsNegativeProbe0(integration.SATBounds);
  ledger.push(makeLedgerEntry0('negativeBoundsProbe', boundsNegative.ok, boundsNegative.nf ?? boundsNegative.witness));
  if (!boundsNegative.ok) {
    return makeRejectFromValidation0(checker, `${checker}.negativeBoundsProbe`, boundsNegative, ledger);
  }

  const binding = input.SemanticFinalSAT.refinement;
  const conclusion = Object.freeze({
    kind: 'GlobalFinalSATRefinementConclusion0',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_SAT_NODE_ID0,
    generatedPackageDependency: 'Final.GeneratedPackageSufficiency',
    lockedNANDThresholdDependency: 'Package.G.LockedNANDThreshold',
    zeroSlackOracleDependency: 'Package.O.ZeroSlackOracle',
    finalIntegrationAccepted: true,
    exactSATDecisionComparatorChecked: true,
    polynomialSATBoundsChecked: true,
    negativeDecisionProbeRejected: true,
    negativeBoundsProbeRejected: true,
    boundedExecutableSATReductionRefinement: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
  });
  const nf = {
    kind: 'GlobalFinalSATSemantic0NF',
    checker,
    version: CHECKER_VERSION,
    globalFinalSATSemanticReady: true,
    globalFinalSATReductionDerivationReady: true,
    globalAcceptedPackageImpliesSATinPRefinementReady: true,

    finalPrefixPredecessorAccepted: true,
    finalPrefixPredecessorChecker: predecessorCall.record.checker,
    finalPrefixPredecessorDigest:
      predecessorCall.record.Digest ?? predecessorCall.record.digest,
    globalFinalPrefixRefinementsReady:
      predecessorNF.globalFinalPrefixRefinementsReady === true,
    globalPackageDerivationsReady: predecessorNF.globalPackageDerivationsReady === true,
    semanticKBundleFinalReady: predecessorNF.semanticKBundleFinalReady === true,

    finalIntegrationAccepted: true,
    finalIntegrationChecker: integrationCall.record.checker,
    finalIntegrationDigest: integrationCall.record.Digest ?? integrationCall.record.digest,
    finalFrameworkDigest: frameworkCall.record.Digest ?? frameworkCall.record.digest,
    satDecisionDigest: decisionCall.record.Digest ?? decisionCall.record.digest,
    satBoundsDigest: boundsCall.record.Digest ?? boundsCall.record.digest,

    finalSATNodeId: GLOBAL_FINAL_SAT_NODE_ID0,
    remainingFinalComplexityNodeId: GLOBAL_FINAL_COMPLEXITY_NODE_ID0,
    globalNodeDigest: binding.globalNodeDigest,
    dependencyNodeDigests: binding.dependencyNodeDigests,
    finalIntegrationRecordDigest: binding.finalIntegrationRecordDigest,
    finalFrameworkRecordDigest: binding.finalFrameworkRecordDigest,
    satDecisionRecordDigest: binding.satDecisionRecordDigest,
    satBoundsRecordDigest: binding.satBoundsRecordDigest,
    checkerContractDigest: binding.checkerContractDigest,
    bindingDigest: binding.bindingDigest,
    positiveIntegrationRecordDigest: integrationCall.record.Digest ?? integrationCall.record.digest,
    positiveDecisionRecordDigest: decisionCall.record.Digest ?? decisionCall.record.digest,
    positiveBoundsRecordDigest: boundsCall.record.Digest ?? boundsCall.record.digest,
    negativeDecisionCoord: decisionNegative.nf.coord,
    negativeDecisionPath: decisionNegative.nf.path,
    negativeDecisionRecordDigest: decisionNegative.nf.recordDigest,
    negativeBoundsCoord: boundsNegative.nf.coord,
    negativeBoundsPath: boundsNegative.nf.path,
    negativeBoundsRecordDigest: boundsNegative.nf.recordDigest,

    comparator: integration.SATDecision.DecisionRule.comparator,
    residualSlackBound: integration.SATBounds.Minimizer.residualSlackBound,
    finalSATPolynomialExponent: integration.SATBounds.Bounds.exponent,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    Scope: { ...GLOBAL_FINAL_SAT_SEMANTIC_SCOPE0 },
    scopeDigest: digestCanonical0(input.Scope),
    boundedExecutableSATReductionRefinementOnly: true,
    unrestrictedSATReductionSoundnessNotClaimed: true,
    complexityClassImplicationNotClaimed: true,
    publicTheoremEmissionAllowed: false,
    globalFinalComplexityImplicationReady: false,
    globalFinalDerivationsReady: false,
    globalSemanticNodeDerivationsReady: false,
    policyDigest: digestCanonical0(input.Policy),
  };

  return makeAcceptRecord0({
    checker,
    nf: {
      ...nf,
      refinementDigest: digestCanonical0(nf),
    },
    ledger,
  });
}

function makeFinalSATBinding0({ node, dependencyNodes, PCCPack }) {
  const base = Object.freeze({
    kind: 'GlobalFinalSATSemanticBinding0',
    version: CHECKER_VERSION,
    nodeId: GLOBAL_FINAL_SAT_NODE_ID0,
    globalNodeDigest: digestCanonical0(stripDigestFields0(node)),
    dependencyNodeIds: [...GLOBAL_FINAL_SAT_CONTRACT0.premises],
    dependencyNodeDigests: dependencyNodes.map((dep) => digestCanonical0(stripDigestFields0(dep))),
    finalIntegrationRecordDigest: digestCanonical0(PCCPack?.FinalIntegration ?? null),
    finalFrameworkRecordDigest: digestCanonical0(PCCPack?.FinalIntegration?.FinalMatch ?? null),
    satDecisionRecordDigest: digestCanonical0(PCCPack?.FinalIntegration?.SATDecision ?? null),
    satBoundsRecordDigest: digestCanonical0(PCCPack?.FinalIntegration?.SATBounds ?? null),
    gpackDigest: digestCanonical0(PCCPack?.GPack ?? null),
    packCoreDigest: digestCanonical0(PCCPack?.Core ?? null),
    packManifestDigest: digestCanonical0(PCCPack?.Manifest ?? null),
    checkerContractDigest: digestCanonical0(GLOBAL_FINAL_SAT_CONTRACT0),
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'global final SAT semantic input must be an object', { actual: typeof input });
  }
  if (input.kind !== 'GlobalFinalSATSemanticInput0') {
    return validationReject0(['kind'], 'global final SAT semantic input kind must be GlobalFinalSATSemanticInput0', { actual: input.kind });
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `global final SAT semantic input version must be ${CHECKER_VERSION}`, { actual: input.version });
  }
  const required = [
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
    'SemanticFinalSAT',
    'Scope',
    'Policy',
  ];
  for (const field of required) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0([field], 'global final SAT semantic input is missing a required field', { field });
    }
  }
  for (const field of required.slice(0, 11)) {
    if (!isPlainObject0(input[field])) {
      return validationReject0([field], 'global final SAT semantic dependency surface must be an object', { field, actual: typeof input[field] });
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(['KBundle', 'Purpose'], 'global final SAT semantic input KBundle must remain development-purpose', { actual: input.KBundle.Purpose });
  }
  if (!Array.isArray(input.LegacyGlobalProofDAG.Nodes)) {
    return validationReject0(['LegacyGlobalProofDAG', 'Nodes'], 'global final SAT semantic input requires a global Nodes array');
  }
  if (!sameCanonical0(input.Scope, GLOBAL_FINAL_SAT_SEMANTIC_SCOPE0)) {
    return validationReject0(['Scope'], 'global final SAT semantic scope must match the bounded fail-closed scope', { expected: GLOBAL_FINAL_SAT_SEMANTIC_SCOPE0, actual: input.Scope });
  }
  if (!sameCanonical0(input.Policy, GLOBAL_FINAL_SAT_SEMANTIC_POLICY0)) {
    return validationReject0(['Policy'], 'global final SAT semantic policy must match the fail-closed policy', { expected: GLOBAL_FINAL_SAT_SEMANTIC_POLICY0, actual: input.Policy });
  }
  const allowed = new Set(['kind', 'version', ...required]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0([unexpected[0]], 'global final SAT semantic checker rejects caller-supplied readiness or truth assertions', { unexpectedFields: unexpected.sort() });
  }
  return validationAccept0({ kind: 'GlobalFinalSATSemanticInputShape0NF' });
}

function validateSemanticSuite0(suite, dag, pack) {
  if (!isPlainObject0(suite)) {
    return validationReject0(['SemanticFinalSAT'], 'global final SAT semantic suite must be an object', { actual: typeof suite });
  }
  const allowed = new Set(['kind', 'version', 'suiteId', 'refinement', 'Scope', 'Policy']);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(['SemanticFinalSAT', unexpected[0]], 'global final SAT semantic suite rejects caller-supplied readiness or truth assertions', { unexpectedFields: unexpected.sort() });
  }
  if (suite.kind !== 'GlobalFinalSATSemanticSuite0'
      || suite.version !== CHECKER_VERSION
      || typeof suite.suiteId !== 'string'
      || !isPlainObject0(suite.refinement)
      || !sameCanonical0(suite.Scope, GLOBAL_FINAL_SAT_SEMANTIC_SCOPE0)
      || !sameCanonical0(suite.Policy, GLOBAL_FINAL_SAT_SEMANTIC_POLICY0)) {
    return validationReject0(['SemanticFinalSAT'], 'global final SAT semantic suite shape, scope, or policy mismatch', { actual: suite });
  }
  const expected = makeGlobalFinalSATSemanticSuite0({
    LegacyGlobalProofDAG: dag,
    PCCPack: pack,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['SemanticFinalSAT'],
      'global final SAT semantic suite must exactly match the computed final-node, dependency, integration, and checker bindings',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalSATSemanticSuite0NF',
    suiteId: suite.suiteId,
    nodeId: suite.refinement.nodeId,
    bindingDigest: suite.refinement.bindingDigest,
    scopeDigest: digestCanonical0(suite.Scope),
    policyDigest: digestCanonical0(suite.Policy),
  });
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
    globalPackageDerivationsReady: true,
    globalRowDerivationsReady: true,
    globalInfrastructureSemanticReady: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(['FinalPrefixPredecessor', 'NF', field], 'final-prefix predecessor readiness boundary mismatch', { field, expected: value, actual: nf[field] });
    }
  }
  if (!sameCanonical0(nf.semanticallyRefinedFinalNodeIds, GLOBAL_FINAL_PREFIX_NODE_IDS0)
      || !nf.remainingBlockedFinalNodeIds?.includes(GLOBAL_FINAL_SAT_NODE_ID0)
      || !sameCanonical0(nf.activeFinalNodeIds, [])) {
    return validationReject0(['FinalPrefixPredecessor', 'NF'], 'final-prefix predecessor must expose prefix refinements, block SAT implication, and expose no active final node', {
      semanticallyRefinedFinalNodeIds: nf.semanticallyRefinedFinalNodeIds,
      remainingBlockedFinalNodeIds: nf.remainingBlockedFinalNodeIds,
      activeFinalNodeIds: nf.activeFinalNodeIds,
    });
  }
  return validationAccept0({ kind: 'GlobalFinalSATPredecessorBoundary0NF', ...expected });
}

function validateFinalSATNode0({ node, nodeById, predecessorNF, globalBoundsExponent }) {
  const contract = GLOBAL_FINAL_SAT_CONTRACT0;
  if (!isPlainObject0(node)) {
    return validationReject0(['LegacyGlobalProofDAG', 'Nodes', contract.nodeId], 'final SAT coordinate is missing its global node', { nodeId: contract.nodeId });
  }
  if (node.id !== contract.nodeId || node.nodeKind !== contract.nodeKind || node.label !== contract.label) {
    return validationReject0(['LegacyGlobalProofDAG', 'Nodes', contract.nodeId], 'final SAT global node identity, kind, or label mismatch', { contract, actual: node });
  }
  if (!sameCanonical0(node.premises, contract.premises)) {
    return validationReject0(['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'premises'], 'final SAT global node premise list must exactly match its contract', { expected: contract.premises, actual: node.premises });
  }
  if (!sameCanonical0(node.imports, []) || String(node.mode ?? 'Full').trim().toLowerCase() !== 'full' || !sameCanonical0(node.payload, {}) || node.route !== null || node.rank !== null) {
    return validationReject0(['LegacyGlobalProofDAG', 'Nodes', contract.nodeId], 'final SAT global node must retain empty imports/payload, Full mode, and null route/rank', {
      imports: node.imports, mode: node.mode, payload: node.payload, route: node.route, rank: node.rank,
    });
  }
  if (node.conclusion?.tag !== contract.conclusionTag || node.conclusion?.theorem !== contract.theorem || Object.keys(node.conclusion).length !== 2) {
    return validationReject0(['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'conclusion'], 'final SAT global node conclusion must exactly match its theorem coordinate', { actual: node.conclusion });
  }
  if (!isPlainObject0(node.bounds) || node.bounds.polynomial !== true || !Number.isInteger(node.bounds.exponent) || node.bounds.exponent <= 0 || !Number.isInteger(globalBoundsExponent) || node.bounds.exponent > globalBoundsExponent) {
    return validationReject0(['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'bounds'], 'final SAT global node must carry a positive polynomial bound inside the global envelope', { globalBoundsExponent, actual: node.bounds });
  }
  for (const premise of contract.premises) {
    if (!isPlainObject0(nodeById.get(premise))) {
      return validationReject0(['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'premises'], 'final SAT premise must resolve to a global node', { premise });
    }
  }
  const overlay = predecessorNF.semanticOverlay;
  if (!overlay?.semanticPackageNodeIds?.includes('Package.G.LockedNANDThreshold')
      || !overlay?.semanticPackageNodeIds?.includes('Package.O.ZeroSlackOracle')
      || !overlay?.semanticFinalPrefixNodeIds?.includes('Final.GeneratedPackageSufficiency')) {
    return validationReject0(['FinalPrefixPredecessor', 'NF', 'semanticOverlay'], 'final SAT predecessor must semantically activate both package dependencies and generated-package prefix dependency', { actual: overlay });
  }
  return validationAccept0({ kind: 'GlobalFinalSATNodeContract0NF', nodeId: contract.nodeId, exponent: node.bounds.exponent });
}

function validateDecisionAndBoundsSurface0(integration) {
  const decision = integration.SATDecision;
  const bounds = integration.SATBounds;
  const match = integration.FinalMatch;
  const baseline = decision?.Baseline?.value;
  if (match?.MinMap?.exactMinimum !== true
      || match?.MinMap?.sameFrontierMinimum !== true
      || match?.MinMap?.decisionComparator !== 'minSize>baseline') {
    return validationReject0(['PCCPack', 'FinalIntegration', 'FinalMatch', 'MinMap'], 'final SAT framework must expose exact same-frontier minimization and the declared comparator', { actual: match?.MinMap });
  }
  if (decision?.DecisionRule?.comparator !== 'minSize>baseline'
      || decision?.DecisionRule?.usesExactMinimum !== true
      || decision?.DecisionRule?.rejectsApproximateMinimum !== true
      || decision?.NandConversion?.preservesSatisfiability !== true) {
    return validationReject0(['PCCPack', 'FinalIntegration', 'SATDecision'], 'final SAT decision must use exact minSize>baseline semantics and satisfiability-preserving conversion', { actual: decision });
  }
  for (const entry of decision.Cases ?? []) {
    if (entry.satisfiable === true && !(entry.minSize > baseline && entry.decision === 'SAT')) {
      return validationReject0(['PCCPack', 'FinalIntegration', 'SATDecision', 'Cases'], 'satisfiable case must be exactly minSize above baseline', { entry, baseline });
    }
    if (entry.satisfiable === false && !(entry.minSize === baseline && entry.decision === 'UNSAT')) {
      return validationReject0(['PCCPack', 'FinalIntegration', 'SATDecision', 'Cases'], 'unsatisfiable case must be exactly minSize equal to baseline', { entry, baseline });
    }
  }
  if (bounds?.Converter?.polynomial !== true
      || bounds?.LockedBuilder?.polynomial !== true
      || bounds?.Minimizer?.exact !== true
      || bounds?.Minimizer?.polynomialWhenResidualSlackBounded !== true
      || bounds?.Minimizer?.residualSlackBound !== 4
      || bounds?.DecisionProcedure?.polynomial !== true
      || bounds?.Bounds?.polynomial !== true
      || bounds?.Bounds?.finite !== true
      || bounds?.Bounds?.exponent !== 42) {
    return validationReject0(['PCCPack', 'FinalIntegration', 'SATBounds'], 'final SAT bounds must expose exact residual-band minimizer and finite polynomial decision bound', { actual: bounds });
  }
  return validationAccept0({
    kind: 'GlobalFinalSATDecisionAndBoundsSurface0NF',
    baseline,
    comparator: decision.DecisionRule.comparator,
    residualSlackBound: bounds.Minimizer.residualSlackBound,
    exponent: bounds.Bounds.exponent,
  });
}

async function runDecisionNegativeProbe0(decision) {
  const mutated = {
    ...decision,
    DecisionRule: {
      ...decision.DecisionRule,
      usesExactMinimum: false,
    },
  };
  const call = await callChecker0('CheckSATDecision0.negative', () => CheckSATDecision0(mutated));
  if (!call.ok) return validationReject0(['SATDecision', 'negativeProbe'], 'SAT decision negative probe threw', call.witness);
  if (call.record.tag !== 'reject' || call.record.checker !== 'CheckSATDecision0') {
    return validationReject0(['SATDecision', 'negativeProbe'], 'SAT decision negative probe must reject', { actual: compactRecord0(call.record) });
  }
  return validationAccept0({ kind: 'GlobalFinalSATDecisionNegativeProbe0NF', coord: call.record.Coord ?? call.record.coord, path: call.record.Path ?? call.record.path, recordDigest: call.record.Digest ?? call.record.digest });
}

async function runBoundsNegativeProbe0(bounds) {
  const mutated = {
    ...bounds,
    Bounds: {
      ...bounds.Bounds,
      polynomial: false,
    },
  };
  const call = await callChecker0('CheckSATBounds0.negative', () => CheckSATBounds0(mutated));
  if (!call.ok) return validationReject0(['SATBounds', 'negativeProbe'], 'SAT bounds negative probe threw', call.witness);
  if (call.record.tag !== 'reject' || call.record.checker !== 'CheckSATBounds0') {
    return validationReject0(['SATBounds', 'negativeProbe'], 'SAT bounds negative probe must reject', { actual: compactRecord0(call.record) });
  }
  return validationAccept0({ kind: 'GlobalFinalSATBoundsNegativeProbe0NF', coord: call.record.Coord ?? call.record.coord, path: call.record.Path ?? call.record.path, recordDigest: call.record.Digest ?? call.record.digest });
}

function validatePackAlignment0(input) {
  const pack = input.PCCPack;
  const checks = [
    ['GlobalProofDAG', pack.GlobalProofDAG, input.LegacyGlobalProofDAG],
    ['RowPack', pack.RowPack, input.RowPack],
    ['LocalPackages', pack.LocalPackages, input.LocalPackages],
    ['RowFamG', pack.RowFamG, input.RowFamG],
    ['GPack', pack.GPack, input.RowFamG?.GPack],
    ['FinalIntegration.GlobalProofDAG', pack.FinalIntegration?.GlobalProofDAG, input.LegacyGlobalProofDAG],
    ['FinalIntegration.GPack', pack.FinalIntegration?.GPack, input.RowFamG?.GPack],
    ['FinalTheorem.FinalIntegration', pack.FinalTheorem?.FinalIntegration, pack.FinalIntegration],
    ['RowFamFinal.FinalTheorem', pack.RowFamFinal?.FinalTheorem, pack.FinalTheorem],
  ];
  for (const [name, actual, expected] of checks) {
    if (!sameCanonical0(actual, expected)) {
      return validationReject0(['PCCPack', ...name.split('.')], 'final SAT PCCPack surface must exactly align with the semantic predecessor inputs', {
        surface: name,
        expectedDigest: digestCanonical0(expected ?? null),
        actualDigest: digestCanonical0(actual ?? null),
      });
    }
  }
  return validationAccept0({ kind: 'GlobalFinalSATPackAlignment0NF', alignedSurfaces: checks.map(([name]) => name) });
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
      return { ok: false, witness: { reason: `${name} did not return a total accept/reject record`, actual: record } };
    }
    return { ok: true, record };
  } catch (error) {
    return { ok: false, witness: { reason: `${name} threw instead of returning a reject record`, errorName: error?.name ?? null, errorMessage: error?.message ?? String(error) } };
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

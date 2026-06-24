import {
  digestCanonical0,
} from './pcc-verifier-frag0.mjs';

import {
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

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
  makeSyntheticPCCPack0,
  makeSyntheticPackSufficiencyTheorem0,
} from './pcc-pack-sufficiency0.mjs';

import {
  makeSyntheticFinalIntegration0,
} from './pcc-final-framework0.mjs';

import {
  makeSyntheticFinalTheorem0,
  makeSyntheticRowFamFinal0,
} from './pcc-final0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_FINAL_PREFIX_NODE_IDS0 = Object.freeze([
  'Final.PackageSoundness',
  'Final.GeneratedPackageSufficiency',
]);

export const GLOBAL_FINAL_REMAINING_NODE_IDS0 = Object.freeze([
  'Final.AcceptedPackageImpliesSATinP',
  'Final.AcceptedPackageImpliesPEqualsNP',
]);

export const PACK_PACKAGE_NODE_ID0 = 'Package.PACK.PackageSufficiency';

export const GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0 = Object.freeze({
  kind: 'GlobalFinalPrefixSemanticScope0',
  version: CHECKER_VERSION,
  scope: 'bounded-executable-final-prefix-refinement',
  packageSuccessorPredecessorChecked: true,
  packSufficiencyCheckerReplayed: true,
  packSurfaceAlignedToSemanticPredecessor: true,
  packageSoundnessNodeContractChecked: true,
  generatedPackageSufficiencyNodeContractChecked: true,
  positiveAndNegativePackProbesChecked: true,
  canonicalGeneratorBoundaryMetadataChecked: true,
  boundedExecutableFinalPrefixRefinementsOnly: true,
  unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
  satReductionSoundnessNotClaimed: true,
  complexityClassImplicationNotClaimed: true,
  publicTheoremEmissionNotAllowed: true,
});

export const GLOBAL_FINAL_PREFIX_SEMANTIC_POLICY0 = Object.freeze({
  kind: 'GlobalFinalPrefixSemanticPolicy0',
  version: CHECKER_VERSION,
  requiresSemanticPackageSuccessorAcceptance: true,
  requiresPackSufficiencyAcceptance: true,
  requiresExactPackSurfaceAlignment: true,
  oneRefinementPerFinalPrefixCoordinate: true,
  exactFinalNodeContractsRequired: true,
  packageSoundnessPositiveProbeRequired: true,
  packageSoundnessNegativeProbeRequired: true,
  generatedSufficiencyPositiveProbeRequired: true,
  generatedSufficiencyNegativeProbeRequired: true,
  bindsGlobalNodeDigest: true,
  bindsDependencyNodeDigest: true,
  bindsPackCoreManifestAndTheoremDigests: true,
  bindsSourceRecordDigest: true,
  bindsPositiveAndNegativeRecordDigests: true,
  callerReadinessAssertionsForbidden: true,
  boundedExecutableFinalPrefixRefinementsOnly: true,
  unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
  satAndComplexityImplicationsRemainSeparate: true,
});

export const GLOBAL_FINAL_PREFIX_CONTRACTS0 = Object.freeze({
  'Final.PackageSoundness': Object.freeze({
    kind: 'GlobalFinalPrefixCheckerContract0',
    version: CHECKER_VERSION,
    index: 0,
    nodeId: 'Final.PackageSoundness',
    nodeKind: 'final',
    label: 'Final.PackageSoundness',
    premises: Object.freeze([PACK_PACKAGE_NODE_ID0]),
    dependencyNodeId: PACK_PACKAGE_NODE_ID0,
    conclusionTag: 'FinalTheoremAccepted0',
    theorem: 'Final.PackageSoundness',
    sourceRecord: 'PackSufficiencyTheorem.packageSufficiency',
    positiveChecker: 'CheckPackSufficiency0',
    negativeField: 'acceptedPackageValid',
    negativePath: Object.freeze([
      'PackSufficiencyTheorem',
      'packageSufficiency',
      'acceptedPackageValid',
    ]),
    unrestrictedTheoremSoundnessNotClaimed: true,
  }),
  'Final.GeneratedPackageSufficiency': Object.freeze({
    kind: 'GlobalFinalPrefixCheckerContract0',
    version: CHECKER_VERSION,
    index: 1,
    nodeId: 'Final.GeneratedPackageSufficiency',
    nodeKind: 'final',
    label: 'Final.GeneratedPackageSufficiency',
    premises: Object.freeze(['Final.PackageSoundness']),
    dependencyNodeId: 'Final.PackageSoundness',
    conclusionTag: 'FinalTheoremAccepted0',
    theorem: 'Final.GeneratedPackageSufficiency',
    sourceRecord: 'PackSufficiencyTheorem.generatedPackageSufficiency',
    positiveChecker: 'CheckPackSufficiency0',
    negativeField: 'canonicalByteEquality',
    negativePath: Object.freeze([
      'PackSufficiencyTheorem',
      'generatedPackageSufficiency',
      'canonicalByteEquality',
    ]),
    unrestrictedTheoremSoundnessNotClaimed: true,
  }),
});

export function makeGlobalFinalPrefixPCCPack0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  RowPack = makeSyntheticRowPack0(),
  RowFamG = makeSyntheticRowFamG0(),
  LocalPackages = makeSyntheticLocalPackages0(),
} = {}) {
  const gpack = RowFamG?.GPack ?? makeSyntheticRowFamG0().GPack;
  const finalIntegration = makeSyntheticFinalIntegration0({
    gpack,
    overrides: {
      GlobalProofDAG: LegacyGlobalProofDAG,
    },
  });
  const finalTheorem = makeSyntheticFinalTheorem0({ finalIntegration });
  return makeSyntheticPCCPack0({
    RowPack,
    GlobalProofDAG: LegacyGlobalProofDAG,
    LocalPackages,
    GPack: gpack,
    RowFamG,
    FinalIntegration: finalIntegration,
    FinalTheorem: finalTheorem,
    RowFamFinal: makeSyntheticRowFamFinal0(finalTheorem),
    PackSufficiencyTheorem: makeSyntheticPackSufficiencyTheorem0(),
  });
}

export function makeGlobalFinalPrefixSemanticSuite0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  PCCPack = makeGlobalFinalPrefixPCCPack0({ LegacyGlobalProofDAG }),
} = {}) {
  const nodeById = new Map(
    (LegacyGlobalProofDAG?.Nodes ?? []).map((node) => [node?.id, node]),
  );
  return Object.freeze({
    kind: 'GlobalFinalPrefixSemanticSuite0',
    version: CHECKER_VERSION,
    suiteId: 'GlobalDAG.final-prefix.semantic.phase37',
    refinements: Object.freeze(
      GLOBAL_FINAL_PREFIX_NODE_IDS0.map((nodeId, index) =>
        makeFinalPrefixBinding0({
          index,
          nodeId,
          node: nodeById.get(nodeId) ?? null,
          dependencyNode:
            nodeById.get(
              GLOBAL_FINAL_PREFIX_CONTRACTS0[nodeId].dependencyNodeId,
            ) ?? null,
          PCCPack,
        })),
    ),
    Scope: { ...GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0 },
    Policy: { ...GLOBAL_FINAL_PREFIX_SEMANTIC_POLICY0 },
  });
}

export function makeGlobalFinalPrefixSemanticInput0({
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
  SemanticFinalPrefix = makeGlobalFinalPrefixSemanticSuite0({
    LegacyGlobalProofDAG,
    PCCPack,
  }),
} = {}) {
  return Object.freeze({
    kind: 'GlobalFinalPrefixSemanticInput0',
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
    SemanticFinalPrefix,
    Scope: { ...GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0 },
    Policy: { ...GLOBAL_FINAL_PREFIX_SEMANTIC_POLICY0 },
  });
}

export function makeFinalPrefixBinding0({
  index,
  nodeId,
  node,
  dependencyNode,
  PCCPack,
}) {
  const contract = GLOBAL_FINAL_PREFIX_CONTRACTS0[nodeId];
  const sourceRecord = getFinalPrefixSourceRecord0(PCCPack, nodeId);
  const base = Object.freeze({
    kind: 'GlobalFinalPrefixSemanticBinding0',
    version: CHECKER_VERSION,
    index,
    nodeId,
    globalNodeDigest: digestCanonical0(stripDigestFields0(node)),
    dependencyNodeId: contract.dependencyNodeId,
    dependencyNodeDigest:
      digestCanonical0(stripDigestFields0(dependencyNode)),
    sourceRecordDigest: digestCanonical0(sourceRecord),
    packCoreDigest: digestCanonical0(PCCPack?.Core ?? null),
    packManifestDigest: digestCanonical0(PCCPack?.Manifest ?? null),
    packTheoremDigest:
      digestCanonical0(PCCPack?.PackSufficiencyTheorem ?? null),
    canonicalBytesDigest:
      digestCanonical0(PCCPack?.Core?.canonicalBytes ?? null),
    checkerContractDigest: digestCanonical0(contract),
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

export function getFinalPrefixSourceRecord0(pack, nodeId) {
  if (nodeId === 'Final.PackageSoundness') {
    return pack?.PackSufficiencyTheorem?.packageSufficiency ?? null;
  }
  if (nodeId === 'Final.GeneratedPackageSufficiency') {
    return pack?.PackSufficiencyTheorem?.generatedPackageSufficiency ?? null;
  }
  return null;
}

function stripDigestFields0(value) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    return value;
  }
  const out = {};
  for (const key of Object.keys(value).sort()) {
    if (key !== 'Digest' && key !== 'digest') out[key] = value[key];
  }
  return out;
}

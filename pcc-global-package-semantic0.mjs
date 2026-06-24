import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0,
  makeSyntheticGlobalProofDAG0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGRowSuccessor0,
  GLOBAL_SEMANTIC_ROW_NODE_IDS0,
  makeGlobalProofDAGRowSuccessor0,
} from './pcc-global-proof-dag-row-successor0.mjs';

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
  CheckLocalPackageFamily0,
  CheckLocalPackages0,
  LOCAL_PACKAGE_REQUIREMENTS0,
  LOCAL_PACKAGE_REQUIRED_FAMILIES0,
  makeSyntheticLocalPackages0,
} from './pcc-local-packages0.mjs';

const CHECKER_VERSION = 0;

export const GLOBAL_PACKAGE_NODE_IDS0 = Object.freeze(
  GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0.map(
    (theorem) => `Package.${theorem}`,
  ),
);

export const GLOBAL_PACKAGE_SEMANTIC_REQUIREMENTS0 = Object.freeze(
  LOCAL_PACKAGE_REQUIREMENTS0.filter((requirement) =>
    GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0.includes(requirement.theorem)),
);

export const GLOBAL_SUPPORTING_LOCAL_PACKAGE_FAMILIES0 = Object.freeze(
  LOCAL_PACKAGE_REQUIREMENTS0
    .filter((requirement) =>
      !GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0.includes(requirement.theorem))
    .map((requirement) => requirement.family),
);

export const GLOBAL_PACKAGE_SEMANTIC_SCOPE0 = Object.freeze({
  kind: 'GlobalPackageSemanticScope0',
  version: CHECKER_VERSION,
  scope: 'bounded-executable-local-package-refinement',
  localPackageInventoryChecked: true,
  localFamilyPositiveProbesChecked: true,
  localFamilyNegativeIdentityProbesChecked: true,
  globalPackageNodeBindingsChecked: true,
  rowToPackageBindingsChecked: true,
  localImportDependenciesChecked: true,
  supportingLocalPackagesChecked: true,
  boundedExecutablePackageRefinementsOnly: true,
  unrestrictedPackageTheoremSoundnessNotClaimed: true,
  finalTheoremSoundnessNotClaimedHere: true,
});

export const GLOBAL_PACKAGE_SEMANTIC_POLICY0 = Object.freeze({
  kind: 'GlobalPackageSemanticPolicy0',
  version: CHECKER_VERSION,
  requiresSemanticRowSuccessorAcceptance: true,
  requiresLocalPackageInventoryAcceptance: true,
  oneRefinementPerGlobalPackageTheorem: true,
  exactGlobalPackageNodeContractRequired: true,
  exactLocalPackageRequirementRequired: true,
  exactRowReferenceBindingRequired: true,
  localPackagePositiveProbeRequired: true,
  localPackageNegativeIdentityProbeRequired: true,
  localPackageImportsMustResolve: true,
  supportingLocalPackagesRemainChecked: true,
  bindsEveryRefinementToGlobalNodeDigest: true,
  bindsEveryRefinementToLocalPackageDigest: true,
  bindsEveryRefinementToRowDerivationDigest: true,
  bindsEveryRefinementToPositiveAndNegativeRecords: true,
  callerReadinessAssertionsForbidden: true,
  boundedExecutablePackageRefinementsOnly: true,
  unrestrictedPackageTheoremSoundnessNotClaimed: true,
  finalDerivationsRemainSeparate: true,
});

export function makeGlobalPackageSemanticSuite0({
  LegacyGlobalProofDAG = makeSyntheticGlobalProofDAG0(),
  LocalPackages = makeSyntheticLocalPackages0(),
} = {}) {
  const nodeById = new Map(
    (LegacyGlobalProofDAG?.Nodes ?? []).map((node) => [node?.id, node]),
  );
  const packageByFamily = new Map(
    (LocalPackages?.Packages ?? []).map((entry) => [entry?.family, entry]),
  );

  return Object.freeze({
    kind: 'GlobalPackageSemanticSuite0',
    version: CHECKER_VERSION,
    suiteId: 'GlobalDAG.packages.semantic.phase36',
    refinements: Object.freeze(
      GLOBAL_PACKAGE_SEMANTIC_REQUIREMENTS0.map((requirement, index) =>
        makePackageBinding0({
          index,
          requirement,
          node: nodeById.get(`Package.${requirement.theorem}`) ?? null,
          localPackage: packageByFamily.get(requirement.family) ?? null,
        })),
    ),
    supportingPackages: Object.freeze(
      GLOBAL_SUPPORTING_LOCAL_PACKAGE_FAMILIES0.map((family, index) => {
        const localPackage = packageByFamily.get(family) ?? null;
        return Object.freeze({
          kind: 'GlobalSupportingLocalPackageBinding0',
          version: CHECKER_VERSION,
          index,
          family,
          theorem: localPackage?.theorem ?? null,
          localPackageDigest: digestCanonical0(localPackage),
        });
      }),
    ),
    Scope: { ...GLOBAL_PACKAGE_SEMANTIC_SCOPE0 },
    Policy: { ...GLOBAL_PACKAGE_SEMANTIC_POLICY0 },
  });
}

export function makeGlobalPackageSemanticInput0({
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
  SemanticPackages = makeGlobalPackageSemanticSuite0({
    LegacyGlobalProofDAG,
    LocalPackages,
  }),
} = {}) {
  return Object.freeze({
    kind: 'GlobalPackageSemanticInput0',
    version: CHECKER_VERSION,
    KBundle,
    LegacyGlobalProofDAG,
    InfrastructureSemanticDerivations,
    RowPack,
    RowFamG,
    RowSemanticDerivations,
    LocalPackages,
    SemanticPackages,
    Scope: { ...GLOBAL_PACKAGE_SEMANTIC_SCOPE0 },
    Policy: { ...GLOBAL_PACKAGE_SEMANTIC_POLICY0 },
  });
}

export async function CheckGlobalPackageSemantic0(input) {
  const checker = 'CheckGlobalPackageSemantic0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGRowSuccessor0',
    () => CheckGlobalProofDAGRowSuccessor0(
      makeGlobalProofDAGRowSuccessor0({
        KBundle: input.KBundle,
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        InfrastructureSemanticDerivations:
          input.InfrastructureSemanticDerivations,
        RowPack: input.RowPack,
        RowFamG: input.RowFamG,
        RowSemanticDerivations: input.RowSemanticDerivations,
        Purpose: 'development',
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGRowSuccessor0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticRowPredecessor.exception`,
      path: ['RowSemanticDerivations'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticRowPredecessor`,
      path: ['RowSemanticDerivations'],
      witness: {
        reason: 'package refinements require an accepted semantic row predecessor',
        inner: compactRecord0(predecessorCall.record),
      },
      ledger,
    });
  }
  const predecessorNF =
    predecessorCall.record.NF ?? predecessorCall.record.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'semanticRowPredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticRowPredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const localPackCall = await callChecker0(
    'CheckLocalPackages0',
    () => CheckLocalPackages0(input.LocalPackages),
  );
  ledger.push(makeLedgerEntry0(
    'CheckLocalPackages0',
    localPackCall.ok && localPackCall.record.tag === 'accept',
    localPackCall.ok ? localPackCall.record : localPackCall.witness,
  ));
  if (!localPackCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.localPackages.exception`,
      path: ['LocalPackages'],
      witness: localPackCall.witness,
      ledger,
    });
  }
  if (localPackCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.localPackages`,
      path: ['LocalPackages'],
      witness: {
        reason: 'global package refinements require an accepted local package inventory',
        inner: compactRecord0(localPackCall.record),
      },
      ledger,
    });
  }

  const suite = validateSemanticSuite0(
    input.SemanticPackages,
    input.LegacyGlobalProofDAG,
    input.LocalPackages,
  );
  ledger.push(makeLedgerEntry0(
    'semanticPackagesSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticPackagesSuite`,
      suite,
      ledger,
    );
  }

  const nodeById = new Map(
    input.LegacyGlobalProofDAG.Nodes.map((node) => [node.id, node]),
  );
  const rowByFamily = new Map(
    input.RowPack.Rows.map((row) => [row.FamilyID, row]),
  );
  const packageByFamily = new Map(
    input.LocalPackages.Packages.map((entry) => [entry.family, entry]),
  );
  const rowDerivationByNodeId = new Map(
    (predecessorNF.globalRowDerivationDigests ?? []).map((entry) => [
      entry.nodeId,
      entry,
    ]),
  );

  const supportingPackages = [];
  for (const family of GLOBAL_SUPPORTING_LOCAL_PACKAGE_FAMILIES0) {
    const localPackage = packageByFamily.get(family);
    const call = await callChecker0(
      `CheckLocalPackageFamily0(${family})`,
      () => CheckLocalPackageFamily0(localPackage),
    );
    ledger.push(makeLedgerEntry0(
      `supportingPackage.${family}`,
      call.ok && call.record.tag === 'accept',
      call.ok ? call.record : call.witness,
    ));
    if (!call.ok) {
      return makeRejectRecord0({
        checker,
        coord: `${checker}.supportingPackage.${safeCoord0(family)}.exception`,
        path: ['LocalPackages', 'Packages', family],
        witness: call.witness,
        ledger,
      });
    }
    if (call.record.tag !== 'accept') {
      return makeRejectRecord0({
        checker,
        coord: `${checker}.supportingPackage.${safeCoord0(family)}`,
        path: ['LocalPackages', 'Packages', family],
        witness: {
          reason: 'supporting local package checker rejected',
          inner: compactRecord0(call.record),
        },
        ledger,
      });
    }
    supportingPackages.push(Object.freeze({
      family,
      theorem: localPackage.theorem,
      localPackageDigest: digestCanonical0(localPackage),
      positiveRecordDigest: call.record.Digest ?? call.record.digest,
      positiveNFKind: (call.record.NF ?? call.record.nf)?.kind ?? null,
    }));
  }

  const refinements = [];
  for (let index = 0;
    index < GLOBAL_PACKAGE_SEMANTIC_REQUIREMENTS0.length;
    index += 1) {
    const requirement = GLOBAL_PACKAGE_SEMANTIC_REQUIREMENTS0[index];
    const nodeId = `Package.${requirement.theorem}`;
    const localPackage = packageByFamily.get(requirement.family);
    const node = nodeById.get(nodeId);
    const row = rowByFamily.get(requirement.family);
    const rowDerivation = rowDerivationByNodeId.get(`Row.${requirement.family}`);
    const binding = input.SemanticPackages.refinements[index];

    const result = await checkPackageRefinement0({
      index,
      requirement,
      node,
      localPackage,
      row,
      rowDerivation,
      binding,
      packageByFamily,
      globalBoundsExponent: input.LegacyGlobalProofDAG.BoundsLedger?.exponent,
    });
    ledger.push(makeLedgerEntry0(
      `package.${requirement.family}`,
      result.ok,
      result.nf ?? result.witness,
    ));
    if (!result.ok) {
      return makeRejectFromValidation0(
        checker,
        `${checker}.package.${safeCoord0(requirement.family)}`,
        result,
        ledger,
      );
    }
    refinements.push(result.nf);
  }

  const localPackNF = localPackCall.record.NF ?? localPackCall.record.nf ?? {};
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalPackageSemantic0NF',
      checker,
      version: CHECKER_VERSION,
      globalPackageSemanticReady: true,
      globalPackageDerivationsReady: true,
      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,

      semanticRowPredecessorAccepted: true,
      semanticRowPredecessorChecker: predecessorCall.record.checker,
      semanticRowPredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      globalRowDerivationsReady: predecessorNF.globalRowDerivationsReady === true,
      globalInfrastructureSemanticReady:
        predecessorNF.globalInfrastructureSemanticReady === true,
      semanticKBundleFinalReady: predecessorNF.kBundleFinalReady === true,
      semanticK0ConformanceReady:
        predecessorNF.semanticK0ConformanceReady === true,
      semanticSigmaReady: predecessorNF.semanticSigmaReady === true,
      semanticReflectionReady: predecessorNF.semanticReflectionReady === true,

      localPackageInventoryAccepted: true,
      localPackageInventoryChecker: localPackCall.record.checker,
      localPackageInventoryDigest:
        localPackCall.record.Digest ?? localPackCall.record.digest,
      localPackageCount:
        localPackNF.packageCount ?? input.LocalPackages.Packages.length,
      localPackageFamilies:
        localPackNF.families ?? [...LOCAL_PACKAGE_REQUIRED_FAMILIES0],
      localPackageObjectDigest: digestCanonical0(input.LocalPackages),

      globalPackageTheorems: [...GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0],
      globalPackageNodeIds: [...GLOBAL_PACKAGE_NODE_IDS0],
      globalPackageRefinementCount: refinements.length,
      positiveProbeCount: refinements.length,
      negativeProbeCount: refinements.length,
      packageRefinements: refinements,
      packageRefinementDigests: refinements.map((entry) => ({
        family: entry.family,
        theorem: entry.theorem,
        nodeId: entry.nodeId,
        digest: entry.refinementDigest,
        globalNodeDigest: entry.globalNodeDigest,
        localPackageDigest: entry.localPackageDigest,
        rowDerivationDigest: entry.rowDerivationDigest,
        positiveRecordDigest: entry.positiveRecordDigest,
        negativeRecordDigest: entry.negativeRecordDigest,
        checkerContractDigest: entry.checkerContractDigest,
        conclusionDigest: entry.conclusionDigest,
      })),
      supportingLocalPackageFamilies:
        [...GLOBAL_SUPPORTING_LOCAL_PACKAGE_FAMILIES0],
      supportingLocalPackageCount: supportingPackages.length,
      supportingLocalPackages: supportingPackages,

      Scope: { ...GLOBAL_PACKAGE_SEMANTIC_SCOPE0 },
      scopeDigest: digestCanonical0(input.Scope),
      boundedExecutablePackageRefinementsOnly: true,
      unrestrictedPackageTheoremSoundnessNotClaimed: true,
      finalTheoremSoundnessNotClaimedHere: true,
      finalDerivationsRemainSeparate: true,
      callerReadinessAssertionsForbidden: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
  });
}

async function checkPackageRefinement0({
  index,
  requirement,
  node,
  localPackage,
  row,
  rowDerivation,
  binding,
  packageByFamily,
  globalBoundsExponent,
}) {
  const nodeValidation = validateGlobalPackageNode0({
    requirement,
    node,
    globalBoundsExponent,
  });
  if (!nodeValidation.ok) return nodeValidation;

  const localValidation = validateLocalPackageAndRowBinding0({
    requirement,
    localPackage,
    row,
    rowDerivation,
    packageByFamily,
  });
  if (!localValidation.ok) return localValidation;

  const expectedBinding = makePackageBinding0({
    index,
    requirement,
    node,
    localPackage,
  });
  if (!sameCanonical0(binding, expectedBinding)) {
    return validationReject0(
      ['SemanticPackages', 'refinements', index],
      'global package refinement binding must exactly match the computed global node, local package, row reference, imports, and checker contract',
      {
        family: requirement.family,
        theorem: requirement.theorem,
        expected: expectedBinding,
        actual: binding,
      },
    );
  }

  const positiveCall = await callChecker0(
    `CheckLocalPackageFamily0(${requirement.family}).positive`,
    () => CheckLocalPackageFamily0(localPackage),
  );
  if (!positiveCall.ok) {
    return validationReject0(
      ['LocalPackages', 'Packages', requirement.family],
      'local package positive probe threw instead of returning a total record',
      positiveCall.witness,
    );
  }
  const positiveRecord = positiveCall.record;
  const positiveNF = positiveRecord.NF ?? positiveRecord.nf ?? {};
  if (positiveRecord.tag !== 'accept'
      || positiveRecord.checker !== 'CheckLocalPackageFamily0'
      || positiveNF.kind !== 'LocalPackageFamily0NF'
      || positiveNF.family !== requirement.family
      || positiveNF.theorem !== requirement.theorem) {
    return validationReject0(
      ['LocalPackages', 'Packages', requirement.family, 'positiveProbe'],
      'local package positive probe did not accept the exact family theorem contract',
      {
        expectedFamily: requirement.family,
        expectedTheorem: requirement.theorem,
        actual: compactRecord0(positiveRecord),
        actualNF: positiveNF,
      },
    );
  }

  const negativeInput = {
    ...localPackage,
    theorem: `${localPackage.theorem}.negative-probe`,
  };
  const negativeCall = await callChecker0(
    `CheckLocalPackageFamily0(${requirement.family}).negative`,
    () => CheckLocalPackageFamily0(negativeInput),
  );
  if (!negativeCall.ok) {
    return validationReject0(
      ['LocalPackages', 'Packages', requirement.family, 'negativeProbe'],
      'local package negative probe threw instead of returning a total record',
      negativeCall.witness,
    );
  }
  const negativeRecord = negativeCall.record;
  if (negativeRecord.tag !== 'reject'
      || negativeRecord.checker !== 'CheckLocalPackageFamily0'
      || (negativeRecord.Coord ?? negativeRecord.coord)
        !== 'CheckLocalPackageFamily0.identity'
      || !sameCanonical0(
        negativeRecord.Path ?? negativeRecord.path,
        ['theorem'],
      )) {
    return validationReject0(
      ['LocalPackages', 'Packages', requirement.family, 'negativeProbe'],
      'local package negative theorem-identity probe did not reject at the declared coordinate',
      {
        expectedCoord: 'CheckLocalPackageFamily0.identity',
        expectedPath: ['theorem'],
        actual: compactRecord0(negativeRecord),
      },
    );
  }

  const importBindings = localPackage.imports.map((family) => {
    const imported = packageByFamily.get(family);
    return Object.freeze({
      family,
      theorem: imported?.theorem ?? null,
      localPackageDigest: digestCanonical0(imported),
      representedByGlobalPackageNode:
        GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0.includes(imported?.theorem),
      globalPackageNodeId:
        GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0.includes(imported?.theorem)
          ? `Package.${imported.theorem}`
          : null,
    });
  });

  const conclusion = Object.freeze({
    kind: 'GlobalPackageSemanticRefinementConclusion0',
    version: CHECKER_VERSION,
    family: requirement.family,
    theorem: requirement.theorem,
    nodeId: `Package.${requirement.theorem}`,
    positiveExecutableContractAccepted: true,
    negativeTheoremIdentityProbeRejected: true,
    rowReferenceBound: true,
    importDependenciesBound: true,
    boundedExecutablePackageRefinement: true,
    unrestrictedPackageTheoremSoundnessNotClaimed: true,
  });

  const nf = {
    kind: 'GlobalPackageSemanticRefinement0NF',
    version: CHECKER_VERSION,
    index,
    family: requirement.family,
    theorem: requirement.theorem,
    nodeId: `Package.${requirement.theorem}`,
    packageId: requirement.packageId,
    batchId: requirement.batchId,
    schemaId: requirement.schemaId,
    proofRule: requirement.proofRule,
    globalNodeDigest: expectedBinding.globalNodeDigest,
    localPackageDigest: expectedBinding.localPackageDigest,
    rowRefDigest: expectedBinding.rowRefDigest,
    importsDigest: expectedBinding.importsDigest,
    checkerContractDigest: expectedBinding.checkerContractDigest,
    bindingDigest: expectedBinding.bindingDigest,
    rowNodeId: `Row.${requirement.family}`,
    rowDigest: localValidation.nf.rowDigest,
    rowDerivationDigest: localValidation.nf.rowDerivationDigest,
    importBindings,
    positiveNFKind: positiveNF.kind,
    positiveRecordDigest:
      positiveRecord.Digest ?? positiveRecord.digest,
    negativeCoord:
      negativeRecord.Coord ?? negativeRecord.coord,
    negativePath:
      negativeRecord.Path ?? negativeRecord.path,
    negativeRecordDigest:
      negativeRecord.Digest ?? negativeRecord.digest,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    boundedExecutablePackageRefinement: true,
    unrestrictedPackageTheoremSoundnessNotClaimed: true,
    ready: true,
  };
  return validationAccept0({
    ...nf,
    refinementDigest: digestCanonical0(nf),
  });
}

function makePackageBinding0({ index, requirement, node, localPackage }) {
  const contract = makePackageCheckerContract0(requirement);
  const base = Object.freeze({
    kind: 'GlobalPackageSemanticBinding0',
    version: CHECKER_VERSION,
    index,
    family: requirement.family,
    theorem: requirement.theorem,
    nodeId: `Package.${requirement.theorem}`,
    globalNodeDigest: digestCanonical0(stripDigestFields0(node)),
    localPackageDigest: digestCanonical0(localPackage),
    rowRefDigest: digestCanonical0(localPackage?.rowRefs ?? null),
    importsDigest: digestCanonical0(localPackage?.imports ?? null),
    checkerContractDigest: digestCanonical0(contract),
  });
  return Object.freeze({
    ...base,
    bindingDigest: digestCanonical0(base),
  });
}

function makePackageCheckerContract0(requirement) {
  return Object.freeze({
    kind: 'GlobalPackageExecutableCheckerContract0',
    version: CHECKER_VERSION,
    family: requirement.family,
    theorem: requirement.theorem,
    nodeId: `Package.${requirement.theorem}`,
    checker: 'CheckLocalPackageFamily0',
    positiveNFKind: 'LocalPackageFamily0NF',
    negativeMutation: 'theorem-identity',
    negativeCoord: 'CheckLocalPackageFamily0.identity',
    negativePath: Object.freeze(['theorem']),
    globalNodeKind: 'package',
    globalPremises: Object.freeze(expectedPackagePremises0(requirement.theorem)),
    globalConclusion: Object.freeze({
      tag: 'PackageTheoremAccepted0',
      theorem: requirement.theorem,
    }),
    boundedExecutablePackageRefinement: true,
    unrestrictedPackageTheoremSoundnessNotClaimed: true,
  });
}

function validateGlobalPackageNode0({
  requirement,
  node,
  globalBoundsExponent,
}) {
  const nodeId = `Package.${requirement.theorem}`;
  if (!isPlainObject0(node)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', nodeId],
      'global package theorem coordinate is missing its global proof node',
      { family: requirement.family, theorem: requirement.theorem },
    );
  }
  for (const [field, expected] of Object.entries({
    id: nodeId,
    nodeKind: 'package',
    label: requirement.theorem,
  })) {
    if (node[field] !== expected) {
      return validationReject0(
        ['LegacyGlobalProofDAG', 'Nodes', nodeId, field],
        'global package theorem node identity or kind mismatch',
        { field, expected, actual: node[field] },
      );
    }
  }
  const expectedPremises = expectedPackagePremises0(requirement.theorem);
  if (!sameCanonical0(node.premises, expectedPremises)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', nodeId, 'premises'],
      'global package theorem node premise list must exactly match its executable refinement contract',
      { expected: expectedPremises, actual: node.premises },
    );
  }
  if (!sameCanonical0(node.imports, [])) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', nodeId, 'imports'],
      'global package theorem node must not introduce undeclared global imports',
      { actual: node.imports },
    );
  }
  if (String(node.mode ?? 'Full').trim().toLowerCase() !== 'full') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', nodeId, 'mode'],
      'global package theorem refinement requires Full mode',
      { actual: node.mode },
    );
  }
  const expectedConclusion = {
    tag: 'PackageTheoremAccepted0',
    theorem: requirement.theorem,
  };
  if (!sameCanonical0(node.conclusion, expectedConclusion)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', nodeId, 'conclusion'],
      'global package theorem conclusion must exactly match its theorem coordinate',
      { expected: expectedConclusion, actual: node.conclusion },
    );
  }
  if (!sameCanonical0(node.payload, {})) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', nodeId, 'payload'],
      'global package theorem node rejects caller-supplied truth or readiness payload fields',
      { actual: node.payload },
    );
  }
  if (!isPlainObject0(node.bounds)
      || node.bounds.polynomial !== true
      || !Number.isInteger(node.bounds.exponent)
      || node.bounds.exponent <= 0
      || !Number.isInteger(globalBoundsExponent)
      || node.bounds.exponent > globalBoundsExponent) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', nodeId, 'bounds'],
      'global package theorem node must carry a positive polynomial bound inside the global envelope',
      { globalBoundsExponent, actual: node.bounds },
    );
  }
  return validationAccept0({
    kind: 'GlobalPackageNodeContract0NF',
    nodeId,
    theorem: requirement.theorem,
    exponent: node.bounds.exponent,
  });
}

function validateLocalPackageAndRowBinding0({
  requirement,
  localPackage,
  row,
  rowDerivation,
  packageByFamily,
}) {
  if (!isPlainObject0(localPackage)) {
    return validationReject0(
      ['LocalPackages', 'Packages', requirement.family],
      'global package refinement is missing its local package record',
      { family: requirement.family },
    );
  }
  const expectedIdentity = {
    family: requirement.family,
    packageId: requirement.packageId,
    batchId: requirement.batchId,
    schemaId: requirement.schemaId,
    kindKey: requirement.kindKey,
    arityKey: requirement.arityKey,
    payloadKey: requirement.payloadKey,
    theorem: requirement.theorem,
  };
  for (const [field, expected] of Object.entries(expectedIdentity)) {
    if (localPackage[field] !== expected) {
      return validationReject0(
        ['LocalPackages', 'Packages', requirement.family, field],
        'local package identity must exactly match the global package requirement',
        { field, expected, actual: localPackage[field] },
      );
    }
  }
  if (!Array.isArray(localPackage.rowRefs)
      || localPackage.rowRefs.length !== 1) {
    return validationReject0(
      ['LocalPackages', 'Packages', requirement.family, 'rowRefs'],
      'global package refinement requires exactly one local row reference',
      { actual: localPackage.rowRefs },
    );
  }
  const expectedRowRef = {
    batchId: requirement.batchId,
    family: requirement.family,
    packageId: requirement.packageId,
    schemaId: requirement.schemaId,
    kindKey: requirement.kindKey,
  };
  if (!sameCanonical0(localPackage.rowRefs[0], expectedRowRef)) {
    return validationReject0(
      ['LocalPackages', 'Packages', requirement.family, 'rowRefs', 0],
      'local package row reference must exactly match the required row family',
      { expected: expectedRowRef, actual: localPackage.rowRefs[0] },
    );
  }
  if (!isPlainObject0(row)) {
    return validationReject0(
      ['RowPack', 'Rows', requirement.family],
      'global package refinement is missing the referenced executable row',
      { family: requirement.family },
    );
  }
  for (const [field, expected] of Object.entries({
    BatchID: requirement.batchId,
    FamilyID: requirement.family,
    PackageID: requirement.packageId,
    SchemaID: requirement.schemaId,
    KindKey: requirement.kindKey,
  })) {
    if (row[field] !== expected) {
      return validationReject0(
        ['RowPack', 'Rows', requirement.family, field],
        'referenced executable row does not match the local package requirement',
        { field, expected, actual: row[field] },
      );
    }
  }
  if (!isPlainObject0(rowDerivation)) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'globalRowDerivationDigests', requirement.family],
      'global package refinement is missing the semantic row derivation binding',
      { family: requirement.family },
    );
  }
  const rowDigest = digestCanonical0(row);
  if (!sameCanonical0(
    rowDerivation.executableRecordDigest,
    rowDigest,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'globalRowDerivationDigests', requirement.family, 'executableRecordDigest'],
      'semantic row derivation digest does not match the referenced executable row',
      {
        family: requirement.family,
        expected: rowDigest,
        actual: rowDerivation.executableRecordDigest,
      },
    );
  }
  if (!Array.isArray(localPackage.imports)) {
    return validationReject0(
      ['LocalPackages', 'Packages', requirement.family, 'imports'],
      'local package imports must be an array',
      { actual: typeof localPackage.imports },
    );
  }
  for (let index = 0; index < localPackage.imports.length; index += 1) {
    const importedFamily = localPackage.imports[index];
    if (!packageByFamily.has(importedFamily)) {
      return validationReject0(
        ['LocalPackages', 'Packages', requirement.family, 'imports', index],
        'local package import must resolve to a checked local package',
        { family: requirement.family, importedFamily },
      );
    }
  }
  return validationAccept0({
    kind: 'GlobalPackageLocalRowBinding0NF',
    family: requirement.family,
    rowDigest,
    rowDerivationDigest: rowDerivation.digest,
    importCount: localPackage.imports.length,
  });
}

function expectedPackagePremises0(theorem) {
  const base = [
    'Bounds.Polynomial',
    'NoMin.Global',
    'Mode.Firewall',
    'Import.Acyclic',
  ];
  if (theorem === 'G.LockedNANDThreshold') {
    return [...base, 'G.ThresholdCert.proof'];
  }
  return base;
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0([], 'global package semantic input must be an object', {
      actual: typeof input,
    });
  }
  if (input.kind !== 'GlobalPackageSemanticInput0') {
    return validationReject0(
      ['kind'],
      'global package semantic input kind must be GlobalPackageSemanticInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `global package semantic input version must be ${CHECKER_VERSION}`,
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
    'SemanticPackages',
    'Scope',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'global package semantic input is missing a required field',
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
    'SemanticPackages',
  ]) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'global package semantic dependency surface must be an object',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'global package semantic input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!Array.isArray(input.LegacyGlobalProofDAG.Nodes)
      || !Array.isArray(input.RowPack.Rows)
      || !Array.isArray(input.LocalPackages.Packages)) {
    return validationReject0(
      ['input'],
      'global package semantic input requires Nodes, Rows, and Packages arrays',
    );
  }
  if (!sameCanonical0(input.Scope, GLOBAL_PACKAGE_SEMANTIC_SCOPE0)) {
    return validationReject0(
      ['Scope'],
      'global package semantic scope must match the bounded executable refinement scope',
      { expected: GLOBAL_PACKAGE_SEMANTIC_SCOPE0, actual: input.Scope },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_PACKAGE_SEMANTIC_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'global package semantic policy must match the fail-closed policy',
      { expected: GLOBAL_PACKAGE_SEMANTIC_POLICY0, actual: input.Policy },
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
    'SemanticPackages',
    'Scope',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'global package semantic checker rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalPackageSemanticInputShape0NF',
  });
}

function validateSemanticSuite0(suite, dag, localPackages) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SemanticPackages'],
      'global package semantic suite must be an object',
      { actual: typeof suite },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'suiteId',
    'refinements',
    'supportingPackages',
    'Scope',
    'Policy',
  ]);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['SemanticPackages', unexpected[0]],
      'global package semantic suite rejects caller-supplied truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (suite.kind !== 'GlobalPackageSemanticSuite0'
      || suite.version !== CHECKER_VERSION
      || typeof suite.suiteId !== 'string'
      || suite.suiteId.length === 0) {
    return validationReject0(
      ['SemanticPackages'],
      'global package semantic suite kind, version, or suiteId is invalid',
      { actual: suite },
    );
  }
  if (!Array.isArray(suite.refinements)
      || suite.refinements.length
        !== GLOBAL_PACKAGE_SEMANTIC_REQUIREMENTS0.length) {
    return validationReject0(
      ['SemanticPackages', 'refinements'],
      'global package semantic suite must provide one refinement per global package theorem',
      {
        expected: GLOBAL_PACKAGE_SEMANTIC_REQUIREMENTS0.length,
        actual: suite.refinements?.length,
      },
    );
  }
  if (!Array.isArray(suite.supportingPackages)
      || suite.supportingPackages.length
        !== GLOBAL_SUPPORTING_LOCAL_PACKAGE_FAMILIES0.length) {
    return validationReject0(
      ['SemanticPackages', 'supportingPackages'],
      'global package semantic suite supporting-package coverage mismatch',
      {
        expected: GLOBAL_SUPPORTING_LOCAL_PACKAGE_FAMILIES0.length,
        actual: suite.supportingPackages?.length,
      },
    );
  }
  if (!sameCanonical0(suite.Scope, GLOBAL_PACKAGE_SEMANTIC_SCOPE0)
      || !sameCanonical0(suite.Policy, GLOBAL_PACKAGE_SEMANTIC_POLICY0)) {
    return validationReject0(
      ['SemanticPackages', 'Scope'],
      'global package semantic suite scope or policy mismatch',
      { actualScope: suite.Scope, actualPolicy: suite.Policy },
    );
  }
  const expected = makeGlobalPackageSemanticSuite0({
    LegacyGlobalProofDAG: dag,
    LocalPackages: localPackages,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['SemanticPackages'],
      'global package semantic suite must exactly match the computed global-node and local-package bindings',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'GlobalPackageSemanticSuite0NF',
    suiteId: suite.suiteId,
    refinementCount: suite.refinements.length,
    supportingPackageCount: suite.supportingPackages.length,
    theoremCoverage: [...GLOBAL_DAG_REQUIRED_PACKAGE_THEOREMS0],
    bindingDigests: suite.refinements.map((entry) => entry.bindingDigest),
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
    kBundleFinalReady: true,
    semanticK0ConformanceReady: true,
    semanticSigmaReady: true,
    semanticReflectionReady: true,
    globalInfrastructureSemanticReady: true,
    globalRowSemanticReady: true,
    globalRowDerivationsReady: true,
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['PredecessorGlobal', 'NF', field],
        'semantic row predecessor boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  const overlay = nf.semanticOverlay;
  if (!isPlainObject0(overlay)
      || overlay.globalRowDerivationsReady !== true
      || overlay.globalPackageDerivationsReady !== false
      || overlay.globalFinalDerivationsReady !== false) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay'],
      'semantic row predecessor readiness decomposition mismatch',
      { actual: overlay },
    );
  }
  if (!sameCanonical0(
    overlay.semanticRowNodeIds,
    GLOBAL_SEMANTIC_ROW_NODE_IDS0,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'semanticRowNodeIds'],
      'semantic row predecessor node coverage mismatch',
      { expected: GLOBAL_SEMANTIC_ROW_NODE_IDS0, actual: overlay.semanticRowNodeIds },
    );
  }
  if (!sameCanonical0(
    overlay.blockedPackageNodeIds,
    GLOBAL_PACKAGE_NODE_IDS0,
  )) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'semanticOverlay', 'blockedPackageNodeIds'],
      'semantic row predecessor package blocker set mismatch',
      { expected: GLOBAL_PACKAGE_NODE_IDS0, actual: overlay.blockedPackageNodeIds },
    );
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0) {
    return validationReject0(
      ['PredecessorGlobal', 'NF', 'activeFinalNodeIds'],
      'semantic row predecessor must expose no active final node',
      { actual: nf.activeFinalNodeIds },
    );
  }
  return validationAccept0({
    kind: 'GlobalPackageSemanticPredecessorBoundary0NF',
    ...expected,
    blockedPackageNodeIds: [...GLOBAL_PACKAGE_NODE_IDS0],
    activeFinalNodeIds: [],
  });
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

function safeCoord0(value) {
  return String(value).replace(/[^A-Za-z0-9_.-]/g, '_');
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

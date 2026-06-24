import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  GLOBAL_DAG_REQUIRED_FINALS0,
} from './pcc-global-proof-dag0.mjs';

import {
  CheckGlobalProofDAGPackageSuccessor0,
  makeGlobalProofDAGPackageSuccessor0,
} from './pcc-global-proof-dag-package-successor0.mjs';

import {
  CheckPackSufficiency0,
} from './pcc-pack-sufficiency0.mjs';

import {
  GLOBAL_FINAL_PREFIX_NODE_IDS0,
  GLOBAL_FINAL_REMAINING_NODE_IDS0,
  GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0,
  GLOBAL_FINAL_PREFIX_SEMANTIC_POLICY0,
  PACK_PACKAGE_NODE_ID0,
  makeGlobalFinalPrefixSemanticSuite0,
  makeGlobalFinalPrefixSemanticInput0,
  makeGlobalFinalPrefixPCCPack0,
} from './pcc-global-final-prefix-contract0.mjs';

import {
  checkGeneratedPackageSufficiencyRefinement0,
  checkPackageSoundnessRefinement0,
} from './pcc-global-final-prefix-derive0.mjs';

const CHECKER_VERSION = 0;

export {
  GLOBAL_FINAL_PREFIX_NODE_IDS0,
  GLOBAL_FINAL_REMAINING_NODE_IDS0,
  GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0,
  GLOBAL_FINAL_PREFIX_SEMANTIC_POLICY0,
  makeGlobalFinalPrefixSemanticSuite0,
  makeGlobalFinalPrefixSemanticInput0,
  makeGlobalFinalPrefixPCCPack0,
};

export async function CheckGlobalFinalPrefixSemantic0(input) {
  const checker = 'CheckGlobalFinalPrefixSemantic0';
  const ledger = [];

  const shape = validateInputShape0(input);
  ledger.push(makeLedgerEntry0('shape', shape.ok, shape.nf ?? shape.witness));
  if (!shape.ok) {
    return makeRejectFromValidation0(checker, `${checker}.input`, shape, ledger);
  }

  const predecessorCall = await callChecker0(
    'CheckGlobalProofDAGPackageSuccessor0',
    () => CheckGlobalProofDAGPackageSuccessor0(
      makeGlobalProofDAGPackageSuccessor0({
        KBundle: input.KBundle,
        LegacyGlobalProofDAG: input.LegacyGlobalProofDAG,
        InfrastructureSemanticDerivations:
          input.InfrastructureSemanticDerivations,
        RowPack: input.RowPack,
        RowFamG: input.RowFamG,
        RowSemanticDerivations: input.RowSemanticDerivations,
        LocalPackages: input.LocalPackages,
        PackageSemanticDerivations: input.PackageSemanticDerivations,
        Purpose: 'development',
      }),
    ),
  );
  ledger.push(makeLedgerEntry0(
    'CheckGlobalProofDAGPackageSuccessor0',
    predecessorCall.ok && predecessorCall.record.tag === 'accept',
    predecessorCall.ok ? predecessorCall.record : predecessorCall.witness,
  ));
  if (!predecessorCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticPackagePredecessor.exception`,
      path: ['PackageSemanticDerivations'],
      witness: predecessorCall.witness,
      ledger,
    });
  }
  if (predecessorCall.record.tag !== 'accept') {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.semanticPackagePredecessor`,
      path: ['PackageSemanticDerivations'],
      witness: {
        reason: 'final-prefix refinements require an accepted semantic package predecessor',
        inner: compactRecord0(predecessorCall.record),
      },
      ledger,
    });
  }
  const predecessorNF =
    predecessorCall.record.NF ?? predecessorCall.record.nf ?? {};
  const predecessorBoundary = validatePredecessorBoundary0(predecessorNF);
  ledger.push(makeLedgerEntry0(
    'semanticPackagePredecessorBoundary',
    predecessorBoundary.ok,
    predecessorBoundary.nf ?? predecessorBoundary.witness,
  ));
  if (!predecessorBoundary.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticPackagePredecessorBoundary`,
      predecessorBoundary,
      ledger,
    );
  }

  const packCall = await callChecker0(
    'CheckPackSufficiency0',
    () => CheckPackSufficiency0(input.PCCPack),
  );
  ledger.push(makeLedgerEntry0(
    'CheckPackSufficiency0',
    packCall.ok && isPackSufficiencyAccept0(packCall.record),
    packCall.ok ? packCall.record : packCall.witness,
  ));
  if (!packCall.ok) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.packSufficiency.exception`,
      path: ['PCCPack'],
      witness: packCall.witness,
      ledger,
    });
  }
  if (!isPackSufficiencyAccept0(packCall.record)) {
    return makeRejectRecord0({
      checker,
      coord: `${checker}.packSufficiency`,
      path: ['PCCPack'],
      witness: {
        reason: 'final-prefix refinements require an accepted version-zero pack-sufficiency record',
        inner: compactRecord0(packCall.record),
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
    input.SemanticFinalPrefix,
    input.LegacyGlobalProofDAG,
    input.PCCPack,
  );
  ledger.push(makeLedgerEntry0(
    'semanticFinalPrefixSuite',
    suite.ok,
    suite.nf ?? suite.witness,
  ));
  if (!suite.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.semanticFinalPrefixSuite`,
      suite,
      ledger,
    );
  }

  const nodeById = new Map(
    input.LegacyGlobalProofDAG.Nodes.map((node) => [node.id, node]),
  );
  const packageRefinementByNodeId = new Map(
    (predecessorNF.globalPackageRefinementDigests ?? []).map((entry) => [
      entry.nodeId,
      entry,
    ]),
  );

  const packageSoundness = await checkPackageSoundnessRefinement0({
    node: nodeById.get('Final.PackageSoundness'),
    dependencyNode: nodeById.get(PACK_PACKAGE_NODE_ID0),
    dependencyRefinement: packageRefinementByNodeId.get(PACK_PACKAGE_NODE_ID0),
    binding: input.SemanticFinalPrefix.refinements[0],
    pack: input.PCCPack,
    positiveRecord: packCall.record,
    globalBoundsExponent: input.LegacyGlobalProofDAG.BoundsLedger?.exponent,
  });
  ledger.push(makeLedgerEntry0(
    'finalPrefix.Final.PackageSoundness',
    packageSoundness.ok,
    packageSoundness.nf ?? packageSoundness.witness,
  ));
  if (!packageSoundness.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.finalPrefix.Final.PackageSoundness`,
      packageSoundness,
      ledger,
    );
  }

  const generatedSufficiency =
    await checkGeneratedPackageSufficiencyRefinement0({
      node: nodeById.get('Final.GeneratedPackageSufficiency'),
      dependencyNode: nodeById.get('Final.PackageSoundness'),
      dependencyDerivation: packageSoundness.nf,
      binding: input.SemanticFinalPrefix.refinements[1],
      pack: input.PCCPack,
      positiveRecord: packCall.record,
      globalBoundsExponent: input.LegacyGlobalProofDAG.BoundsLedger?.exponent,
    });
  ledger.push(makeLedgerEntry0(
    'finalPrefix.Final.GeneratedPackageSufficiency',
    generatedSufficiency.ok,
    generatedSufficiency.nf ?? generatedSufficiency.witness,
  ));
  if (!generatedSufficiency.ok) {
    return makeRejectFromValidation0(
      checker,
      `${checker}.finalPrefix.Final.GeneratedPackageSufficiency`,
      generatedSufficiency,
      ledger,
    );
  }

  const refinements = [packageSoundness.nf, generatedSufficiency.nf];
  const packNF = packCall.record.NF ?? packCall.record.nf ?? {};
  return makeAcceptRecord0({
    checker,
    nf: {
      kind: 'GlobalFinalPrefixSemantic0NF',
      checker,
      version: CHECKER_VERSION,
      globalFinalPrefixSemanticReady: true,
      globalFinalPrefixRefinementsReady: true,
      globalPackageSoundnessNodeRefinementReady: true,
      globalGeneratedPackageSufficiencyNodeRefinementReady: true,

      semanticPackagePredecessorAccepted: true,
      semanticPackagePredecessorChecker: predecessorCall.record.checker,
      semanticPackagePredecessorDigest:
        predecessorCall.record.Digest ?? predecessorCall.record.digest,
      globalPackageDerivationsReady:
        predecessorNF.globalPackageDerivationsReady === true,
      globalRowDerivationsReady:
        predecessorNF.globalRowDerivationsReady === true,
      globalInfrastructureSemanticReady:
        predecessorNF.globalInfrastructureSemanticReady === true,
      semanticKBundleFinalReady:
        predecessorNF.semanticKBundleFinalReady === true,

      packSufficiencyAccepted: true,
      packSufficiencyChecker: packCall.record.checker,
      packSufficiencyDigest: packCall.record.Digest ?? packCall.record.digest,
      packSufficiencyNFKind: packNF.kind,
      packObjectDigest: digestCanonical0(input.PCCPack),
      packCoreDigest: digestCanonical0(input.PCCPack.Core),
      packManifestDigest: digestCanonical0(input.PCCPack.Manifest),
      packSufficiencyTheoremDigest:
        digestCanonical0(input.PCCPack.PackSufficiencyTheorem),

      globalFinalPrefixNodeIds: [...GLOBAL_FINAL_PREFIX_NODE_IDS0],
      globalFinalRemainingNodeIds: [...GLOBAL_FINAL_REMAINING_NODE_IDS0],
      globalFinalPrefixRefinementCount: refinements.length,
      finalPrefixRefinements: refinements,
      finalPrefixRefinementDigests: refinements.map((entry) => ({
        nodeId: entry.nodeId,
        digest: entry.refinementDigest,
        globalNodeDigest: entry.globalNodeDigest,
        dependencyNodeDigest: entry.dependencyNodeDigest,
        sourceRecordDigest: entry.sourceRecordDigest,
        positiveRecordDigest: entry.positiveRecordDigest,
        negativeRecordDigest: entry.negativeRecordDigest,
        checkerContractDigest: entry.checkerContractDigest,
        conclusionDigest: entry.conclusionDigest,
      })),

      Scope: { ...GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0 },
      scopeDigest: digestCanonical0(input.Scope),
      boundedExecutableFinalPrefixRefinementsOnly: true,
      unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
      packAcceptanceDoesNotActivatePublicConclusion: true,
      satReductionSoundnessNotClaimed: true,
      complexityClassImplicationNotClaimed: true,
      publicTheoremEmissionAllowed: false,

      globalFinalSATReductionDerivationReady: false,
      globalFinalComplexityImplicationReady: false,
      globalFinalDerivationsReady: false,
      globalSemanticNodeDerivationsReady: false,
      remainingFinalImplicationsRemainSeparate: true,
      callerReadinessAssertionsForbidden: true,
      policyDigest: digestCanonical0(input.Policy),
    },
    ledger,
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
        'final-prefix PCCPack surface must exactly align with the semantic package predecessor inputs',
        {
          surface: name,
          expectedDigest: digestCanonical0(expected ?? null),
          actualDigest: digestCanonical0(actual ?? null),
        },
      );
    }
  }
  return validationAccept0({
    kind: 'GlobalFinalPrefixPackAlignment0NF',
    alignedSurfaces: checks.map(([name]) => name),
  });
}

function validateInputShape0(input) {
  if (!isPlainObject0(input)) {
    return validationReject0(
      [],
      'global final-prefix semantic input must be an object',
      { actual: typeof input },
    );
  }
  if (input.kind !== 'GlobalFinalPrefixSemanticInput0') {
    return validationReject0(
      ['kind'],
      'global final-prefix semantic input kind must be GlobalFinalPrefixSemanticInput0',
      { actual: input.kind },
    );
  }
  if (input.version !== CHECKER_VERSION) {
    return validationReject0(
      ['version'],
      `global final-prefix semantic input version must be ${CHECKER_VERSION}`,
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
    'SemanticFinalPrefix',
    'Scope',
    'Policy',
  ]) {
    if (!Object.prototype.hasOwnProperty.call(input, field)) {
      return validationReject0(
        [field],
        'global final-prefix semantic input is missing a required field',
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
    'SemanticFinalPrefix',
  ]) {
    if (!isPlainObject0(input[field])) {
      return validationReject0(
        [field],
        'global final-prefix semantic dependency surface must be an object',
        { field, actual: typeof input[field] },
      );
    }
  }
  if (input.KBundle.Purpose !== 'development') {
    return validationReject0(
      ['KBundle', 'Purpose'],
      'global final-prefix semantic input KBundle must remain development-purpose',
      { actual: input.KBundle.Purpose },
    );
  }
  if (!Array.isArray(input.LegacyGlobalProofDAG.Nodes)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes'],
      'global final-prefix semantic input requires a global Nodes array',
    );
  }
  if (!sameCanonical0(input.Scope, GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0)) {
    return validationReject0(
      ['Scope'],
      'global final-prefix semantic scope must match the bounded fail-closed scope',
      { expected: GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0, actual: input.Scope },
    );
  }
  if (!sameCanonical0(input.Policy, GLOBAL_FINAL_PREFIX_SEMANTIC_POLICY0)) {
    return validationReject0(
      ['Policy'],
      'global final-prefix semantic policy must match the fail-closed policy',
      { expected: GLOBAL_FINAL_PREFIX_SEMANTIC_POLICY0, actual: input.Policy },
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
    'SemanticFinalPrefix',
    'Scope',
    'Policy',
  ]);
  const unexpected = Object.keys(input).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      [unexpected[0]],
      'global final-prefix semantic checker rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalPrefixSemanticInputShape0NF',
  });
}

function validateSemanticSuite0(suite, dag, pack) {
  if (!isPlainObject0(suite)) {
    return validationReject0(
      ['SemanticFinalPrefix'],
      'global final-prefix semantic suite must be an object',
      { actual: typeof suite },
    );
  }
  const allowed = new Set([
    'kind',
    'version',
    'suiteId',
    'refinements',
    'Scope',
    'Policy',
  ]);
  const unexpected = Object.keys(suite).filter((key) => !allowed.has(key));
  if (unexpected.length !== 0) {
    return validationReject0(
      ['SemanticFinalPrefix', unexpected[0]],
      'global final-prefix semantic suite rejects caller-supplied readiness or truth assertions',
      { unexpectedFields: unexpected.sort() },
    );
  }
  if (suite.kind !== 'GlobalFinalPrefixSemanticSuite0'
      || suite.version !== CHECKER_VERSION
      || typeof suite.suiteId !== 'string'
      || suite.suiteId.length === 0
      || !Array.isArray(suite.refinements)
      || suite.refinements.length !== GLOBAL_FINAL_PREFIX_NODE_IDS0.length) {
    return validationReject0(
      ['SemanticFinalPrefix'],
      'global final-prefix semantic suite shape or refinement count mismatch',
      {
        expectedCount: GLOBAL_FINAL_PREFIX_NODE_IDS0.length,
        actual: suite,
      },
    );
  }
  if (!sameCanonical0(suite.Scope, GLOBAL_FINAL_PREFIX_SEMANTIC_SCOPE0)
      || !sameCanonical0(suite.Policy, GLOBAL_FINAL_PREFIX_SEMANTIC_POLICY0)) {
    return validationReject0(
      ['SemanticFinalPrefix'],
      'global final-prefix semantic suite scope or policy mismatch',
      { actualScope: suite.Scope, actualPolicy: suite.Policy },
    );
  }
  const expected = makeGlobalFinalPrefixSemanticSuite0({
    LegacyGlobalProofDAG: dag,
    PCCPack: pack,
  });
  if (!sameCanonical0(suite, expected)) {
    return validationReject0(
      ['SemanticFinalPrefix'],
      'global final-prefix semantic suite must exactly match the computed final-node, dependency, pack, and checker bindings',
      { expected, actual: suite },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalPrefixSemanticSuite0NF',
    suiteId: suite.suiteId,
    refinementCount: suite.refinements.length,
    nodeIds: [...GLOBAL_FINAL_PREFIX_NODE_IDS0],
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
    globalPackageSemanticReady: true,
    globalPackageDerivationsReady: true,
    globalRowDerivationsReady: true,
    globalInfrastructureSemanticReady: true,
    legacyFinalNodesQuarantined: true,
  };
  for (const [field, value] of Object.entries(expected)) {
    if (nf[field] !== value) {
      return validationReject0(
        ['SemanticPackagePredecessor', 'NF', field],
        'semantic package predecessor boundary mismatch',
        { field, expected: value, actual: nf[field] },
      );
    }
  }
  if (!Array.isArray(nf.activeFinalNodeIds)
      || nf.activeFinalNodeIds.length !== 0
      || !sameCanonical0(
        nf.semanticOverlay?.blockedFinalNodeIds,
        GLOBAL_DAG_REQUIRED_FINALS0,
      )
      || nf.semanticOverlay?.globalFinalDerivationsReady !== false) {
    return validationReject0(
      ['SemanticPackagePredecessor', 'NF', 'semanticOverlay'],
      'semantic package predecessor must keep every final node blocked and expose no active final node',
      {
        activeFinalNodeIds: nf.activeFinalNodeIds,
        blockedFinalNodeIds: nf.semanticOverlay?.blockedFinalNodeIds,
        globalFinalDerivationsReady:
          nf.semanticOverlay?.globalFinalDerivationsReady,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalPrefixPackagePredecessorBoundary0NF',
    ...expected,
    blockedFinalNodeIds: [...GLOBAL_DAG_REQUIRED_FINALS0],
    activeFinalNodeIds: [],
  });
}

function isPackSufficiencyAccept0(record) {
  const nf = record?.NF ?? record?.nf;
  return record?.tag === 'accept'
    && record?.checker === 'CheckPackSufficiency0'
    && nf?.kind === 'PackSufficiency0NF'
    && nf?.packageKind === 'PCCPack0';
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

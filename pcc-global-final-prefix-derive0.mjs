import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckPackSufficiency0,
} from './pcc-pack-sufficiency0.mjs';

import {
  GLOBAL_FINAL_PREFIX_CONTRACTS0,
  PACK_PACKAGE_NODE_ID0,
  makeFinalPrefixBinding0,
} from './pcc-global-final-prefix-contract0.mjs';

const CHECKER_VERSION = 0;

export async function checkPackageSoundnessRefinement0({
  node,
  dependencyNode,
  dependencyRefinement,
  binding,
  pack,
  positiveRecord,
  globalBoundsExponent,
}) {
  const nodeId = 'Final.PackageSoundness';
  const contract = GLOBAL_FINAL_PREFIX_CONTRACTS0[nodeId];
  const nodeValidation = validateFinalPrefixNode0({
    node,
    contract,
    globalBoundsExponent,
  });
  if (!nodeValidation.ok) return nodeValidation;

  if (!isPlainObject0(dependencyNode)
      || dependencyNode.id !== PACK_PACKAGE_NODE_ID0
      || dependencyNode.nodeKind !== 'package'
      || dependencyNode.conclusion?.tag !== 'PackageTheoremAccepted0'
      || dependencyNode.conclusion?.theorem !== 'PACK.PackageSufficiency') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', PACK_PACKAGE_NODE_ID0],
      'Final.PackageSoundness requires the exact semantic PACK package predecessor',
      { actual: dependencyNode },
    );
  }
  if (!isPlainObject0(dependencyRefinement)
      || dependencyRefinement.nodeId !== PACK_PACKAGE_NODE_ID0
      || !isDigest0(dependencyRefinement.digest)) {
    return validationReject0(
      ['SemanticPackagePredecessor', 'globalPackageRefinementDigests', PACK_PACKAGE_NODE_ID0],
      'Final.PackageSoundness requires the accepted PACK package refinement digest',
      { actual: dependencyRefinement },
    );
  }

  const source = pack.PackSufficiencyTheorem?.packageSufficiency;
  const sourceValidation = validatePackageSufficiencySource0(source);
  if (!sourceValidation.ok) return sourceValidation;

  const expectedBinding = makeFinalPrefixBinding0({
    index: 0,
    nodeId,
    node,
    dependencyNode,
    PCCPack: pack,
  });
  if (!sameCanonical0(binding, expectedBinding)) {
    return validationReject0(
      ['SemanticFinalPrefix', 'refinements', 0],
      'Final.PackageSoundness binding must exactly match the global node, PACK dependency, pack theorem surface, and executable contract',
      { expected: expectedBinding, actual: binding },
    );
  }

  const negativeProbe = await runPackNegativeProbe0({
    pack,
    probeName: nodeId,
    mutate: (value) => ({
      ...value,
      PackSufficiencyTheorem: {
        ...value.PackSufficiencyTheorem,
        packageSufficiency: {
          ...value.PackSufficiencyTheorem.packageSufficiency,
          acceptedPackageValid: false,
        },
      },
    }),
    expectedPath: contract.negativePath,
  });
  if (!negativeProbe.ok) return negativeProbe;

  const conclusion = Object.freeze({
    kind: 'GlobalFinalPrefixRefinementConclusion0',
    version: CHECKER_VERSION,
    nodeId,
    packageDependency: PACK_PACKAGE_NODE_ID0,
    packSufficiencyCheckerAccepted: true,
    packageSufficiencySourceContractChecked: true,
    negativePackageValidityProbeRejected: true,
    boundedExecutableFinalPrefixRefinement: true,
    unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
  });
  const nf = {
    kind: 'GlobalFinalPrefixRefinement0NF',
    version: CHECKER_VERSION,
    index: 0,
    nodeId,
    refinementClass: 'package-soundness-executable-boundary',
    globalNodeDigest: expectedBinding.globalNodeDigest,
    dependencyNodeId: PACK_PACKAGE_NODE_ID0,
    dependencyNodeDigest: expectedBinding.dependencyNodeDigest,
    dependencyRefinementDigest: dependencyRefinement.digest,
    sourceRecordDigest: expectedBinding.sourceRecordDigest,
    packCoreDigest: expectedBinding.packCoreDigest,
    packManifestDigest: expectedBinding.packManifestDigest,
    packTheoremDigest: expectedBinding.packTheoremDigest,
    checkerContractDigest: expectedBinding.checkerContractDigest,
    bindingDigest: expectedBinding.bindingDigest,
    positiveRecordDigest:
      positiveRecord.Digest ?? positiveRecord.digest,
    negativeCoord: negativeProbe.nf.coord,
    negativePath: negativeProbe.nf.path,
    negativeRecordDigest: negativeProbe.nf.recordDigest,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    boundedExecutableFinalPrefixRefinement: true,
    unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
    ready: true,
  };
  return validationAccept0({
    ...nf,
    refinementDigest: digestCanonical0(nf),
  });
}

export async function checkGeneratedPackageSufficiencyRefinement0({
  node,
  dependencyNode,
  dependencyDerivation,
  binding,
  pack,
  positiveRecord,
  globalBoundsExponent,
}) {
  const nodeId = 'Final.GeneratedPackageSufficiency';
  const contract = GLOBAL_FINAL_PREFIX_CONTRACTS0[nodeId];
  const nodeValidation = validateFinalPrefixNode0({
    node,
    contract,
    globalBoundsExponent,
  });
  if (!nodeValidation.ok) return nodeValidation;

  if (!isPlainObject0(dependencyNode)
      || dependencyNode.id !== 'Final.PackageSoundness'
      || dependencyNode.nodeKind !== 'final') {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', 'Final.PackageSoundness'],
      'Final.GeneratedPackageSufficiency requires the exact Final.PackageSoundness predecessor',
      { actual: dependencyNode },
    );
  }
  if (!isPlainObject0(dependencyDerivation)
      || dependencyDerivation.nodeId !== 'Final.PackageSoundness'
      || dependencyDerivation.ready !== true
      || !isDigest0(dependencyDerivation.refinementDigest)) {
    return validationReject0(
      ['FinalPrefixDerivations', 'Final.PackageSoundness'],
      'Final.GeneratedPackageSufficiency requires the checked package-soundness prefix refinement',
      { actual: dependencyDerivation },
    );
  }

  const source = pack.PackSufficiencyTheorem?.generatedPackageSufficiency;
  const sourceValidation = validateGeneratedSufficiencySource0(source);
  if (!sourceValidation.ok) return sourceValidation;
  const coreValidation = validateGeneratedCoreBoundary0(pack.Core);
  if (!coreValidation.ok) return coreValidation;

  const expectedBinding = makeFinalPrefixBinding0({
    index: 1,
    nodeId,
    node,
    dependencyNode,
    PCCPack: pack,
  });
  if (!sameCanonical0(binding, expectedBinding)) {
    return validationReject0(
      ['SemanticFinalPrefix', 'refinements', 1],
      'Final.GeneratedPackageSufficiency binding must exactly match the global node, package-soundness dependency, generated-package record, core boundary, and executable contract',
      { expected: expectedBinding, actual: binding },
    );
  }

  const negativeProbe = await runPackNegativeProbe0({
    pack,
    probeName: nodeId,
    mutate: (value) => ({
      ...value,
      PackSufficiencyTheorem: {
        ...value.PackSufficiencyTheorem,
        generatedPackageSufficiency: {
          ...value.PackSufficiencyTheorem.generatedPackageSufficiency,
          canonicalByteEquality: false,
        },
      },
    }),
    expectedPath: contract.negativePath,
  });
  if (!negativeProbe.ok) return negativeProbe;

  const conclusion = Object.freeze({
    kind: 'GlobalFinalPrefixRefinementConclusion0',
    version: CHECKER_VERSION,
    nodeId,
    predecessorFinalNode: 'Final.PackageSoundness',
    generatedPackageBoundaryContractChecked: true,
    canonicalByteEqualityMetadataChecked: true,
    coreExcludesAcceptRunChecked: true,
    negativeCanonicalByteProbeRejected: true,
    boundedExecutableFinalPrefixRefinement: true,
    unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
  });
  const nf = {
    kind: 'GlobalFinalPrefixRefinement0NF',
    version: CHECKER_VERSION,
    index: 1,
    nodeId,
    refinementClass: 'generated-package-executable-boundary',
    globalNodeDigest: expectedBinding.globalNodeDigest,
    dependencyNodeId: 'Final.PackageSoundness',
    dependencyNodeDigest: expectedBinding.dependencyNodeDigest,
    dependencyRefinementDigest: dependencyDerivation.refinementDigest,
    sourceRecordDigest: expectedBinding.sourceRecordDigest,
    packCoreDigest: expectedBinding.packCoreDigest,
    packManifestDigest: expectedBinding.packManifestDigest,
    packTheoremDigest: expectedBinding.packTheoremDigest,
    canonicalBytesDigest: expectedBinding.canonicalBytesDigest,
    checkerContractDigest: expectedBinding.checkerContractDigest,
    bindingDigest: expectedBinding.bindingDigest,
    positiveRecordDigest:
      positiveRecord.Digest ?? positiveRecord.digest,
    negativeCoord: negativeProbe.nf.coord,
    negativePath: negativeProbe.nf.path,
    negativeRecordDigest: negativeProbe.nf.recordDigest,
    conclusion,
    conclusionDigest: digestCanonical0(conclusion),
    boundedExecutableFinalPrefixRefinement: true,
    unrestrictedFinalPrefixTheoremSoundnessNotClaimed: true,
    ready: true,
  };
  return validationAccept0({
    ...nf,
    refinementDigest: digestCanonical0(nf),
  });
}

function validateFinalPrefixNode0({ node, contract, globalBoundsExponent }) {
  if (!isPlainObject0(node)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'final-prefix coordinate is missing its global node',
      { nodeId: contract.nodeId },
    );
  }
  if (node.id !== contract.nodeId
      || node.nodeKind !== contract.nodeKind
      || node.label !== contract.label) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId],
      'final-prefix global node identity, kind, or label mismatch',
      { contract, actual: node },
    );
  }
  if (!sameCanonical0(node.premises, contract.premises)) {
    return validationReject0(
      ['LegacyGlobalProofDAG', 'Nodes', contract.nodeId, 'premises'],
      'final-prefix global node premise list must exactly match its contract',
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
      'final-prefix global node must retain empty imports/payload, Full mode, and null route/rank',
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
      'final-prefix global node conclusion must exactly match its theorem coordinate',
      {
        expected: {
          tag: contract.conclusionTag,
          theorem: contract.theorem,
        },
        actual: node.conclusion,
      },
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
      'final-prefix global node must carry a positive polynomial bound inside the global envelope',
      { globalBoundsExponent, actual: node.bounds },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalPrefixNodeContract0NF',
    nodeId: contract.nodeId,
    exponent: node.bounds.exponent,
  });
}

function validatePackageSufficiencySource0(source) {
  if (!isPlainObject0(source)) {
    return validationReject0(
      ['PCCPack', 'PackSufficiencyTheorem', 'packageSufficiency'],
      'package-sufficiency source record must be an object',
      { actual: typeof source },
    );
  }
  const expectedKeys = [
    'id',
    'acceptedPackageValid',
    'explicitFinite',
    'polynomial',
    'allLocalPackagesAccepted',
    'allGlobalFirewallsAccepted',
    'allFinalArtefactsAccepted',
  ];
  if (!sameCanonical0(Object.keys(source).sort(), [...expectedKeys].sort())) {
    return validationReject0(
      ['PCCPack', 'PackSufficiencyTheorem', 'packageSufficiency'],
      'package-sufficiency source record must expose exactly the bounded version-zero fields',
      { expectedKeys, actualKeys: Object.keys(source).sort() },
    );
  }
  if (source.id !== 'PackageSufficiency') {
    return validationReject0(
      ['PCCPack', 'PackSufficiencyTheorem', 'packageSufficiency', 'id'],
      'package-sufficiency source id mismatch',
      { actual: source.id },
    );
  }
  for (const field of expectedKeys.slice(1)) {
    if (source[field] !== true) {
      return validationReject0(
        ['PCCPack', 'PackSufficiencyTheorem', 'packageSufficiency', field],
        'package-sufficiency bounded source field must be true',
        { field, actual: source[field] },
      );
    }
  }
  return validationAccept0({
    kind: 'GlobalFinalPrefixPackageSufficiencySource0NF',
    id: source.id,
  });
}

function validateGeneratedSufficiencySource0(source) {
  if (!isPlainObject0(source)) {
    return validationReject0(
      ['PCCPack', 'PackSufficiencyTheorem', 'generatedPackageSufficiency'],
      'generated-package sufficiency source record must be an object',
      { actual: typeof source },
    );
  }
  const expectedKeys = [
    'id',
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
    'coreExcludesAcceptRun',
    'assumption',
    'conclusion',
  ];
  if (!sameCanonical0(Object.keys(source).sort(), [...expectedKeys].sort())) {
    return validationReject0(
      ['PCCPack', 'PackSufficiencyTheorem', 'generatedPackageSufficiency'],
      'generated-package sufficiency source record must expose exactly the bounded version-zero fields',
      { expectedKeys, actualKeys: Object.keys(source).sort() },
    );
  }
  if (source.id !== 'GeneratedPackageSufficiency') {
    return validationReject0(
      ['PCCPack', 'PackSufficiencyTheorem', 'generatedPackageSufficiency', 'id'],
      'generated-package sufficiency source id mismatch',
      { actual: source.id },
    );
  }
  for (const field of [
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
    'coreExcludesAcceptRun',
  ]) {
    if (source[field] !== true) {
      return validationReject0(
        ['PCCPack', 'PackSufficiencyTheorem', 'generatedPackageSufficiency', field],
        'generated-package sufficiency bounded source field must be true',
        { field, actual: source[field] },
      );
    }
  }
  if (source.assumption
        !== 'CheckPCCPackexp(Core(GeneratePCCPack()))=accept'
      || source.conclusion
        !== 'CheckPCCPackexp(GeneratePCCPack())=accept') {
    return validationReject0(
      ['PCCPack', 'PackSufficiencyTheorem', 'generatedPackageSufficiency'],
      'generated-package sufficiency assumption or conclusion mismatch',
      {
        assumption: source.assumption,
        conclusion: source.conclusion,
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalPrefixGeneratedSufficiencySource0NF',
    id: source.id,
  });
}

function validateGeneratedCoreBoundary0(core) {
  if (!isPlainObject0(core)
      || core.kind !== 'PCCCorePackage0'
      || core.generatedBy !== 'GeneratePCCPack'
      || core.excludesAcceptRun !== true
      || core.includesAcceptRun !== false
      || Object.prototype.hasOwnProperty.call(core, 'AcceptRun')) {
    return validationReject0(
      ['PCCPack', 'Core'],
      'generated-package core must retain the untrusted-generator and accept-run exclusion boundary',
      { actual: core },
    );
  }
  for (const field of [
    'generatorUntrusted',
    'materializedOutputOnly',
    'canonicalByteEquality',
    'noDigestOnlyEquality',
  ]) {
    if (core[field] !== true) {
      return validationReject0(
        ['PCCPack', 'Core', field],
        'generated-package core boundary field must be true',
        { field, actual: core[field] },
      );
    }
  }
  if (!isPlainObject0(core.canonicalBytes)
      || core.canonicalBytes.alg !== 'canonical-json-v0'
      || !isDigest0(core.canonicalBytes.digest)) {
    return validationReject0(
      ['PCCPack', 'Core', 'canonicalBytes'],
      'generated-package core must expose canonical-json bytes and a SHA256 digest',
      { actual: core.canonicalBytes },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalPrefixGeneratedCoreBoundary0NF',
    canonicalBytesDigest: digestCanonical0(core.canonicalBytes),
  });
}

async function runPackNegativeProbe0({
  pack,
  probeName,
  mutate,
  expectedPath,
}) {
  const negativeInput = mutate(pack);
  const call = await callChecker0(
    `CheckPackSufficiency0(${probeName}).negative`,
    () => CheckPackSufficiency0(negativeInput),
  );
  if (!call.ok) {
    return validationReject0(
      ['PCCPack', 'negativeProbe', probeName],
      'final-prefix negative pack probe threw instead of returning a total record',
      call.witness,
    );
  }
  const record = call.record;
  const coord = record.Coord ?? record.coord;
  const path = record.Path ?? record.path;
  if (record.tag !== 'reject'
      || record.checker !== 'CheckPackSufficiency0'
      || coord !== 'CheckPackSufficiency0.PackSufficiencyTheorem'
      || !sameCanonical0(path, expectedPath)) {
    return validationReject0(
      ['PCCPack', 'negativeProbe', probeName],
      'final-prefix negative pack probe did not reject at the declared theorem coordinate',
      {
        expectedCoord: 'CheckPackSufficiency0.PackSufficiencyTheorem',
        expectedPath,
        actual: compactRecord0(record),
      },
    );
  }
  return validationAccept0({
    kind: 'GlobalFinalPrefixNegativePackProbe0NF',
    probeName,
    coord,
    path,
    recordDigest: record.Digest ?? record.digest,
  });
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

function isDigest0(value) {
  return isPlainObject0(value)
    && value.alg === 'SHA256'
    && typeof value.hex === 'string'
    && /^[0-9a-f]{64}$/u.test(value.hex);
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

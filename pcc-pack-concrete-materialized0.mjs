import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedPCCPack0,
  makeMaterializedPCCPack0,
} from './pcc-pack-materialized0.mjs';

const CHECKER_VERSION = 0;

const CONCRETE_PACK_FORBIDDEN_MARKERS0 = Object.freeze([
  'placeholder',
  'stub',
  'mock',
  'fixture-only',
  'todo',
]);

const CONCRETE_PACK_SYNTHETIC_MARKER0 = 'synthetic';

export function makeConcreteMaterializedPCCPackConfig0(overrides = {}) {
  return {
    kind: 'ConcreteMaterializedPCCPackConfig0',
    version: CHECKER_VERSION,
    checkMaterializedPCCPack: true,
    checkConcreteCoverage: true,
    checkJsonMaterialized: true,
    rejectFixtureMarkers: true,
    allowSyntheticScaffoldMarker: true,
    checkLinkage: true,
    materializedPCCPackConfig: {},
    ...overrides,
  };
}

export async function makeConcreteMaterializedPCCPack0({
  MaterializedPCCPackEnvelope = null,
  overrides = {},
} = {}) {
  const materializedPCCPackEnvelope = MaterializedPCCPackEnvelope ?? await makeMaterializedPCCPack0();
  const coverage = summarizeConcretePCCPackCoverage0(materializedPCCPackEnvelope);

  const linkage = {
    kind: 'ConcreteMaterializedPCCPackLinkage0',
    version: CHECKER_VERSION,
    materializedPCCPackDigest: digestCanonical0(materializedPCCPackEnvelope),
    pccPackDigest: digestCanonical0(materializedPCCPackEnvelope.PCCPack),
    concreteCoverageDigest: digestCanonical0(coverage),
    coreDigest: digestCanonical0(materializedPCCPackEnvelope.PCCPack.Core),
    manifestDigest: digestCanonical0(materializedPCCPackEnvelope.PCCPack.Manifest),
    packSufficiencyDigest: digestCanonical0(materializedPCCPackEnvelope.PCCPack.PackSufficiencyTheorem),
  };

  return {
    kind: 'ConcreteMaterializedPCCPack0',
    version: CHECKER_VERSION,
    MaterializedPCCPackEnvelope: materializedPCCPackEnvelope,
    PCCPack: materializedPCCPackEnvelope.PCCPack,
    ConcreteCoverage: coverage,
    Linkage: linkage,
    PiConcreteMaterializedPCCPack: {
      kind: 'PiConcreteMaterializedPCCPack0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'MaterializedPCCPackEnvelope',
          digest: linkage.materializedPCCPackDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteCoverage',
          digest: linkage.concreteCoverageDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function summarizeConcretePCCPackCoverage0(materializedPCCPackEnvelope) {
  const pccPack = materializedPCCPackEnvelope?.PCCPack ?? null;

  const kBundleEnvelope = materializedPCCPackEnvelope?.KBundleEnvelope ?? null;
  const hardEnvelope = materializedPCCPackEnvelope?.HardEnvelope ?? null;
  const rowsEnvelope = materializedPCCPackEnvelope?.RowsEnvelope ?? null;
  const localPackagesEnvelope = materializedPCCPackEnvelope?.LocalPackagesEnvelope ?? null;
  const globalFirewallsEnvelope = materializedPCCPackEnvelope?.GlobalFirewallsEnvelope ?? null;
  const globalProofDAGEnvelope = materializedPCCPackEnvelope?.GlobalProofDAGEnvelope ?? null;
  const finalIntegrationEnvelope = materializedPCCPackEnvelope?.FinalIntegrationEnvelope ?? null;

  const kBundleInventory = kBundleEnvelope?.ProofInventory ?? null;
  const hardCoverage = hardEnvelope?.Coverage ?? null;
  const finalIntegrationLinks = finalIntegrationEnvelope?.ConcreteLinks ?? null;

  const innerKBundle = resolveMaterializedKBundle0(kBundleEnvelope);
  const hardCheck = hardEnvelope?.HardCheck ?? hardEnvelope?.MaterializedHardEnvelope?.HardCheck ?? null;
  const rowPack = rowsEnvelope?.RowPack ?? null;
  const localPackages = localPackagesEnvelope?.LocalPackages ?? null;
  const globalFirewalls = globalFirewallsEnvelope?.GlobalFirewalls ?? null;
  const globalProofDAG = globalProofDAGEnvelope?.GlobalProofDAG ?? null;

  return {
    kind: 'ConcretePCCPackCoverage0',
    version: CHECKER_VERSION,

    pccPackKind: pccPack?.kind ?? null,
    generatedBy: pccPack?.Core?.generatedBy ?? null,
    publicConclusionOnlyAfterAcceptRun: pccPack?.Manifest?.publicConclusionOnlyAfterAcceptRun === true,

    kBundleEnvelopeKind: kBundleEnvelope?.kind ?? null,
    concreteKBundle: kBundleEnvelope?.kind === 'ConcreteMaterializedKBundle0',
    kBundleKernelRuleCoverageComplete: kBundleInventory?.kernelRuleCoverageComplete === true,
    kBundleSigmaProofRefsResolve: kBundleInventory?.sigmaProofRefsResolve === true,
    kBundleReflectionProofRefsResolve: kBundleInventory?.reflectionProofRefsResolve === true,
    kBundleNoOpaqueProofRefs: kBundleInventory?.noOpaqueProofRefs === true,
    kBundleNoExecutableMinSymbols: kBundleInventory?.noExecutableMinSymbols === true,
    kBundleCoverageDigest: isPlainObject(kBundleInventory) ? digestCanonical0(kBundleInventory) : null,

    hardEnvelopeKind: hardEnvelope?.kind ?? null,
    concreteHardCheck: hardEnvelope?.kind === 'ConcreteMaterializedHardCheck0',
    hardCheckerCoverageComplete: hardCoverage?.checkerCoverageComplete === true,
    hardRowKeyCoverageComplete: hardCoverage?.rowKeyCoverageComplete === true,
    hardRoutePriorityComplete: hardCoverage?.routePriorityComplete === true,
    hardProofRefPolicyComplete: hardCoverage?.proofRefPolicyComplete === true,
    hardHashDisciplineComplete: hardCoverage?.hashDisciplineComplete === true,
    hardNoMinCoverageComplete: hardCoverage?.noMinCoverageComplete === true,
    hardImportPolicyComplete: hardCoverage?.importPolicyComplete === true,
    hardReflectionPolicyComplete: hardCoverage?.reflectionPolicyComplete === true,
    hardBoundsPolicyComplete: hardCoverage?.boundsPolicyComplete === true,
    hardDiagnosticsPolicyComplete: hardCoverage?.diagnosticsPolicyComplete === true,
    hardCoverageDigest: isPlainObject(hardCoverage) ? digestCanonical0(hardCoverage) : null,

    rowsEnvelopeKind: rowsEnvelope?.kind ?? null,
    concreteRows: rowsEnvelope?.kind === 'ConcreteMaterializedRows0',

    localPackagesEnvelopeKind: localPackagesEnvelope?.kind ?? null,
    concreteLocalPackages: localPackagesEnvelope?.kind === 'ConcreteMaterializedLocalPackages0',

    globalFirewallsEnvelopeKind: globalFirewallsEnvelope?.kind ?? null,
    concreteGlobalFirewalls: globalFirewallsEnvelope?.kind === 'ConcreteMaterializedGlobalFirewalls0',

    globalProofDAGEnvelopeKind: globalProofDAGEnvelope?.kind ?? null,
    concreteGlobalProofDAG: globalProofDAGEnvelope?.kind === 'ConcreteMaterializedGlobalProofDAG0',

    finalIntegrationEnvelopeKind: finalIntegrationEnvelope?.kind ?? null,
    concreteFinalIntegration: finalIntegrationEnvelope?.kind === 'ConcreteMaterializedFinalIntegration0',
    finalIntegrationConcreteGlobalProofDAG: finalIntegrationLinks?.concreteGlobalProofDAG === true,
    finalIntegrationGPackFieldCoverageComplete: finalIntegrationLinks?.gpackFieldCoverageComplete === true,
    finalIntegrationRowFamGCoverageComplete: finalIntegrationLinks?.rowFamGCoverageComplete === true,
    finalIntegrationUsesGPack: finalIntegrationLinks?.finalIntegrationUsesGPack === true,
    rowFamGUsesGPack: finalIntegrationLinks?.rowFamGUsesGPack === true,
    finalTheoremUsesFinalIntegration: finalIntegrationLinks?.finalTheoremUsesFinalIntegration === true,
    rowFamFinalUsesFinalTheorem: finalIntegrationLinks?.rowFamFinalUsesFinalTheorem === true,
    finalMatchUsesGPack: finalIntegrationLinks?.finalMatchUsesGPack === true,
    satDecisionUsesGPack: finalIntegrationLinks?.satDecisionUsesGPack === true,
    finalIntegrationLinksDigest: isPlainObject(finalIntegrationLinks) ? digestCanonical0(finalIntegrationLinks) : null,

    pccPackLinkedToKBundle: digestMatchesAnyCanonical0(
      pccPack?.KBundle ?? null,
      concreteKBundleCandidates0(kBundleEnvelope),
    ),
    pccPackLinkedToHardCheck: sameDigestHex0(digestCanonical0(pccPack?.HardCheck ?? null), digestCanonical0(hardCheck)),
    pccPackLinkedToRows: sameDigestHex0(digestCanonical0(pccPack?.RowPack ?? null), digestCanonical0(rowPack)),
    pccPackLinkedToLocalPackages: sameDigestHex0(digestCanonical0(pccPack?.LocalPackages ?? null), digestCanonical0(localPackages)),
    pccPackLinkedToGlobalFirewalls: sameDigestHex0(digestCanonical0(pccPack?.GlobalFirewalls ?? null), digestCanonical0(globalFirewalls)),
    pccPackLinkedToGlobalProofDAG: sameDigestHex0(digestCanonical0(pccPack?.GlobalProofDAG ?? null), digestCanonical0(globalProofDAG)),
    pccPackLinkedToGPack: sameDigestHex0(digestCanonical0(pccPack?.GPack ?? null), digestCanonical0(finalIntegrationEnvelope?.GPack ?? null)),
    pccPackLinkedToFinalIntegration: sameDigestHex0(digestCanonical0(pccPack?.FinalIntegration ?? null), digestCanonical0(finalIntegrationEnvelope?.FinalIntegration ?? null)),
    pccPackLinkedToFinalTheorem: sameDigestHex0(digestCanonical0(pccPack?.FinalTheorem ?? null), digestCanonical0(finalIntegrationEnvelope?.FinalTheorem ?? null)),
  };
}

export async function CheckConcreteMaterializedPCCPack0(
  input,
  config = makeConcreteMaterializedPCCPackConfig0(),
) {
  const checker = 'CheckConcreteMaterializedPCCPack0';
  const ledger = [];
  const cfg = makeConcreteMaterializedPCCPackConfig0(config);
  const envelope = normalizeInput0(input);

  const cfgCheck = validateConfig0(cfg);

  ledger.push({
    phase: 'config',
    status: cfgCheck.ok ? 'pass' : 'fail',
    digest: digestCanonical0(cfgCheck.nf ?? cfgCheck.witness ?? null),
  });

  if (!cfgCheck.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.config`,
      path: cfgCheck.path,
      witness: cfgCheck.witness,
      ledger,
    });
  }

  const shape = validateShape0(envelope);

  ledger.push({
    phase: 'shape',
    status: shape.ok ? 'pass' : 'fail',
    digest: digestCanonical0(shape.nf ?? shape.witness ?? null),
  });

  if (!shape.ok) {
    return makeRejectRecord({
      checker,
      coord: `${checker}.input`,
      path: shape.path,
      witness: shape.witness,
      ledger,
    });
  }

  if (cfg.checkMaterializedPCCPack === true) {
    const record = await CheckMaterializedPCCPack0(
      envelope.MaterializedPCCPackEnvelope,
      cfg.materializedPCCPackConfig ?? {},
    );
    const result = recordToValidation0(record, ['MaterializedPCCPackEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedPCCPack0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.MaterializedPCCPack`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  const recomputedCoverage = summarizeConcretePCCPackCoverage0(envelope.MaterializedPCCPackEnvelope);

  if (cfg.checkConcreteCoverage === true) {
    const coverage = validateConcreteCoverage0(envelope.ConcreteCoverage, recomputedCoverage);

    ledger.push({
      phase: 'concreteCoverage',
      status: coverage.ok ? 'pass' : 'fail',
      digest: digestCanonical0(coverage.nf ?? coverage.witness ?? null),
    });

    if (!coverage.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.concreteCoverage`,
        path: coverage.path,
        witness: coverage.witness,
        ledger,
      });
    }
  }

  if (cfg.checkJsonMaterialized === true) {
    const json = validateJsonMaterialized0(envelope);

    ledger.push({
      phase: 'jsonMaterialized',
      status: json.ok ? 'pass' : 'fail',
      digest: digestCanonical0(json.nf ?? json.witness ?? null),
    });

    if (!json.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.json`,
        path: json.path,
        witness: json.witness,
        ledger,
      });
    }
  }

  const markerInventory = collectFixtureMarkers0(envelope, ['ConcreteMaterializedPCCPack0']);

  ledger.push({
    phase: 'fixtureMarkerInventory',
    status: 'pass',
    digest: digestCanonical0(markerInventory),
  });

  if (cfg.rejectFixtureMarkers === true) {
    const markers = validateNoForbiddenFixtureMarkers0(markerInventory, cfg);

    ledger.push({
      phase: 'fixtureMarkers',
      status: markers.ok ? 'pass' : 'fail',
      digest: digestCanonical0(markers.nf ?? markers.witness ?? null),
    });

    if (!markers.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.fixtureMarkers`,
        path: markers.path,
        witness: markers.witness,
        ledger,
      });
    }
  }

  if (cfg.checkLinkage === true) {
    const linkage = validateLinkage0(envelope, recomputedCoverage);

    ledger.push({
      phase: 'linkage',
      status: linkage.ok ? 'pass' : 'fail',
      digest: digestCanonical0(linkage.nf ?? linkage.witness ?? null),
    });

    if (!linkage.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.linkage`,
        path: linkage.path,
        witness: linkage.witness,
        ledger,
      });
    }
  }

  const nf = {
    kind: 'ConcreteMaterializedPCCPack0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,

    pccPackDigest: digestCanonical0(envelope.PCCPack),
    materializedPCCPackDigest: digestCanonical0(envelope.MaterializedPCCPackEnvelope),
    concreteCoverageDigest: digestCanonical0(recomputedCoverage),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),

    concreteKBundle: recomputedCoverage.concreteKBundle,
    kBundleKernelRuleCoverageComplete: recomputedCoverage.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: recomputedCoverage.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: recomputedCoverage.kBundleReflectionProofRefsResolve,

    concreteHardCheck: recomputedCoverage.concreteHardCheck,
    hardCheckerCoverageComplete: recomputedCoverage.hardCheckerCoverageComplete,
    hardRowKeyCoverageComplete: recomputedCoverage.hardRowKeyCoverageComplete,
    hardRoutePriorityComplete: recomputedCoverage.hardRoutePriorityComplete,
    hardProofRefPolicyComplete: recomputedCoverage.hardProofRefPolicyComplete,
    hardHashDisciplineComplete: recomputedCoverage.hardHashDisciplineComplete,
    hardNoMinCoverageComplete: recomputedCoverage.hardNoMinCoverageComplete,
    hardImportPolicyComplete: recomputedCoverage.hardImportPolicyComplete,
    hardReflectionPolicyComplete: recomputedCoverage.hardReflectionPolicyComplete,
    hardBoundsPolicyComplete: recomputedCoverage.hardBoundsPolicyComplete,
    hardDiagnosticsPolicyComplete: recomputedCoverage.hardDiagnosticsPolicyComplete,

    concreteRows: recomputedCoverage.concreteRows,
    concreteLocalPackages: recomputedCoverage.concreteLocalPackages,
    concreteGlobalFirewalls: recomputedCoverage.concreteGlobalFirewalls,
    concreteGlobalProofDAG: recomputedCoverage.concreteGlobalProofDAG,

    concreteFinalIntegration: recomputedCoverage.concreteFinalIntegration,
    finalIntegrationConcreteGlobalProofDAG: recomputedCoverage.finalIntegrationConcreteGlobalProofDAG,
    finalIntegrationGPackFieldCoverageComplete: recomputedCoverage.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: recomputedCoverage.finalIntegrationRowFamGCoverageComplete,

    pccPackLinkedToKBundle: recomputedCoverage.pccPackLinkedToKBundle,
    pccPackLinkedToHardCheck: recomputedCoverage.pccPackLinkedToHardCheck,
    pccPackLinkedToRows: recomputedCoverage.pccPackLinkedToRows,
    pccPackLinkedToLocalPackages: recomputedCoverage.pccPackLinkedToLocalPackages,
    pccPackLinkedToGlobalFirewalls: recomputedCoverage.pccPackLinkedToGlobalFirewalls,
    pccPackLinkedToGlobalProofDAG: recomputedCoverage.pccPackLinkedToGlobalProofDAG,
    pccPackLinkedToGPack: recomputedCoverage.pccPackLinkedToGPack,
    pccPackLinkedToFinalIntegration: recomputedCoverage.pccPackLinkedToFinalIntegration,
    pccPackLinkedToFinalTheorem: recomputedCoverage.pccPackLinkedToFinalTheorem,

    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
    allowSyntheticScaffoldMarker: cfg.allowSyntheticScaffoldMarker,
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeConcreteMaterializedPCCPackFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteMaterializedPCCPackFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteMaterializedPCCPack0(options);
  const checked = await CheckConcreteMaterializedPCCPack0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteMaterializedPCCPack0.json');
  const materializedPCCPackPath = path.join(outDir, 'MaterializedPCCPack0.json');
  const pccPackPath = path.join(outDir, 'PCCPack0.json');
  const coveragePath = path.join(outDir, 'ConcretePCCPackCoverage0.json');
  const checkPath = path.join(outDir, 'ConcreteMaterializedPCCPack0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(materializedPCCPackPath, envelope.MaterializedPCCPackEnvelope);
  await writeJsonFile0(pccPackPath, envelope.PCCPack);
  await writeJsonFile0(coveragePath, envelope.ConcreteCoverage);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      materializedPCCPackPath,
      pccPackPath,
      coveragePath,
      checkPath,
    },
  };
}

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'MaterializedPCCPack0') {
    const coverage = summarizeConcretePCCPackCoverage0(input);

    return {
      kind: 'ConcreteMaterializedPCCPack0',
      version: CHECKER_VERSION,
      MaterializedPCCPackEnvelope: input,
      PCCPack: input.PCCPack,
      ConcreteCoverage: coverage,
      Linkage: {
        kind: 'ConcreteMaterializedPCCPackLinkage0',
        version: CHECKER_VERSION,
        materializedPCCPackDigest: digestCanonical0(input),
        pccPackDigest: digestCanonical0(input.PCCPack),
        concreteCoverageDigest: digestCanonical0(coverage),
        coreDigest: digestCanonical0(input.PCCPack.Core),
        manifestDigest: digestCanonical0(input.PCCPack.Manifest),
        packSufficiencyDigest: digestCanonical0(input.PCCPack.PackSufficiencyTheorem),
      },
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteMaterializedPCCPackConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteMaterializedPCCPackConfig0') {
    return validationReject0(['kind'], 'ConcreteMaterializedPCCPackConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedPCCPackConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkMaterializedPCCPack',
    'checkConcreteCoverage',
    'checkJsonMaterialized',
    'rejectFixtureMarkers',
    'allowSyntheticScaffoldMarker',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteMaterializedPCCPackConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.materializedPCCPackConfig)) {
    return validationReject0(['materializedPCCPackConfig'], 'materializedPCCPackConfig must be an object', {
      actual: typeof config.materializedPCCPackConfig,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedPCCPackConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteMaterializedPCCPack0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteMaterializedPCCPack0') {
    return validationReject0(['kind'], 'ConcreteMaterializedPCCPack0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (!isPlainObject(envelope.MaterializedPCCPackEnvelope)) {
    return validationReject0(['MaterializedPCCPackEnvelope'], 'ConcreteMaterializedPCCPack0 must include MaterializedPCCPackEnvelope', {
      actual: typeof envelope.MaterializedPCCPackEnvelope,
    });
  }

  if (!isPlainObject(envelope.PCCPack)) {
    return validationReject0(['PCCPack'], 'ConcreteMaterializedPCCPack0 must include PCCPack', {
      actual: typeof envelope.PCCPack,
    });
  }

  if (!isPlainObject(envelope.ConcreteCoverage)) {
    return validationReject0(['ConcreteCoverage'], 'ConcreteMaterializedPCCPack0 must include ConcreteCoverage', {
      actual: typeof envelope.ConcreteCoverage,
    });
  }

  if (!sameDigestHex0(digestCanonical0(envelope.MaterializedPCCPackEnvelope.PCCPack), digestCanonical0(envelope.PCCPack))) {
    return validationReject0(['PCCPack'], 'top-level PCCPack must match MaterializedPCCPackEnvelope.PCCPack', {
      expected: digestCanonical0(envelope.MaterializedPCCPackEnvelope.PCCPack),
      actual: digestCanonical0(envelope.PCCPack),
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedPCCPackShape0NF',
  });
}

function validateConcreteCoverage0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['ConcreteCoverage'], 'ConcretePCCPackCoverage0 must match recomputed concrete package coverage', {
      expectedDigest: digestCanonical0(expected),
      actualDigest: digestCanonical0(actual),
    });
  }

  for (const field of [
    'concreteKBundle',
    'kBundleKernelRuleCoverageComplete',
    'kBundleSigmaProofRefsResolve',
    'kBundleReflectionProofRefsResolve',

    'concreteHardCheck',
    'hardCheckerCoverageComplete',
    'hardRowKeyCoverageComplete',
    'hardRoutePriorityComplete',
    'hardProofRefPolicyComplete',
    'hardHashDisciplineComplete',
    'hardNoMinCoverageComplete',
    'hardImportPolicyComplete',
    'hardReflectionPolicyComplete',
    'hardBoundsPolicyComplete',
    'hardDiagnosticsPolicyComplete',

    'concreteRows',
    'concreteLocalPackages',
    'concreteGlobalFirewalls',
    'concreteGlobalProofDAG',

    'concreteFinalIntegration',
    'finalIntegrationConcreteGlobalProofDAG',
    'finalIntegrationGPackFieldCoverageComplete',
    'finalIntegrationRowFamGCoverageComplete',

    'pccPackLinkedToKBundle',
    'pccPackLinkedToHardCheck',
    'pccPackLinkedToRows',
    'pccPackLinkedToLocalPackages',
    'pccPackLinkedToGlobalFirewalls',
    'pccPackLinkedToGlobalProofDAG',
    'pccPackLinkedToGPack',
    'pccPackLinkedToFinalIntegration',
    'pccPackLinkedToFinalTheorem',
  ]) {
    if (expected[field] !== true) {
      return validationReject0(['ConcreteCoverage', field], `ConcretePCCPackCoverage0 must certify ${field}`, {
        actual: expected[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcretePCCPackCoverage0NF',
    concreteCoverageDigest: digestCanonical0(expected),
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['ConcreteMaterializedPCCPack0'], 'ConcreteMaterializedPCCPack0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ConcreteMaterializedPCCPack0'], 'ConcreteMaterializedPCCPack0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedPCCPackJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateLinkage0(envelope, coverage) {
  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteMaterializedPCCPackLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteMaterializedPCCPack0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const expected = {
    materializedPCCPackDigest: digestCanonical0(envelope.MaterializedPCCPackEnvelope),
    pccPackDigest: digestCanonical0(envelope.PCCPack),
    concreteCoverageDigest: digestCanonical0(coverage),
    coreDigest: digestCanonical0(envelope.PCCPack.Core),
    manifestDigest: digestCanonical0(envelope.PCCPack.Manifest),
    packSufficiencyDigest: digestCanonical0(envelope.PCCPack.PackSufficiencyTheorem),
  };

  for (const [field, expectedDigest] of Object.entries(expected)) {
    if (!sameDigestHex0(envelope.Linkage[field], expectedDigest)) {
      return validationReject0(['Linkage', field], `Linkage ${field} mismatch`, {
        expected: expectedDigest,
        actual: envelope.Linkage[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedPCCPackLinkage0NF',
    present: true,
    ...expected,
  });
}

function collectFixtureMarkers0(value, rootPath) {
  const hits = [];

  scanFixtureMarkers0(value, rootPath, hits);

  return {
    kind: 'ConcreteMaterializedPCCPackFixtureMarkerInventory0NF',
    syntheticMarkerCount: hits.filter((hit) => hit.marker === CONCRETE_PACK_SYNTHETIC_MARKER0).length,
    forbiddenMarkerCount: hits.filter((hit) => hit.marker !== CONCRETE_PACK_SYNTHETIC_MARKER0).length,
    hits,
  };
}

function validateNoForbiddenFixtureMarkers0(markerInventory, config) {
  const disallowed = markerInventory.hits.filter((hit) => (
    hit.marker !== CONCRETE_PACK_SYNTHETIC_MARKER0 ||
    config.allowSyntheticScaffoldMarker !== true
  ));

  if (disallowed.length > 0) {
    return validationReject0(disallowed[0].path, 'concrete materialized PCCPack contains forbidden fixture-marker text', {
      hit: disallowed[0],
      hitCount: disallowed.length,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedPCCPackNoForbiddenFixtureMarkers0NF',
    syntheticMarkerCount: markerInventory.syntheticMarkerCount,
    forbiddenMarkerCount: markerInventory.forbiddenMarkerCount,
  });
}

function scanFixtureMarkers0(value, pathNow, hits) {
  if (value === null || value === undefined) {
    return;
  }

  if (typeof value === 'string') {
    const lower = value.toLowerCase();

    for (const marker of [
      CONCRETE_PACK_SYNTHETIC_MARKER0,
      ...CONCRETE_PACK_FORBIDDEN_MARKERS0,
    ]) {
      if (lower.includes(marker)) {
        hits.push({
          path: pathNow,
          marker,
          value,
        });
      }
    }

    return;
  }

  if (
    typeof value === 'number' ||
    typeof value === 'boolean' ||
    typeof value === 'bigint'
  ) {
    return;
  }

  if (Array.isArray(value)) {
    for (let index = 0; index < value.length; index += 1) {
      scanFixtureMarkers0(value[index], [...pathNow, index], hits);
    }

    return;
  }

  if (!isPlainObject(value)) {
    return;
  }

  for (const key of Object.keys(value)) {
    scanFixtureMarkers0(value[key], [...pathNow, key], hits);
  }
}

function digestMatchesAnyCanonical0(value, candidates) {
  const actual = digestCanonical0(value ?? null);

  return candidates.some((candidate) => (
    candidate !== null &&
    candidate !== undefined &&
    sameDigestHex0(actual, digestCanonical0(candidate))
  ));
}

function concreteKBundleCandidates0(value) {
  const candidates = [];
  const push = (candidate) => {
    if (candidate !== null && candidate !== undefined) {
      candidates.push(candidate);
    }
  };

  push(value);

  if (!isPlainObject(value)) {
    return candidates;
  }

  push(value.MaterializedKBundleEnvelope);
  push(value.materializedKBundleEnvelope);
  push(value.KBundle);
  push(value.KImpl);
  push(value.MaterializedKBundleEnvelope?.KBundle);
  push(value.MaterializedKBundleEnvelope?.KImpl);

  const materializedShape = materializedKBundleShapeFromConcrete0(value);

  if (materializedShape !== null) {
    push(materializedShape);
  }

  return candidates;
}

function materializedKBundleShapeFromConcrete0(value) {
  if (!isPlainObject(value) || value.kind !== 'ConcreteMaterializedKBundle0') {
    return null;
  }

  if (
    !isPlainObject(value.Boot0) ||
    !isPlainObject(value.KImpl) ||
    !isPlainObject(value.K0) ||
    !isPlainObject(value.PSigma) ||
    !isPlainObject(value.ReflectionRegistry)
  ) {
    return null;
  }

  return {
    kind: 'MaterializedKBundle0',
    version: value.version ?? 0,
    Boot0: value.Boot0,
    KImpl: value.KImpl,
    K0: value.K0,
    PSigma: value.PSigma,
    ReflectionRegistry: value.ReflectionRegistry,
  };
}

function resolveMaterializedKBundle0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'MaterializedKBundle0'
    ? value
    : value.MaterializedKBundleEnvelope ?? value.materializedKBundleEnvelope ?? null;
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}

function sameDigestHex0(actual, expected) {
  return (
    isPlainObject(actual) &&
    isPlainObject(expected) &&
    typeof actual.hex === 'string' &&
    typeof expected.hex === 'string' &&
    actual.hex === expected.hex &&
    (
      actual.alg === undefined ||
      expected.alg === undefined ||
      actual.alg === expected.alg
    )
  );
}

function recordToValidation0(record, path) {
  if (isRejectRecord0(record)) {
    return validationReject0(path, `${record.checker} rejected`, {
      inner: compactReject0(record),
    });
  }

  return validationAccept0(record.NF ?? record.nf ?? record);
}

function makeAcceptRecord({
  checker,
  nf,
  ledger,
}) {
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

function makeRejectRecord({
  checker,
  coord,
  path,
  witness,
  ledger,
}) {
  const rejectNF = {
    kind: `${checker}RejectNF`,
    checker,
    version: CHECKER_VERSION,
    coord,
    path,
    witness,
    ledger,
  };

  const digest = digestCanonical0(rejectNF);

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
  return {
    ok: true,
    nf,
  };
}

function validationReject0(path, reason, detail) {
  return {
    ok: false,
    path,
    witness: {
      reason,
      detail,
    },
  };
}

function isRejectRecord0(value) {
  return classifyRecord0(value) === 'reject';
}

function classifyRecord0(value) {
  if (!isPlainObject(value)) {
    return 'unknown';
  }

  const raw =
    value.tag ??
    value.kind ??
    value.verdict ??
    value.status ??
    value.result ??
    value.outcome;

  if (typeof raw !== 'string') {
    return 'unknown';
  }

  const normalized = raw.trim().toLowerCase();

  if (
    normalized === 'accept' ||
    normalized === 'accepted' ||
    normalized === 'ok' ||
    normalized === 'pass' ||
    normalized === 'passed'
  ) {
    return 'accept';
  }

  if (
    normalized === 'reject' ||
    normalized === 'rejected' ||
    normalized === 'err' ||
    normalized === 'error' ||
    normalized === 'fail' ||
    normalized === 'failed'
  ) {
    return 'reject';
  }

  return 'unknown';
}

function compactReject0(value) {
  if (!isPlainObject(value)) {
    return value;
  }

  return {
    checker: value.checker ?? null,
    coord: value.Coord ?? value.coord ?? null,
    path: value.Path ?? value.path ?? null,
    witness: value.Witness ?? value.witness ?? null,
    digest: value.Digest ?? value.digest ?? null,
  };
}

function isPlainObject(value) {
  if (value === null || typeof value !== 'object') {
    return false;
  }

  const proto = Object.getPrototypeOf(value);
  return proto === Object.prototype || proto === null;
}

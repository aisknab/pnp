import fs from 'node:fs/promises';
import path from 'node:path';

import {
  digestCanonical0,
  stableStringify0,
} from './pcc-verifier-frag0.mjs';

import {
  CheckMaterializedGeneratedAcceptRun0,
  makeMaterializedGeneratedAcceptRun0,
} from './pcc-accept-run-materialized0.mjs';

import {
  CheckConcreteMaterializedPCCPack0,
  makeConcreteMaterializedPCCPack0,
  summarizeConcretePCCPackCoverage0,
} from './pcc-pack-concrete-materialized0.mjs';

import {
  CheckPCCPackexp0,
} from './pcc-check-pcc-pack-exp0.mjs';

import {
  CheckGeneratedPCCPackexp0,
  makeGeneratedPCCPackexp0,
} from './pcc-generate-pcc-pack0.mjs';

const CHECKER_VERSION = 0;

export function makeConcreteMaterializedGeneratedAcceptRunConfig0(overrides = {}) {
  return {
    kind: 'ConcreteMaterializedGeneratedAcceptRunConfig0',
    version: CHECKER_VERSION,
    checkGeneratedAcceptRun: true,
    checkConcretePCCPack: true,
    checkPCCPackexp: true,
    checkGeneratedPCCPackexp: true,
    checkConcreteChain: true,
    checkJsonMaterialized: true,
    checkLinkage: true,
    generatedAcceptRunConfig: {},
    concretePCCPackConfig: {},
    checkPCCPackexpConfig: {},
    generatedPCCPackexpConfig: {},
    ...overrides,
  };
}

export async function makeConcreteMaterializedGeneratedAcceptRun0({
  GeneratedAcceptRunEnvelope = null,
  GeneratedPCCPackexpEnvelope = null,
  overrides = {},
} = {}) {
  const generatedAcceptRunEnvelope = GeneratedAcceptRunEnvelope ?? await makeMaterializedGeneratedAcceptRun0();
  const concreteChain = summarizeConcreteGeneratedAcceptRunChain0(generatedAcceptRunEnvelope);
  const checkPCCPackexpRecord = await CheckPCCPackexp0(generatedAcceptRunEnvelope.MaterializedPCCPack);
  const generatedPCCPack = await makeConcreteMaterializedPCCPack0({
    MaterializedPCCPackEnvelope: generatedAcceptRunEnvelope.MaterializedPCCPack,
  });
  const generatedPCCPackexpEnvelope = GeneratedPCCPackexpEnvelope ?? await makeGeneratedPCCPackexp0({
    GeneratedPCCPack: generatedPCCPack,
    CheckPCCPackexpRecord: checkPCCPackexpRecord,
  });
  const checkGeneratedPCCPackexpRecord = await CheckGeneratedPCCPackexp0(generatedPCCPackexpEnvelope);

  const linkage = {
    kind: 'ConcreteMaterializedGeneratedAcceptRunLinkage0',
    version: CHECKER_VERSION,
    generatedAcceptRunEnvelopeDigest: digestCanonical0(generatedAcceptRunEnvelope),
    materializedPCCPackDigest: digestCanonical0(generatedAcceptRunEnvelope.MaterializedPCCPack),
    pccPackDigest: digestCanonical0(resolvePCCPack0(generatedAcceptRunEnvelope.MaterializedPCCPack)),
    acceptRunDigest: digestCanonical0(generatedAcceptRunEnvelope.AcceptRun),
    generatedPackageDigest: digestCanonical0(generatedAcceptRunEnvelope.GeneratedPackage),
    checkPCCPackexpRecordDigest: digestFromRecord0(checkPCCPackexpRecord),
    generatedPCCPackexpEnvelopeDigest: digestCanonical0(generatedPCCPackexpEnvelope),
    generatedPCCPackDigest: digestCanonical0(generatedPCCPackexpEnvelope.GeneratedPCCPack),
    checkGeneratedPCCPackexpRecordDigest: digestFromRecord0(checkGeneratedPCCPackexpRecord),
    concreteChainDigest: digestCanonical0(concreteChain),
  };

  return {
    kind: 'ConcreteMaterializedGeneratedAcceptRun0',
    version: CHECKER_VERSION,
    GeneratedAcceptRunEnvelope: generatedAcceptRunEnvelope,
    CheckPCCPackexpRecord: checkPCCPackexpRecord,
    GeneratedPCCPackexpEnvelope: generatedPCCPackexpEnvelope,
    CheckGeneratedPCCPackexpRecord: checkGeneratedPCCPackexpRecord,
    ConcreteChain: concreteChain,
    Linkage: linkage,
    PiConcreteMaterializedGeneratedAcceptRun: {
      kind: 'PiConcreteMaterializedGeneratedAcceptRun0',
      version: CHECKER_VERSION,
      materialized: true,
      externalJson: true,
      refs: [
        {
          kind: 'MaterializedRef0',
          target: 'GeneratedAcceptRunEnvelope',
          digest: linkage.generatedAcceptRunEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'CheckPCCPackexpRecord',
          digest: linkage.checkPCCPackexpRecordDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'GeneratedPCCPackexpEnvelope',
          digest: linkage.generatedPCCPackexpEnvelopeDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'CheckGeneratedPCCPackexpRecord',
          digest: linkage.checkGeneratedPCCPackexpRecordDigest,
        },
        {
          kind: 'MaterializedRef0',
          target: 'ConcreteChain',
          digest: linkage.concreteChainDigest,
        },
      ],
    },
    ...overrides,
  };
}

export function summarizeConcreteGeneratedAcceptRunChain0(generatedAcceptRunEnvelope) {
  const materializedPCCPack = generatedAcceptRunEnvelope?.MaterializedPCCPack ?? null;
  const pccPack = resolvePCCPack0(materializedPCCPack);

  const rowsEnvelope = materializedPCCPack?.RowsEnvelope ?? null;
  const localPackagesEnvelope = materializedPCCPack?.LocalPackagesEnvelope ?? null;
  const globalFirewallsEnvelope = materializedPCCPack?.GlobalFirewallsEnvelope ?? null;
  const globalProofDAGEnvelope = materializedPCCPack?.GlobalProofDAGEnvelope ?? null;
  const kBundleEnvelope = materializedPCCPack?.KBundleEnvelope ?? null;
  const hardEnvelope = materializedPCCPack?.HardEnvelope ?? null;
  const finalIntegrationEnvelope = materializedPCCPack?.FinalIntegrationEnvelope ?? null;

  const kBundleInventory = kBundleEnvelope?.ProofInventory ?? null;
  const hardCoverage = hardEnvelope?.Coverage ?? null;
  const finalIntegrationLinks = finalIntegrationEnvelope?.ConcreteLinks ?? null;
  const concretePCCPackCoverage = summarizeConcretePCCPackCoverage0(materializedPCCPack);

  const rowPack = resolveRowPack0(rowsEnvelope);
  const localPackages = resolveLocalPackages0(localPackagesEnvelope);
  const globalFirewalls = resolveGlobalFirewalls0(globalFirewallsEnvelope);
  const globalProofDAG = resolveGlobalProofDAG0(globalProofDAGEnvelope);

  const pccPackDigest = digestCanonical0(pccPack);
  const acceptRunPgenDigest = digestCanonical0(generatedAcceptRunEnvelope?.AcceptRun?.Pgen ?? null);

  const rowPackDigest = digestCanonical0(rowPack);
  const localPackagesDigest = digestCanonical0(localPackages);
  const globalFirewallsDigest = digestCanonical0(globalFirewalls);
  const globalProofDAGDigest = digestCanonical0(globalProofDAG);

  return {
    kind: 'ConcreteGeneratedAcceptRunChain0',
    version: CHECKER_VERSION,

    concreteRows: rowsEnvelope?.kind === 'ConcreteMaterializedRows0',
    concreteLocalPackages: localPackagesEnvelope?.kind === 'ConcreteMaterializedLocalPackages0',
    concreteGlobalFirewalls: globalFirewallsEnvelope?.kind === 'ConcreteMaterializedGlobalFirewalls0',
    concreteGlobalProofDAG: globalProofDAGEnvelope?.kind === 'ConcreteMaterializedGlobalProofDAG0',

    concreteKBundle: kBundleEnvelope?.kind === 'ConcreteMaterializedKBundle0',
    kBundleKernelRuleCoverageComplete: kBundleInventory?.kernelRuleCoverageComplete === true,
    kBundleSigmaProofRefsResolve: kBundleInventory?.sigmaProofRefsResolve === true,
    kBundleReflectionProofRefsResolve: kBundleInventory?.reflectionProofRefsResolve === true,

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

    concretePCCPack: (
      concretePCCPackCoverage.pccPackKind === 'PCCPack0' &&
      allTrue0(
        concretePCCPackCoverage.publicConclusionOnlyAfterAcceptRun,
        concretePCCPackCoverage.concreteKBundle,
        concretePCCPackCoverage.concreteHardCheck,
        concretePCCPackCoverage.concreteRows,
        concretePCCPackCoverage.concreteLocalPackages,
        concretePCCPackCoverage.concreteGlobalFirewalls,
        concretePCCPackCoverage.concreteGlobalProofDAG,
        concretePCCPackCoverage.concreteFinalIntegration,
        concretePCCPackCoverage.pccPackLinkedToKBundle,
        concretePCCPackCoverage.pccPackLinkedToHardCheck,
        concretePCCPackCoverage.pccPackLinkedToRows,
        concretePCCPackCoverage.pccPackLinkedToLocalPackages,
        concretePCCPackCoverage.pccPackLinkedToGlobalFirewalls,
        concretePCCPackCoverage.pccPackLinkedToGlobalProofDAG,
        concretePCCPackCoverage.pccPackLinkedToGPack,
        concretePCCPackCoverage.pccPackLinkedToFinalIntegration,
        concretePCCPackCoverage.pccPackLinkedToFinalTheorem
      )
    ),
    concretePCCPackCoverageDigest: digestCanonical0(concretePCCPackCoverage),
    pccPackPublicConclusionOnlyAfterAcceptRun: concretePCCPackCoverage.publicConclusionOnlyAfterAcceptRun === true,
    pccPackLinkedToKBundle: concretePCCPackCoverage.pccPackLinkedToKBundle === true,
    pccPackLinkedToHardCheck: concretePCCPackCoverage.pccPackLinkedToHardCheck === true,
    pccPackLinkedToRows: concretePCCPackCoverage.pccPackLinkedToRows === true,
    pccPackLinkedToLocalPackages: concretePCCPackCoverage.pccPackLinkedToLocalPackages === true,
    pccPackLinkedToGlobalFirewalls: concretePCCPackCoverage.pccPackLinkedToGlobalFirewalls === true,
    pccPackLinkedToGlobalProofDAG: concretePCCPackCoverage.pccPackLinkedToGlobalProofDAG === true,
    pccPackLinkedToGPack: concretePCCPackCoverage.pccPackLinkedToGPack === true,
    pccPackLinkedToFinalIntegration: concretePCCPackCoverage.pccPackLinkedToFinalIntegration === true,
    pccPackLinkedToFinalTheorem: concretePCCPackCoverage.pccPackLinkedToFinalTheorem === true,

    rowsEnvelopeKind: rowsEnvelope?.kind ?? null,
    localPackagesEnvelopeKind: localPackagesEnvelope?.kind ?? null,
    globalFirewallsEnvelopeKind: globalFirewallsEnvelope?.kind ?? null,
    globalProofDAGEnvelopeKind: globalProofDAGEnvelope?.kind ?? null,
    kBundleEnvelopeKind: kBundleEnvelope?.kind ?? null,
    hardEnvelopeKind: hardEnvelope?.kind ?? null,
    finalIntegrationEnvelopeKind: finalIntegrationEnvelope?.kind ?? null,

    kBundleCoverageDigest: isPlainObject(kBundleInventory) ? digestCanonical0(kBundleInventory) : null,
    hardCoverageDigest: isPlainObject(hardCoverage) ? digestCanonical0(hardCoverage) : null,
    finalIntegrationLinksDigest: isPlainObject(finalIntegrationLinks) ? digestCanonical0(finalIntegrationLinks) : null,

    pccPackDigest,
    acceptRunPgenDigest,
    pccPackLinkedToAcceptRun: sameDigestHex0(pccPackDigest, acceptRunPgenDigest),

    rowPackDigest,
    pccPackRowPackDigest: digestCanonical0(pccPack?.RowPack ?? null),
    rowPackLinkedToPCCPack: sameDigestHex0(rowPackDigest, digestCanonical0(pccPack?.RowPack ?? null)),

    localPackagesDigest,
    pccPackLocalPackagesDigest: digestCanonical0(pccPack?.LocalPackages ?? null),
    localPackagesLinkedToPCCPack: sameDigestHex0(localPackagesDigest, digestCanonical0(pccPack?.LocalPackages ?? null)),

    globalFirewallsDigest,
    pccPackGlobalFirewallsDigest: digestCanonical0(pccPack?.GlobalFirewalls ?? null),
    globalFirewallsLinkedToPCCPack: sameDigestHex0(globalFirewallsDigest, digestCanonical0(pccPack?.GlobalFirewalls ?? null)),

    globalProofDAGDigest,
    pccPackGlobalProofDAGDigest: digestCanonical0(pccPack?.GlobalProofDAG ?? null),
    globalProofDAGLinkedToPCCPack: sameDigestHex0(globalProofDAGDigest, digestCanonical0(pccPack?.GlobalProofDAG ?? null)),
  };
}

export async function CheckConcreteMaterializedGeneratedAcceptRun0(
  input,
  config = makeConcreteMaterializedGeneratedAcceptRunConfig0(),
) {
  const checker = 'CheckConcreteMaterializedGeneratedAcceptRun0';
  const ledger = [];
  const cfg = makeConcreteMaterializedGeneratedAcceptRunConfig0(config);
  const envelope = normalizeInput0(input);
  let checkPCCPackexpRecord = null;
  let materializedCheckPCCPackexpRecord = null;
  let generatedPCCPackexpRecord = null;
  let materializedGeneratedPCCPackexpEnvelope = null;
  let materializedCheckGeneratedPCCPackexpRecord = null;

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

  if (cfg.checkGeneratedAcceptRun === true) {
    const record = await CheckMaterializedGeneratedAcceptRun0(
      envelope.GeneratedAcceptRunEnvelope,
      cfg.generatedAcceptRunConfig ?? {},
    );
    const result = recordToValidation0(record, ['GeneratedAcceptRunEnvelope']);

    ledger.push({
      phase: 'CheckMaterializedGeneratedAcceptRun0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.GeneratedAcceptRun`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkConcretePCCPack === true) {
    const record = await CheckConcreteMaterializedPCCPack0(
      envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      cfg.concretePCCPackConfig ?? {},
    );
    const result = recordToValidation0(record, ['GeneratedAcceptRunEnvelope', 'MaterializedPCCPack']);

    ledger.push({
      phase: 'CheckConcreteMaterializedPCCPack0',
      status: result.ok ? 'pass' : 'fail',
      digest: record.Digest ?? record.digest ?? digestCanonical0(record),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.ConcretePCCPack`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }
  }

  if (cfg.checkPCCPackexp === true) {
    checkPCCPackexpRecord = await CheckPCCPackexp0(
      envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      cfg.checkPCCPackexpConfig ?? {},
    );
    const result = recordToValidation0(checkPCCPackexpRecord, ['GeneratedAcceptRunEnvelope', 'MaterializedPCCPack']);

    ledger.push({
      phase: 'CheckPCCPackexp0',
      status: result.ok ? 'pass' : 'fail',
      digest: digestFromRecord0(checkPCCPackexpRecord) ?? digestCanonical0(checkPCCPackexpRecord),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckPCCPackexp`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    const materializedRecord = validateMaterializedCheckPCCPackexpRecord0(
      envelope.CheckPCCPackexpRecord,
      checkPCCPackexpRecord,
    );

    ledger.push({
      phase: 'CheckPCCPackexpRecord',
      status: materializedRecord.ok ? 'pass' : 'fail',
      digest: digestCanonical0(materializedRecord.nf ?? materializedRecord.witness ?? null),
    });

    if (!materializedRecord.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckPCCPackexp`,
        path: materializedRecord.path,
        witness: materializedRecord.witness,
        ledger,
      });
    }

    materializedCheckPCCPackexpRecord = envelope.CheckPCCPackexpRecord;
  }

  if (cfg.checkGeneratedPCCPackexp === true) {
    generatedPCCPackexpRecord = await CheckGeneratedPCCPackexp0(
      envelope.GeneratedPCCPackexpEnvelope,
      cfg.generatedPCCPackexpConfig ?? {},
    );
    const result = recordToValidation0(generatedPCCPackexpRecord, ['GeneratedPCCPackexpEnvelope']);

    ledger.push({
      phase: 'CheckGeneratedPCCPackexp0',
      status: result.ok ? 'pass' : 'fail',
      digest: digestFromRecord0(generatedPCCPackexpRecord) ?? digestCanonical0(generatedPCCPackexpRecord),
    });

    if (!result.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.GeneratedPCCPackexp`,
        path: result.path,
        witness: result.witness,
        ledger,
      });
    }

    const generatedAlignment = validateGeneratedPCCPackexpEnvelope0({
      generatedPCCPackexpEnvelope: envelope.GeneratedPCCPackexpEnvelope,
      materializedPCCPack: envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      checkPCCPackexpRecord: envelope.CheckPCCPackexpRecord,
      generatedPCCPackexpRecord,
    });

    ledger.push({
      phase: 'GeneratedPCCPackexpEnvelope',
      status: generatedAlignment.ok ? 'pass' : 'fail',
      digest: digestCanonical0(generatedAlignment.nf ?? generatedAlignment.witness ?? null),
    });

    if (!generatedAlignment.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.GeneratedPCCPackexp`,
        path: generatedAlignment.path,
        witness: generatedAlignment.witness,
        ledger,
      });
    }

    const generatedRecordAlignment = validateMaterializedCheckGeneratedPCCPackexpRecord0(
      envelope.CheckGeneratedPCCPackexpRecord,
      generatedPCCPackexpRecord,
    );

    ledger.push({
      phase: 'CheckGeneratedPCCPackexpRecord',
      status: generatedRecordAlignment.ok ? 'pass' : 'fail',
      digest: digestCanonical0(generatedRecordAlignment.nf ?? generatedRecordAlignment.witness ?? null),
    });

    if (!generatedRecordAlignment.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.CheckGeneratedPCCPackexpRecord`,
        path: generatedRecordAlignment.path,
        witness: generatedRecordAlignment.witness,
        ledger,
      });
    }

    materializedGeneratedPCCPackexpEnvelope = envelope.GeneratedPCCPackexpEnvelope;
    materializedCheckGeneratedPCCPackexpRecord = envelope.CheckGeneratedPCCPackexpRecord;
  }

  const recomputedChain = summarizeConcreteGeneratedAcceptRunChain0(envelope.GeneratedAcceptRunEnvelope);

  if (cfg.checkConcreteChain === true) {
    const chain = validateConcreteChain0(envelope.ConcreteChain, recomputedChain);

    ledger.push({
      phase: 'concreteChain',
      status: chain.ok ? 'pass' : 'fail',
      digest: digestCanonical0(chain.nf ?? chain.witness ?? null),
    });

    if (!chain.ok) {
      return makeRejectRecord({
        checker,
        coord: `${checker}.concreteChain`,
        path: chain.path,
        witness: chain.witness,
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

  if (cfg.checkLinkage === true) {
    const linkage = validateLinkage0(envelope, recomputedChain);

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
    kind: 'ConcreteMaterializedGeneratedAcceptRun0NF',
    checker,
    version: CHECKER_VERSION,
    materializedPath: true,
    syntheticRunAll: false,

    concreteRows: recomputedChain.concreteRows,
    concreteLocalPackages: recomputedChain.concreteLocalPackages,
    concreteGlobalFirewalls: recomputedChain.concreteGlobalFirewalls,
    concreteGlobalProofDAG: recomputedChain.concreteGlobalProofDAG,

    concreteKBundle: recomputedChain.concreteKBundle,
    kBundleKernelRuleCoverageComplete: recomputedChain.kBundleKernelRuleCoverageComplete,
    kBundleSigmaProofRefsResolve: recomputedChain.kBundleSigmaProofRefsResolve,
    kBundleReflectionProofRefsResolve: recomputedChain.kBundleReflectionProofRefsResolve,

    concreteHardCheck: recomputedChain.concreteHardCheck,
    hardCheckerCoverageComplete: recomputedChain.hardCheckerCoverageComplete,
    hardRowKeyCoverageComplete: recomputedChain.hardRowKeyCoverageComplete,
    hardRoutePriorityComplete: recomputedChain.hardRoutePriorityComplete,
    hardProofRefPolicyComplete: recomputedChain.hardProofRefPolicyComplete,
    hardHashDisciplineComplete: recomputedChain.hardHashDisciplineComplete,
    hardNoMinCoverageComplete: recomputedChain.hardNoMinCoverageComplete,
    hardImportPolicyComplete: recomputedChain.hardImportPolicyComplete,
    hardReflectionPolicyComplete: recomputedChain.hardReflectionPolicyComplete,
    hardBoundsPolicyComplete: recomputedChain.hardBoundsPolicyComplete,
    hardDiagnosticsPolicyComplete: recomputedChain.hardDiagnosticsPolicyComplete,

    concreteFinalIntegration: recomputedChain.concreteFinalIntegration,
    finalIntegrationConcreteGlobalProofDAG: recomputedChain.finalIntegrationConcreteGlobalProofDAG,
    finalIntegrationGPackFieldCoverageComplete: recomputedChain.finalIntegrationGPackFieldCoverageComplete,
    finalIntegrationRowFamGCoverageComplete: recomputedChain.finalIntegrationRowFamGCoverageComplete,
    finalIntegrationUsesGPack: recomputedChain.finalIntegrationUsesGPack,
    rowFamGUsesGPack: recomputedChain.rowFamGUsesGPack,
    finalTheoremUsesFinalIntegration: recomputedChain.finalTheoremUsesFinalIntegration,
    rowFamFinalUsesFinalTheorem: recomputedChain.rowFamFinalUsesFinalTheorem,
    finalMatchUsesGPack: recomputedChain.finalMatchUsesGPack,
    satDecisionUsesGPack: recomputedChain.satDecisionUsesGPack,

    concretePCCPack: recomputedChain.concretePCCPack,
    concretePCCPackCoverageDigest: recomputedChain.concretePCCPackCoverageDigest,
    pccPackPublicConclusionOnlyAfterAcceptRun: recomputedChain.pccPackPublicConclusionOnlyAfterAcceptRun,
    pccPackLinkedToKBundle: recomputedChain.pccPackLinkedToKBundle,
    pccPackLinkedToHardCheck: recomputedChain.pccPackLinkedToHardCheck,
    pccPackLinkedToRows: recomputedChain.pccPackLinkedToRows,
    pccPackLinkedToLocalPackages: recomputedChain.pccPackLinkedToLocalPackages,
    pccPackLinkedToGlobalFirewalls: recomputedChain.pccPackLinkedToGlobalFirewalls,
    pccPackLinkedToGlobalProofDAG: recomputedChain.pccPackLinkedToGlobalProofDAG,
    pccPackLinkedToGPack: recomputedChain.pccPackLinkedToGPack,
    pccPackLinkedToFinalIntegration: recomputedChain.pccPackLinkedToFinalIntegration,
    pccPackLinkedToFinalTheorem: recomputedChain.pccPackLinkedToFinalTheorem,

    checkPCCPackexp: cfg.checkPCCPackexp === true,
    checkPCCPackexpRecordDigest: digestFromRecord0(checkPCCPackexpRecord),
    checkPCCPackexpRecordAccepted: checkPCCPackexpRecord === null ? null : checkPCCPackexpRecord.tag === 'accept',
    checkPCCPackexpRecordChecker: checkPCCPackexpRecord?.checker ?? null,
    checkPCCPackexpMaterializedRecordPresent: isPlainObject(materializedCheckPCCPackexpRecord),
    checkPCCPackexpMaterializedRecordDigest: digestFromRecord0(materializedCheckPCCPackexpRecord),
    checkPCCPackexpMaterializedRecordMatchesFresh: (
      materializedCheckPCCPackexpRecord === null
        ? null
        : sameDigestHex0(digestFromRecord0(materializedCheckPCCPackexpRecord), digestFromRecord0(checkPCCPackexpRecord))
    ),

    generatedPCCPackexp: cfg.checkGeneratedPCCPackexp === true,
    generatedPCCPackexpEnvelopePresent: isPlainObject(materializedGeneratedPCCPackexpEnvelope),
    generatedPCCPackexpEnvelopeDigest: (
      isPlainObject(materializedGeneratedPCCPackexpEnvelope)
        ? digestCanonical0(materializedGeneratedPCCPackexpEnvelope)
        : null
    ),
    generatedPCCPackexpRecordAccepted: (
      generatedPCCPackexpRecord === null
        ? null
        : generatedPCCPackexpRecord.tag === 'accept'
    ),
    generatedPCCPackexpRecordChecker: generatedPCCPackexpRecord?.checker ?? null,
    generatedPCCPackexpRecordDigest: digestFromRecord0(generatedPCCPackexpRecord),
    generatedPCCPackexpPackageMatchesAcceptRun: (
      isPlainObject(materializedGeneratedPCCPackexpEnvelope)
        ? sameDigestHex0(
            digestCanonical0(materializedGeneratedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope ?? null),
            digestCanonical0(envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack),
          )
        : null
    ),
    generatedPCCPackexpCheckRecordMatchesMaterialized: (
      isPlainObject(materializedGeneratedPCCPackexpEnvelope)
        ? sameDigestHex0(
            digestFromRecord0(materializedGeneratedPCCPackexpEnvelope.CheckPCCPackexpRecord),
            digestFromRecord0(envelope.CheckPCCPackexpRecord),
          )
        : null
    ),
    generatedPCCPackexpRecordMatchesMaterialized: (
      isPlainObject(materializedGeneratedPCCPackexpEnvelope) &&
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (
            sameDigestHex0(
              (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageDigest,
              digestCanonical0(materializedGeneratedPCCPackexpEnvelope.GeneratedPCCPack),
            ) &&
            sameDigestHex0(
              (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexpRecordDigest,
              digestFromRecord0(materializedGeneratedPCCPackexpEnvelope.CheckPCCPackexpRecord),
            )
          )
        : null
    ),
    checkGeneratedPCCPackexpRecordPresent: isPlainObject(materializedCheckGeneratedPCCPackexpRecord),
    checkGeneratedPCCPackexpRecordAccepted: (
      materializedCheckGeneratedPCCPackexpRecord === null
        ? null
        : materializedCheckGeneratedPCCPackexpRecord.tag === 'accept'
    ),
    checkGeneratedPCCPackexpRecordChecker: materializedCheckGeneratedPCCPackexpRecord?.checker ?? null,
    checkGeneratedPCCPackexpRecordDigest: digestFromRecord0(materializedCheckGeneratedPCCPackexpRecord),
    checkGeneratedPCCPackexpRecordDigestMatchesNF: (
      isPlainObject(materializedCheckGeneratedPCCPackexpRecord?.NF ?? materializedCheckGeneratedPCCPackexpRecord?.nf)
        ? sameDigestHex0(
            digestFromRecord0(materializedCheckGeneratedPCCPackexpRecord),
            digestCanonical0(materializedCheckGeneratedPCCPackexpRecord.NF ?? materializedCheckGeneratedPCCPackexpRecord.nf),
          )
        : null
    ),
    checkGeneratedPCCPackexpRecordMatchesFresh: (
      materializedCheckGeneratedPCCPackexpRecord === null
        ? null
        : sameDigestHex0(
            digestFromRecord0(materializedCheckGeneratedPCCPackexpRecord),
            digestFromRecord0(generatedPCCPackexpRecord),
          )
    ),

    generatedPCCPackexpBoot0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageBoot0 === true
        : null
    ),
    generatedPCCPackexpBoot0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0Accepted === true
        : null
    ),
    generatedPCCPackexpBoot0Kind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0Kind
        : null
    ),
    generatedPCCPackexpBoot0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0Digest
        : null
    ),
    generatedPCCPackexpBoot0CheckDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0CheckDigest
        : null
    ),
    generatedPCCPackexpBoot0CanonicalByteDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0CanonicalByteDigest
        : null
    ),
    generatedPCCPackexpBoot0RowCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0RowCount
        : null
    ),
    generatedPCCPackexpBoot0KernelRuleCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0KernelRuleCount
        : null
    ),
    generatedPCCPackexpBoot0JsonMaterialized: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0JsonMaterialized === true
        : null
    ),
    generatedPCCPackexpBoot0NoFixtureMarkers: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0NoFixtureMarkers === true
        : null
    ),
    generatedPCCPackexpBoot0BootBatchDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0BootBatchDigest
        : null
    ),
    generatedPCCPackexpBoot0BootAuditDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0BootAuditDigest
        : null
    ),
    generatedPCCPackexpBoot0LinkedToPCCPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0LinkedToPCCPack === true
        : null
    ),
    generatedPCCPackexpBoot0LinkedToCoreDigestMap: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0LinkedToCoreDigestMap === true
        : null
    ),

    generatedPCCPackexpBoot0B0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0Accepted === true
        : null
    ),
    generatedPCCPackexpBoot0B0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0Digest
        : null
    ),
    generatedPCCPackexpBoot0B0CoverageDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoverageDigest
        : null
    ),
    generatedPCCPackexpBoot0B0FamilyCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0FamilyCount
        : null
    ),
    generatedPCCPackexpBoot0B0RequiredFamilyCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0RequiredFamilyCount
        : null
    ),
    generatedPCCPackexpBoot0B0Families: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0Families
        : null
    ),
    generatedPCCPackexpBoot0B0AllRequiredFamiliesPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0AllRequiredFamiliesPresent === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversIface: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversIface === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversSched: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversSched === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversNF: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversNF === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversTruthEval: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversTruthEval === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversRel: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversRel === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversCharge: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversCharge === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversObl: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversObl === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversArith: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversArith === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversMode: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversMode === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversRoute: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversRoute === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversHash: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversHash === true
        : null
    ),
    generatedPCCPackexpBoot0B0CoversImport: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).boot0B0CoversImport === true
        : null
    ),

    generatedPCCPackexpKernelSeed0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageKernelSeed0 === true
        : null
    ),
    generatedPCCPackexpKernelSeed0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0Accepted === true
        : null
    ),
    generatedPCCPackexpKernelSeed0Kind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0Kind
        : null
    ),
    generatedPCCPackexpKernelSeed0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0Digest
        : null
    ),
    generatedPCCPackexpKernelSeed0RuleCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0RuleCount
        : null
    ),
    generatedPCCPackexpKernelSeed0RequiredRuleCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0RequiredRuleCount
        : null
    ),
    generatedPCCPackexpKernelSeed0Rules: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0Rules
        : null
    ),
    generatedPCCPackexpKernelSeed0AllRequiredRulesPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0AllRequiredRulesPresent === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasEq: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasEq === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasSubst: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasSubst === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasRecord: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasRecord === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasDAGInd: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasDAGInd === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasLedgerInd: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasLedgerInd === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasOblTopoInd: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasOblTopoInd === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasTraceInd: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasTraceInd === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasFiniteExhaust: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasFiniteExhaust === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasDPInd: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasDPInd === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasHall: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasHall === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasRankInd: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasRankInd === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasMinCounterexample: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasMinCounterexample === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasIntArith: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasIntArith === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasTransport: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasTransport === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasTruthVec: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasTruthVec === true
        : null
    ),
    generatedPCCPackexpKernelSeed0HasFiniteRel: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0HasFiniteRel === true
        : null
    ),
    generatedPCCPackexpKernelSeed0ProofNodeKindCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0ProofNodeKindCount
        : null
    ),
    generatedPCCPackexpKernelSeed0ProofNodeKinds: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0ProofNodeKinds
        : null
    ),
    generatedPCCPackexpKernelSeed0AllRequiredProofNodeKindsPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0AllRequiredProofNodeKindsPresent === true
        : null
    ),
    generatedPCCPackexpKernelSeed0ProofRefsRejectOpaque: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0ProofRefsRejectOpaque === true
        : null
    ),
    generatedPCCPackexpKernelSeed0ProofRefsTypedAcyclic: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0ProofRefsTypedAcyclic === true
        : null
    ),
    generatedPCCPackexpKernelSeed0ProofRefsHashIndependent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0ProofRefsHashIndependent === true
        : null
    ),
    generatedPCCPackexpKernelSeed0PiBootDigestMatches: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).kernelSeed0PiBootDigestMatches === true
        : null
    ),

    generatedPCCPackexpCodec0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageCodec0 === true
        : null
    ),
    generatedPCCPackexpCodec0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).codec0Accepted === true
        : null
    ),
    generatedPCCPackexpCodec0Kind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).codec0Kind
        : null
    ),
    generatedPCCPackexpCodec0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).codec0Digest
        : null
    ),
    generatedPCCPackexpCodec0Canonical: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).codec0Canonical === true
        : null
    ),
    generatedPCCPackexpCodec0NaturalEncoding: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).codec0NaturalEncoding
        : null
    ),
    generatedPCCPackexpCodec0IntegerEncoding: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).codec0IntegerEncoding
        : null
    ),
    generatedPCCPackexpCodec0StringEncoding: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).codec0StringEncoding
        : null
    ),
    generatedPCCPackexpCodec0TopLevelConsumesAllBytes: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).codec0TopLevelConsumesAllBytes === true
        : null
    ),
    generatedPCCPackexpCodec0NormalFormSerialization: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).codec0NormalFormSerialization
        : null
    ),
    generatedPCCPackexpCodec0PiBootDigestMatches: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).codec0PiBootDigestMatches === true
        : null
    ),

    generatedPCCPackexpDigest0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageDigest0 === true
        : null
    ),
    generatedPCCPackexpDigest0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).digest0Accepted === true
        : null
    ),
    generatedPCCPackexpDigest0Kind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).digest0Kind
        : null
    ),
    generatedPCCPackexpDigest0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).digest0Digest
        : null
    ),
    generatedPCCPackexpDigest0Alg: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).digest0Alg
        : null
    ),
    generatedPCCPackexpDigest0Bytes: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).digest0Bytes
        : null
    ),
    generatedPCCPackexpDigest0EqualityNotObjectEquality: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).digest0EqualityNotObjectEquality === true
        : null
    ),
    generatedPCCPackexpDigest0FullKeyComparisonAfterHashLookup: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).digest0FullKeyComparisonAfterHashLookup === true
        : null
    ),
    generatedPCCPackexpDigest0PiBootDigestMatches: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).digest0PiBootDigestMatches === true
        : null
    ),

    generatedPCCPackexpIfaceDict0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageIfaceDict0 === true
        : null
    ),
    generatedPCCPackexpIfaceDict0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).ifaceDict0Accepted === true
        : null
    ),
    generatedPCCPackexpIfaceDict0Kind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).ifaceDict0Kind
        : null
    ),
    generatedPCCPackexpIfaceDict0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).ifaceDict0Digest
        : null
    ),
    generatedPCCPackexpIfaceDict0ForbiddenSymbolCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).ifaceDict0ForbiddenSymbolCount
        : null
    ),
    generatedPCCPackexpIfaceDict0RequiredForbiddenSymbolsPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).ifaceDict0RequiredForbiddenSymbolsPresent === true
        : null
    ),
    generatedPCCPackexpIfaceDict0NoExecutableMinSymbols: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).ifaceDict0NoExecutableMinSymbols === true
        : null
    ),
    generatedPCCPackexpIfaceDict0PublicConstructorsPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).ifaceDict0PublicConstructorsPresent === true
        : null
    ),
    generatedPCCPackexpIfaceDict0CriticalKindsPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).ifaceDict0CriticalKindsPresent === true
        : null
    ),
    generatedPCCPackexpIfaceDict0RouteTokensPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).ifaceDict0RouteTokensPresent === true
        : null
    ),
    generatedPCCPackexpIfaceDict0PiBootDigestMatches: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).ifaceDict0PiBootDigestMatches === true
        : null
    ),

    generatedPCCPackexpSched0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageSched0 === true
        : null
    ),
    generatedPCCPackexpSched0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0Accepted === true
        : null
    ),
    generatedPCCPackexpSched0Kind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0Kind
        : null
    ),
    generatedPCCPackexpSched0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0Digest
        : null
    ),
    generatedPCCPackexpSched0CoreMatchesExpected: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0CoreMatchesExpected === true
        : null
    ),
    generatedPCCPackexpSched0CoreB0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0CoreB0
        : null
    ),
    generatedPCCPackexpSched0CoreK0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0CoreK0
        : null
    ),
    generatedPCCPackexpSched0CoreR0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0CoreR0
        : null
    ),
    generatedPCCPackexpSched0CoreH0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0CoreH0
        : null
    ),
    generatedPCCPackexpSched0CoreO0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0CoreO0
        : null
    ),
    generatedPCCPackexpSched0CoreRel0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0CoreRel0
        : null
    ),
    generatedPCCPackexpSched0ScaleFactorsPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0ScaleFactorsPresent === true
        : null
    ),
    generatedPCCPackexpSched0SelectorBoundsPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0SelectorBoundsPresent === true
        : null
    ),
    generatedPCCPackexpSched0SelectorBoundBH: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0SelectorBoundBH
        : null
    ),
    generatedPCCPackexpSched0SelectorBoundBTheta: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0SelectorBoundBTheta
        : null
    ),
    generatedPCCPackexpSched0PolynomialExponent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0PolynomialExponent
        : null
    ),
    generatedPCCPackexpSched0PiBootDigestMatches: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).sched0PiBootDigestMatches === true
        : null
    ),

    generatedPCCPackexpByteLang0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageByteLang0 === true
        : null
    ),
    generatedPCCPackexpByteLang0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0Accepted === true
        : null
    ),
    generatedPCCPackexpByteLang0Kind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0Kind
        : null
    ),
    generatedPCCPackexpByteLang0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0Digest
        : null
    ),
    generatedPCCPackexpByteLang0TagCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0TagCount
        : null
    ),
    generatedPCCPackexpByteLang0TagsUnique: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0TagsUnique === true
        : null
    ),
    generatedPCCPackexpByteLang0RequiredTagsPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0RequiredTagsPresent === true
        : null
    ),
    generatedPCCPackexpByteLang0SortCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0SortCount
        : null
    ),
    generatedPCCPackexpByteLang0RequiredSortsPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0RequiredSortsPresent === true
        : null
    ),
    generatedPCCPackexpByteLang0ConstructorCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0ConstructorCount
        : null
    ),
    generatedPCCPackexpByteLang0RequiredConstructorsPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0RequiredConstructorsPresent === true
        : null
    ),
    generatedPCCPackexpByteLang0RecordCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0RecordCount
        : null
    ),
    generatedPCCPackexpByteLang0RequiredRecordAritiesPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0RequiredRecordAritiesPresent === true
        : null
    ),
    generatedPCCPackexpByteLang0PiBootDigestMatches: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).byteLang0PiBootDigestMatches === true
        : null
    ),

    generatedPCCPackexpBootAudit0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageBootAudit0 === true
        : null
    ),
    generatedPCCPackexpBootAudit0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0Accepted === true
        : null
    ),
    generatedPCCPackexpBootAudit0Checker: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0Checker
        : null
    ),
    generatedPCCPackexpBootAudit0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0Digest
        : null
    ),
    generatedPCCPackexpBootAudit0DigestMatchesNF: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0DigestMatchesNF === true
        : null
    ),
    generatedPCCPackexpBootAudit0NFKind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0NFKind
        : null
    ),
    generatedPCCPackexpBootAudit0SuiteId: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0SuiteId
        : null
    ),
    generatedPCCPackexpBootAudit0CaseCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0CaseCount
        : null
    ),
    generatedPCCPackexpBootAudit0PositiveCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0PositiveCount
        : null
    ),
    generatedPCCPackexpBootAudit0NegativeCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0NegativeCount
        : null
    ),
    generatedPCCPackexpBootAudit0CoversB0Accept: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0CoversB0Accept === true
        : null
    ),
    generatedPCCPackexpBootAudit0CoversB0MissingCoverageReject: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0CoversB0MissingCoverageReject === true
        : null
    ),
    generatedPCCPackexpBootAudit0CoversB0HashKeyTamperReject: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).bootAudit0CoversB0HashKeyTamperReject === true
        : null
    ),

    generatedPCCPackexpPiBoot0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackagePiBoot0 === true
        : null
    ),
    generatedPCCPackexpPiBoot0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0Accepted === true
        : null
    ),
    generatedPCCPackexpPiBoot0Kind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0Kind
        : null
    ),
    generatedPCCPackexpPiBoot0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0Digest
        : null
    ),
    generatedPCCPackexpPiBoot0Materialized: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0Materialized === true
        : null
    ),
    generatedPCCPackexpPiBoot0ExternalJson: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0ExternalJson === true
        : null
    ),
    generatedPCCPackexpPiBoot0RefCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0RefCount
        : null
    ),
    generatedPCCPackexpPiBoot0AllBootRefsPresent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0AllBootRefsPresent === true
        : null
    ),
    generatedPCCPackexpPiBoot0RefsMatchBootObjects: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0RefsMatchBootObjects === true
        : null
    ),
    generatedPCCPackexpPiBoot0RefsIncludeByteLang0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0RefsIncludeByteLang0 === true
        : null
    ),
    generatedPCCPackexpPiBoot0RefsIncludeCodec0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0RefsIncludeCodec0 === true
        : null
    ),
    generatedPCCPackexpPiBoot0RefsIncludeDigest0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0RefsIncludeDigest0 === true
        : null
    ),
    generatedPCCPackexpPiBoot0RefsIncludeIfaceDict0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0RefsIncludeIfaceDict0 === true
        : null
    ),
    generatedPCCPackexpPiBoot0RefsIncludeSched0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0RefsIncludeSched0 === true
        : null
    ),
    generatedPCCPackexpPiBoot0RefsIncludeKernelSeed0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0RefsIncludeKernelSeed0 === true
        : null
    ),
    generatedPCCPackexpPiBoot0RefsIncludeB0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0RefsIncludeB0 === true
        : null
    ),
    generatedPCCPackexpPiBoot0RefsIncludeBootAudit0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).piBoot0RefsIncludeBootAudit0 === true
        : null
    ),

    generatedPCCPackexpConcreteKBundle0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageConcreteKBundle0 === true
        : null
    ),
    generatedPCCPackexpConcreteKBundle0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0Accepted === true
        : null
    ),
    generatedPCCPackexpConcreteKBundle0Checker: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0Checker
        : null
    ),
    generatedPCCPackexpConcreteKBundle0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0Digest
        : null
    ),
    generatedPCCPackexpConcreteKBundle0MaterializedKBundleDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0MaterializedKBundleDigest
        : null
    ),
    generatedPCCPackexpConcreteKBundle0BootDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0BootDigest
        : null
    ),
    generatedPCCPackexpConcreteKBundle0KImplDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0KImplDigest
        : null
    ),
    generatedPCCPackexpConcreteKBundle0K0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0K0Digest
        : null
    ),
    generatedPCCPackexpConcreteKBundle0SigmaDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0SigmaDigest
        : null
    ),
    generatedPCCPackexpConcreteKBundle0ReflectionDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0ReflectionDigest
        : null
    ),
    generatedPCCPackexpConcreteKBundle0ProofInventoryDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0ProofInventoryDigest
        : null
    ),
    generatedPCCPackexpConcreteKBundle0KernelRuleCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0KernelRuleCount
        : null
    ),
    generatedPCCPackexpConcreteKBundle0ConformanceNodeCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0ConformanceNodeCount
        : null
    ),
    generatedPCCPackexpConcreteKBundle0KernelRuleCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0KernelRuleCoverageComplete === true
        : null
    ),
    generatedPCCPackexpConcreteKBundle0SigmaTheoremCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0SigmaTheoremCount
        : null
    ),
    generatedPCCPackexpConcreteKBundle0SigmaCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0SigmaCoverageComplete === true
        : null
    ),
    generatedPCCPackexpConcreteKBundle0SigmaProofRefsResolve: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0SigmaProofRefsResolve === true
        : null
    ),
    generatedPCCPackexpConcreteKBundle0ReflectionCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0ReflectionCount
        : null
    ),
    generatedPCCPackexpConcreteKBundle0ReflectionCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0ReflectionCoverageComplete === true
        : null
    ),
    generatedPCCPackexpConcreteKBundle0ReflectionProofRefsResolve: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0ReflectionProofRefsResolve === true
        : null
    ),
    generatedPCCPackexpConcreteKBundle0NoOpaqueProofRefs: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0NoOpaqueProofRefs === true
        : null
    ),
    generatedPCCPackexpConcreteKBundle0NoExecutableMinSymbols: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0NoExecutableMinSymbols === true
        : null
    ),
    generatedPCCPackexpConcreteKBundle0LinkedToGeneratedBoot0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteKBundle0LinkedToGeneratedBoot0 === true
        : null
    ),

    generatedPCCPackexpConcreteHard0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageConcreteHard0 === true
        : null
    ),
    generatedPCCPackexpConcreteHard0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0Accepted === true
        : null
    ),
    generatedPCCPackexpConcreteHard0Checker: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0Checker
        : null
    ),
    generatedPCCPackexpConcreteHard0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0Digest
        : null
    ),
    generatedPCCPackexpConcreteHard0MaterializedHardDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0MaterializedHardDigest
        : null
    ),
    generatedPCCPackexpConcreteHard0HardCheckDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0HardCheckDigest
        : null
    ),
    generatedPCCPackexpConcreteHard0CoverageDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0CoverageDigest
        : null
    ),
    generatedPCCPackexpConcreteHard0CheckerCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0CheckerCount
        : null
    ),
    generatedPCCPackexpConcreteHard0CheckerCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0CheckerCoverageComplete === true
        : null
    ),
    generatedPCCPackexpConcreteHard0RowKeyFieldCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0RowKeyFieldCount
        : null
    ),
    generatedPCCPackexpConcreteHard0RowKeyCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0RowKeyCoverageComplete === true
        : null
    ),
    generatedPCCPackexpConcreteHard0RoutePriorityComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0RoutePriorityComplete === true
        : null
    ),
    generatedPCCPackexpConcreteHard0ProofRefPolicyComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0ProofRefPolicyComplete === true
        : null
    ),
    generatedPCCPackexpConcreteHard0HashDisciplineComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0HashDisciplineComplete === true
        : null
    ),
    generatedPCCPackexpConcreteHard0NoMinCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0NoMinCoverageComplete === true
        : null
    ),
    generatedPCCPackexpConcreteHard0ForbiddenSymbolCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0ForbiddenSymbolCount
        : null
    ),
    generatedPCCPackexpConcreteHard0ImportPolicyComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0ImportPolicyComplete === true
        : null
    ),
    generatedPCCPackexpConcreteHard0ForbiddenImportEdgeCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0ForbiddenImportEdgeCount
        : null
    ),
    generatedPCCPackexpConcreteHard0ReflectionPolicyComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0ReflectionPolicyComplete === true
        : null
    ),
    generatedPCCPackexpConcreteHard0BoundsPolicyComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0BoundsPolicyComplete === true
        : null
    ),
    generatedPCCPackexpConcreteHard0DiagnosticsPolicyComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0DiagnosticsPolicyComplete === true
        : null
    ),
    generatedPCCPackexpConcreteHard0LinkedToPCCPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteHard0LinkedToPCCPack === true
        : null
    ),

    generatedPCCPackexpConcreteRows0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageConcreteRows0 === true
        : null
    ),
    generatedPCCPackexpConcreteRows0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0Accepted === true
        : null
    ),
    generatedPCCPackexpConcreteRows0Checker: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0Checker
        : null
    ),
    generatedPCCPackexpConcreteRows0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0Digest
        : null
    ),
    generatedPCCPackexpConcreteRows0RowPackDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0RowPackDigest
        : null
    ),
    generatedPCCPackexpConcreteRows0RowPackObjectDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0RowPackObjectDigest
        : null
    ),
    generatedPCCPackexpConcreteRows0BootDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0BootDigest
        : null
    ),
    generatedPCCPackexpConcreteRows0IfaceHash: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0IfaceHash
        : null
    ),
    generatedPCCPackexpConcreteRows0SchedHash: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0SchedHash
        : null
    ),
    generatedPCCPackexpConcreteRows0RowCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0RowCount
        : null
    ),
    generatedPCCPackexpConcreteRows0BatchCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0BatchCount
        : null
    ),
    generatedPCCPackexpConcreteRows0FamilyCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0FamilyCount
        : null
    ),
    generatedPCCPackexpConcreteRows0ConcreteIfaceHash: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0ConcreteIfaceHash === true
        : null
    ),
    generatedPCCPackexpConcreteRows0SyntheticIfaceHashCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0SyntheticIfaceHashCount
        : null
    ),
    generatedPCCPackexpConcreteRows0ScaffoldMarkerCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0ScaffoldMarkerCount
        : null
    ),
    generatedPCCPackexpConcreteRows0LinkedToGeneratedBoot0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0LinkedToGeneratedBoot0 === true
        : null
    ),
    generatedPCCPackexpConcreteRows0LinkedToPCCPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteRows0LinkedToPCCPack === true
        : null
    ),

    generatedPCCPackexpConcreteGlobalProofDAG0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageConcreteGlobalProofDAG0 === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0Accepted === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0Checker: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0Checker
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0Digest
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0GlobalProofDAGDigest
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalProofDAGObjectDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0GlobalProofDAGObjectDigest
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0MaterializedGlobalProofDAGDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0MaterializedGlobalProofDAGDigest
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0KImplDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0KImplDigest
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0RowPackDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0RowPackDigest
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0LocalPackagesDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0LocalPackagesDigest
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0GlobalFirewallsDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0GlobalFirewallsDigest
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleProofInventoryDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0KBundleProofInventoryDigest
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleKernelRuleCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0KBundleKernelRuleCoverageComplete === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleSigmaProofRefsResolve: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0KBundleSigmaProofRefsResolve === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0KBundleReflectionProofRefsResolve: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0KBundleReflectionProofRefsResolve === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0NodeCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0NodeCount
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0NodeCountMinimum: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0NodeCountMinimum === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0FinalTheoremCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0FinalTheoremCount
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0FinalPackageSoundness: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0FinalPackageSoundness === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0FinalGeneratedPackageSufficiency: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0FinalGeneratedPackageSufficiency === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0IfaceHash: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0IfaceHash
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0SchedHash: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0SchedHash
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0IfaceMatchesRows: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0IfaceMatchesRows === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0SchedMatchesKImpl: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0SchedMatchesKImpl === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0SyntheticMarkerCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0SyntheticMarkerCount
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0ForbiddenMarkerCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0ForbiddenMarkerCount
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0NoForbiddenMarkers: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0NoForbiddenMarkers === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGeneratedBoot0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0LinkedToGeneratedBoot0 === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToKImpl: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0LinkedToKImpl === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToConcreteRows: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0LinkedToConcreteRows === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToLocalPackages: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0LinkedToLocalPackages === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToGlobalFirewalls: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0LinkedToGlobalFirewalls === true
        : null
    ),
    generatedPCCPackexpConcreteGlobalProofDAG0LinkedToPCCPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteGlobalProofDAG0LinkedToPCCPack === true
        : null
    ),

    generatedPCCPackexpConcreteFinalIntegration0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageConcreteFinalIntegration0 === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0Accepted === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0Checker: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0Checker
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0Digest
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAGDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0ConcreteGlobalProofDAGDigest
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0MaterializedFinalIntegrationDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0MaterializedFinalIntegrationDigest
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0GPackDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0GPackDigest
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0RowFamGDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0RowFamGDigest
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0FinalIntegrationDigest
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0FinalTheoremDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0FinalTheoremDigest
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0RowFamFinalDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0RowFamFinalDigest
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0ConcreteLinksDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0ConcreteLinksDigest
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalProofDAG: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0ConcreteGlobalProofDAG === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0ConcreteKBundle: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0ConcreteKBundle === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0ConcreteRows: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0ConcreteRows === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0ConcreteLocalPackages: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0ConcreteLocalPackages === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0ConcreteGlobalFirewalls: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0ConcreteGlobalFirewalls === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0KBundleKernelRuleCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0KBundleKernelRuleCoverageComplete === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0KBundleSigmaProofRefsResolve: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0KBundleSigmaProofRefsResolve === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0KBundleReflectionProofRefsResolve: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0KBundleReflectionProofRefsResolve === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0GPackFieldCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0GPackFieldCoverageComplete === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0RowFamGCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0RowFamGCoverageComplete === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0FinalIntegrationUsesGPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0FinalIntegrationUsesGPack === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0RowFamGUsesGPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0RowFamGUsesGPack === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0FinalTheoremUsesFinalIntegration: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0FinalTheoremUsesFinalIntegration === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0RowFamFinalUsesFinalTheorem: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0RowFamFinalUsesFinalTheorem === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0FinalMatchUsesGPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0FinalMatchUsesGPack === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0SATDecisionUsesGPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0SATDecisionUsesGPack === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0SyntheticMarkerCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0SyntheticMarkerCount
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0ForbiddenMarkerCount: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0ForbiddenMarkerCount
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0NoForbiddenMarkers: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0NoForbiddenMarkers === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0LinkedToGeneratedGlobalProofDAG: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0LinkedToGeneratedGlobalProofDAG === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0LinkedToGPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0LinkedToGPack === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamG: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0LinkedToRowFamG === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalIntegration: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0LinkedToFinalIntegration === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0LinkedToFinalTheorem: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0LinkedToFinalTheorem === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0LinkedToRowFamFinal: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0LinkedToRowFamFinal === true
        : null
    ),
    generatedPCCPackexpConcreteFinalIntegration0LinkedToPCCPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).concreteFinalIntegration0LinkedToPCCPack === true
        : null
    ),

    generatedPCCPackexpCheckPCCPackexp0: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).generatedPackageCheckPCCPackexp0 === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0Accepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0Accepted === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0Checker: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0Checker
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0Digest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0Digest
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0MaterializedPath: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0MaterializedPath === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0SyntheticRunAll: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0SyntheticRunAll === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PackageKind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PackageKind
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0MaterializedPCCPackKind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0MaterializedPCCPackKind
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackDigest
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0MaterializedPCCPackDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0MaterializedPCCPackDigest
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcretePCCPackRecordDigest
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageDigest: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcreteCoverageDigest
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PublicConclusionOnlyAfterAcceptRun: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PublicConclusionOnlyAfterAcceptRun === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PublicConclusionEmitted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PublicConclusionEmitted === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0NoPrematurePublicConclusion: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0NoPrematurePublicConclusion === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConditional: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ClaimBoundaryConditional === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryAntecedent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ClaimBoundaryAntecedent
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ClaimBoundaryConsequent: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ClaimBoundaryConsequent
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0GeneratedPackageImplication: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0GeneratedPackageImplication === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcretePCCPack === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcreteKBundle: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcreteKBundle === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcreteHardCheck: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcreteHardCheck === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcreteRows: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcreteRows === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcreteLocalPackages: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcreteLocalPackages === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalFirewalls: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcreteGlobalFirewalls === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcreteGlobalProofDAG: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcreteGlobalProofDAG === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcreteFinalIntegration: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcreteFinalIntegration === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0KBundleCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0KBundleCoverageComplete === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0HardCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0HardCoverageComplete === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0FinalIntegrationCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0FinalIntegrationCoverageComplete === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToKBundle: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackLinkedToKBundle === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToHardCheck: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackLinkedToHardCheck === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToRows: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackLinkedToRows === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToLocalPackages: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackLinkedToLocalPackages === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGlobalFirewalls: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackLinkedToGlobalFirewalls === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGlobalProofDAG: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackLinkedToGlobalProofDAG === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToGPack: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackLinkedToGPack === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToFinalIntegration: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackLinkedToFinalIntegration === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkedToFinalTheorem: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackLinkedToFinalTheorem === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0PCCPackLinkageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0PCCPackLinkageComplete === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcreteCoverageComplete: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcreteCoverageComplete === true
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordKind: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcretePCCPackRecordKind
        : null
    ),
    generatedPCCPackexpCheckPCCPackexp0ConcretePCCPackRecordAccepted: (
      isPlainObject(generatedPCCPackexpRecord?.NF ?? generatedPCCPackexpRecord?.nf)
        ? (generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf).checkPCCPackexp0ConcretePCCPackRecordAccepted === true
        : null
    ),

    rowsEnvelopeKind: recomputedChain.rowsEnvelopeKind,
    localPackagesEnvelopeKind: recomputedChain.localPackagesEnvelopeKind,
    globalFirewallsEnvelopeKind: recomputedChain.globalFirewallsEnvelopeKind,
    globalProofDAGEnvelopeKind: recomputedChain.globalProofDAGEnvelopeKind,
    kBundleEnvelopeKind: recomputedChain.kBundleEnvelopeKind,
    hardEnvelopeKind: recomputedChain.hardEnvelopeKind,
    finalIntegrationEnvelopeKind: recomputedChain.finalIntegrationEnvelopeKind,

    kBundleCoverageDigest: recomputedChain.kBundleCoverageDigest,
    hardCoverageDigest: recomputedChain.hardCoverageDigest,
    finalIntegrationLinksDigest: recomputedChain.finalIntegrationLinksDigest,

    pccPackLinkedToAcceptRun: recomputedChain.pccPackLinkedToAcceptRun,
    rowPackLinkedToPCCPack: recomputedChain.rowPackLinkedToPCCPack,
    localPackagesLinkedToPCCPack: recomputedChain.localPackagesLinkedToPCCPack,
    globalFirewallsLinkedToPCCPack: recomputedChain.globalFirewallsLinkedToPCCPack,
    globalProofDAGLinkedToPCCPack: recomputedChain.globalProofDAGLinkedToPCCPack,

    pccPackDigest: recomputedChain.pccPackDigest,
    acceptRunPgenDigest: recomputedChain.acceptRunPgenDigest,
    concreteChainDigest: digestCanonical0(recomputedChain),
    generatedAcceptRunEnvelopeDigest: digestCanonical0(envelope.GeneratedAcceptRunEnvelope),
    linkageDigest: digestCanonical0(envelope.Linkage ?? null),
  };

  return makeAcceptRecord({
    checker,
    nf,
    ledger,
  });
}

export async function writeConcreteMaterializedGeneratedAcceptRunFiles0(outDir, options = {}) {
  if (typeof outDir !== 'string' || outDir.length === 0) {
    throw new TypeError('writeConcreteMaterializedGeneratedAcceptRunFiles0 requires a non-empty output directory');
  }

  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0(options);
  const checked = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, options.checkConfig ?? {});

  await fs.mkdir(outDir, {
    recursive: true,
  });

  const envelopePath = path.join(outDir, 'ConcreteMaterializedGeneratedAcceptRun0.json');
  const generatedAcceptRunPath = path.join(outDir, 'MaterializedGeneratedAcceptRun0.json');
  const concreteChainPath = path.join(outDir, 'ConcreteGeneratedAcceptRunChain0.json');
  const checkPCCPackexpRecordPath = path.join(outDir, 'CheckPCCPackexp0.json');
  const generatedPCCPackexpEnvelopePath = path.join(outDir, 'GeneratedPCCPackexp0.json');
  const checkGeneratedPCCPackexpRecordPath = path.join(outDir, 'CheckGeneratedPCCPackexp0.json');
  const acceptRunPath = path.join(outDir, 'AcceptRun0.json');
  const pccPackPath = path.join(outDir, 'PCCPack0.json');
  const checkPath = path.join(outDir, 'ConcreteMaterializedGeneratedAcceptRun0.check.json');

  await writeJsonFile0(envelopePath, envelope);
  await writeJsonFile0(generatedAcceptRunPath, envelope.GeneratedAcceptRunEnvelope);
  await writeJsonFile0(concreteChainPath, envelope.ConcreteChain);
  await writeJsonFile0(checkPCCPackexpRecordPath, envelope.CheckPCCPackexpRecord);
  await writeJsonFile0(generatedPCCPackexpEnvelopePath, envelope.GeneratedPCCPackexpEnvelope);
  await writeJsonFile0(checkGeneratedPCCPackexpRecordPath, envelope.CheckGeneratedPCCPackexpRecord);
  await writeJsonFile0(acceptRunPath, envelope.GeneratedAcceptRunEnvelope.AcceptRun);
  await writeJsonFile0(pccPackPath, envelope.GeneratedAcceptRunEnvelope.AcceptRun.Pgen);
  await writeJsonFile0(checkPath, checked);

  return {
    envelope,
    checked,
    files: {
      envelopePath,
      generatedAcceptRunPath,
      concreteChainPath,
      checkPCCPackexpRecordPath,
      generatedPCCPackexpEnvelopePath,
      checkGeneratedPCCPackexpRecordPath,
      acceptRunPath,
      pccPackPath,
      checkPath,
    },
  };
}

function normalizeInput0(input) {
  if (isPlainObject(input) && input.kind === 'MaterializedGeneratedAcceptRun0') {
    const concreteChain = summarizeConcreteGeneratedAcceptRunChain0(input);

    return {
      kind: 'ConcreteMaterializedGeneratedAcceptRun0',
      version: CHECKER_VERSION,
      GeneratedAcceptRunEnvelope: input,
      ConcreteChain: concreteChain,
      Linkage: {
        kind: 'ConcreteMaterializedGeneratedAcceptRunLinkage0',
        version: CHECKER_VERSION,
        generatedAcceptRunEnvelopeDigest: digestCanonical0(input),
        materializedPCCPackDigest: digestCanonical0(input.MaterializedPCCPack),
        pccPackDigest: digestCanonical0(resolvePCCPack0(input.MaterializedPCCPack)),
        acceptRunDigest: digestCanonical0(input.AcceptRun),
        generatedPackageDigest: digestCanonical0(input.GeneratedPackage),
        checkPCCPackexpRecordDigest: null,
        concreteChainDigest: digestCanonical0(concreteChain),
      },
    };
  }

  return input;
}

function validateConfig0(config) {
  if (!isPlainObject(config)) {
    return validationReject0([], 'ConcreteMaterializedGeneratedAcceptRunConfig0 must be an object', {
      actual: typeof config,
    });
  }

  if (config.kind !== undefined && config.kind !== 'ConcreteMaterializedGeneratedAcceptRunConfig0') {
    return validationReject0(['kind'], 'ConcreteMaterializedGeneratedAcceptRunConfig0 kind mismatch', {
      actual: config.kind,
    });
  }

  if (config.version !== undefined && config.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedGeneratedAcceptRunConfig0 version must be ${CHECKER_VERSION} when present`, {
      actual: config.version,
    });
  }

  for (const field of [
    'checkGeneratedAcceptRun',
    'checkConcretePCCPack',
    'checkPCCPackexp',
    'checkGeneratedPCCPackexp',
    'checkConcreteChain',
    'checkJsonMaterialized',
    'checkLinkage',
  ]) {
    if (typeof config[field] !== 'boolean') {
      return validationReject0([field], `ConcreteMaterializedGeneratedAcceptRunConfig0 ${field} must be boolean`, {
        actual: config[field],
      });
    }
  }

  if (!isPlainObject(config.generatedAcceptRunConfig)) {
    return validationReject0(['generatedAcceptRunConfig'], 'generatedAcceptRunConfig must be an object', {
      actual: typeof config.generatedAcceptRunConfig,
    });
  }

  if (!isPlainObject(config.concretePCCPackConfig)) {
    return validationReject0(['concretePCCPackConfig'], 'concretePCCPackConfig must be an object', {
      actual: typeof config.concretePCCPackConfig,
    });
  }

  if (!isPlainObject(config.checkPCCPackexpConfig)) {
    return validationReject0(['checkPCCPackexpConfig'], 'checkPCCPackexpConfig must be an object', {
      actual: typeof config.checkPCCPackexpConfig,
    });
  }

  if (!isPlainObject(config.generatedPCCPackexpConfig)) {
    return validationReject0(['generatedPCCPackexpConfig'], 'generatedPCCPackexpConfig must be an object', {
      actual: typeof config.generatedPCCPackexpConfig,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedGeneratedAcceptRunConfig0NF',
  });
}

function validateShape0(envelope) {
  if (!isPlainObject(envelope)) {
    return validationReject0([], 'ConcreteMaterializedGeneratedAcceptRun0 must be an object', {
      actual: typeof envelope,
    });
  }

  if (envelope.kind !== undefined && envelope.kind !== 'ConcreteMaterializedGeneratedAcceptRun0') {
    return validationReject0(['kind'], 'ConcreteMaterializedGeneratedAcceptRun0 kind mismatch', {
      actual: envelope.kind,
    });
  }

  if (envelope.version !== undefined && envelope.version !== CHECKER_VERSION) {
    return validationReject0(['version'], `ConcreteMaterializedGeneratedAcceptRun0 version must be ${CHECKER_VERSION} when present`, {
      actual: envelope.version,
    });
  }

  if (!isPlainObject(envelope.GeneratedAcceptRunEnvelope)) {
    return validationReject0(['GeneratedAcceptRunEnvelope'], 'ConcreteMaterializedGeneratedAcceptRun0 must include GeneratedAcceptRunEnvelope', {
      actual: typeof envelope.GeneratedAcceptRunEnvelope,
    });
  }

  if (!isPlainObject(envelope.ConcreteChain)) {
    return validationReject0(['ConcreteChain'], 'ConcreteMaterializedGeneratedAcceptRun0 must include ConcreteChain', {
      actual: typeof envelope.ConcreteChain,
    });
  }

  return validationAccept0({
    kind: 'ConcreteMaterializedGeneratedAcceptRunShape0NF',
  });
}

function validateConcreteChain0(actual, expected) {
  if (stableStringify0(actual) !== stableStringify0(expected)) {
    return validationReject0(['ConcreteChain'], 'ConcreteChain summary must match recomputed generated accept-run chain', {
      expectedDigest: digestCanonical0(expected),
      actualDigest: digestCanonical0(actual),
    });
  }

  const requiredTrue = [
    'concreteRows',
    'concreteLocalPackages',
    'concreteGlobalFirewalls',
    'concreteGlobalProofDAG',

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

    'concreteFinalIntegration',
    'finalIntegrationConcreteGlobalProofDAG',
    'finalIntegrationGPackFieldCoverageComplete',
    'finalIntegrationRowFamGCoverageComplete',
    'finalIntegrationUsesGPack',
    'rowFamGUsesGPack',
    'finalTheoremUsesFinalIntegration',
    'rowFamFinalUsesFinalTheorem',
    'finalMatchUsesGPack',
    'satDecisionUsesGPack',

    'concretePCCPack',
    'pccPackPublicConclusionOnlyAfterAcceptRun',
    'pccPackLinkedToKBundle',
    'pccPackLinkedToHardCheck',
    'pccPackLinkedToRows',
    'pccPackLinkedToLocalPackages',
    'pccPackLinkedToGlobalFirewalls',
    'pccPackLinkedToGlobalProofDAG',
    'pccPackLinkedToGPack',
    'pccPackLinkedToFinalIntegration',
    'pccPackLinkedToFinalTheorem',

    'pccPackLinkedToAcceptRun',
    'rowPackLinkedToPCCPack',
    'localPackagesLinkedToPCCPack',
    'globalFirewallsLinkedToPCCPack',
    'globalProofDAGLinkedToPCCPack',
  ];

  for (const field of requiredTrue) {
    if (expected[field] !== true) {
      return validationReject0(['ConcreteChain', field], `Concrete generated accept-run chain must certify ${field}`, {
        actual: expected[field],
      });
    }
  }

  return validationAccept0({
    kind: 'ConcreteGeneratedAcceptRunChain0NF',
    concreteChainDigest: digestCanonical0(expected),
    pccPackDigest: expected.pccPackDigest,
  });
}

function validateJsonMaterialized0(value) {
  let bytes;
  let parsed;

  try {
    bytes = stableStringify0(value);
    parsed = JSON.parse(bytes);
  } catch (error) {
    return validationReject0(['ConcreteMaterializedGeneratedAcceptRun0'], 'ConcreteMaterializedGeneratedAcceptRun0 must serialize and parse as JSON', {
      error: error.message,
    });
  }

  const reparsedBytes = stableStringify0(parsed);

  if (reparsedBytes !== bytes) {
    return validationReject0(['ConcreteMaterializedGeneratedAcceptRun0'], 'ConcreteMaterializedGeneratedAcceptRun0 canonical JSON bytes must roundtrip', {
      expectedDigest: digestCanonical0(value),
      actualDigest: digestCanonical0(parsed),
    });
  }

  return validationAccept0({
    kind: 'ConcreteGeneratedAcceptRunJson0NF',
    byteLength: bytes.length,
    envelopeDigest: digestCanonical0(value),
  });
}

function validateMaterializedCheckPCCPackexpRecord0(actual, expected) {
  if (!isPlainObject(actual)) {
    return validationReject0(['CheckPCCPackexpRecord'], 'ConcreteMaterializedGeneratedAcceptRun0 must include CheckPCCPackexpRecord', {
      actual: typeof actual,
    });
  }

  if (actual.tag !== 'accept') {
    return validationReject0(['CheckPCCPackexpRecord', 'tag'], 'CheckPCCPackexpRecord must be accepted', {
      actual: actual.tag,
    });
  }

  if (actual.checker !== 'CheckPCCPackexp0') {
    return validationReject0(['CheckPCCPackexpRecord', 'checker'], 'CheckPCCPackexpRecord checker mismatch', {
      actual: actual.checker,
    });
  }

  const actualNF = actual.NF ?? actual.nf;
  const expectedNF = expected?.NF ?? expected?.nf;

  if (!isPlainObject(actualNF)) {
    return validationReject0(['CheckPCCPackexpRecord', 'NF'], 'CheckPCCPackexpRecord must expose NF', {
      actual: typeof actualNF,
    });
  }

  if (!isPlainObject(expectedNF)) {
    return validationReject0(['CheckPCCPackexpRecord'], 'fresh CheckPCCPackexp0 record must expose NF', {
      actual: typeof expectedNF,
    });
  }

  const actualDigest = digestFromRecord0(actual);
  const actualNFDigest = digestCanonical0(actualNF);

  if (!sameDigestHex0(actualDigest, actualNFDigest)) {
    return validationReject0(['CheckPCCPackexpRecord', 'Digest'], 'CheckPCCPackexpRecord Digest must match its NF', {
      expected: actualNFDigest,
      actual: actualDigest,
    });
  }

  if (stableStringify0(actualNF) !== stableStringify0(expectedNF)) {
    return validationReject0(['CheckPCCPackexpRecord', 'NF'], 'materialized CheckPCCPackexpRecord must match fresh CheckPCCPackexp0 replay', {
      expectedDigest: digestCanonical0(expectedNF),
      actualDigest: digestCanonical0(actualNF),
    });
  }

  if (!sameDigestHex0(actualDigest, digestFromRecord0(expected))) {
    return validationReject0(['CheckPCCPackexpRecord', 'Digest'], 'materialized CheckPCCPackexpRecord digest must match fresh replay digest', {
      expected: digestFromRecord0(expected),
      actual: actualDigest,
    });
  }

  return validationAccept0({
    kind: 'ConcreteGeneratedAcceptRunCheckPCCPackexpRecord0NF',
    checkPCCPackexpRecordDigest: actualDigest,
  });
}

function validateGeneratedPCCPackexpEnvelope0({
  generatedPCCPackexpEnvelope,
  materializedPCCPack,
  checkPCCPackexpRecord,
  generatedPCCPackexpRecord,
}) {
  if (!isPlainObject(generatedPCCPackexpEnvelope)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope'], 'ConcreteMaterializedGeneratedAcceptRun0 must include GeneratedPCCPackexpEnvelope', {
      actual: typeof generatedPCCPackexpEnvelope,
    });
  }

  if (!isPlainObject(generatedPCCPackexpEnvelope.GeneratedPCCPack)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'GeneratedPCCPack'], 'GeneratedPCCPackexpEnvelope must include GeneratedPCCPack', {
      actual: typeof generatedPCCPackexpEnvelope.GeneratedPCCPack,
    });
  }

  if (!isPlainObject(generatedPCCPackexpEnvelope.CheckPCCPackexpRecord)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'CheckPCCPackexpRecord'], 'GeneratedPCCPackexpEnvelope must include CheckPCCPackexpRecord', {
      actual: typeof generatedPCCPackexpEnvelope.CheckPCCPackexpRecord,
    });
  }

  if (generatedPCCPackexpRecord?.tag !== 'accept') {
    return validationReject0(['GeneratedPCCPackexpEnvelope'], 'CheckGeneratedPCCPackexp0 record must be accepted', {
      actual: generatedPCCPackexpRecord?.tag ?? null,
    });
  }

  if (!sameDigestHex0(
    digestCanonical0(generatedPCCPackexpEnvelope.GeneratedPCCPack.MaterializedPCCPackEnvelope ?? null),
    digestCanonical0(materializedPCCPack),
  )) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'GeneratedPCCPack'], 'GeneratedPCCPackexpEnvelope package must match accept-run materialized package', {
      expected: digestCanonical0(materializedPCCPack),
      actual: digestCanonical0(generatedPCCPackexpEnvelope.GeneratedPCCPack.MaterializedPCCPackEnvelope ?? null),
    });
  }

  if (!sameDigestHex0(
    digestFromRecord0(generatedPCCPackexpEnvelope.CheckPCCPackexpRecord),
    digestFromRecord0(checkPCCPackexpRecord),
  )) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'CheckPCCPackexpRecord'], 'GeneratedPCCPackexpEnvelope CheckPCCPackexpRecord must match accept-run record', {
      expected: digestFromRecord0(checkPCCPackexpRecord),
      actual: digestFromRecord0(generatedPCCPackexpEnvelope.CheckPCCPackexpRecord),
    });
  }

  const generatedNF = generatedPCCPackexpRecord.NF ?? generatedPCCPackexpRecord.nf;

  if (!sameDigestHex0(
    generatedNF?.generatedPackageDigest ?? null,
    digestCanonical0(generatedPCCPackexpEnvelope.GeneratedPCCPack),
  )) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'GeneratedPCCPack'], 'CheckGeneratedPCCPackexp0 NF must digest the materialized generated package', {
      expected: digestCanonical0(generatedPCCPackexpEnvelope.GeneratedPCCPack),
      actual: generatedNF?.generatedPackageDigest ?? null,
    });
  }

  if (!sameDigestHex0(
    generatedNF?.checkPCCPackexpRecordDigest ?? null,
    digestFromRecord0(checkPCCPackexpRecord),
  )) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'CheckPCCPackexpRecord'], 'CheckGeneratedPCCPackexp0 NF must digest the materialized CheckPCCPackexpRecord', {
      expected: digestFromRecord0(checkPCCPackexpRecord),
      actual: generatedNF?.checkPCCPackexpRecordDigest ?? null,
    });
  }

  for (const field of [
    'generatedPackageBoot0',
    'boot0Accepted',
    'boot0JsonMaterialized',
    'boot0NoFixtureMarkers',
    'boot0LinkedToPCCPack',
    'boot0LinkedToCoreDigestMap',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.boot0Kind !== 'Boot0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'boot0Kind'], 'GeneratedPCCPackexp0 NF must certify Boot0 kind', {
      actual: generatedNF.boot0Kind,
    });
  }

  if (!(typeof generatedNF.boot0RowCount === 'number' && generatedNF.boot0RowCount > 0)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'boot0RowCount'], 'GeneratedPCCPackexp0 NF must certify nonempty Boot0 row batch', {
      actual: generatedNF.boot0RowCount,
    });
  }

  if (!(typeof generatedNF.boot0KernelRuleCount === 'number' && generatedNF.boot0KernelRuleCount > 0)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'boot0KernelRuleCount'], 'GeneratedPCCPackexp0 NF must certify nonempty KernelSeed0 rule set', {
      actual: generatedNF.boot0KernelRuleCount,
    });
  }

  for (const field of [
    'boot0B0Accepted',
    'boot0B0AllRequiredFamiliesPresent',
    'boot0B0CoversIface',
    'boot0B0CoversSched',
    'boot0B0CoversNF',
    'boot0B0CoversTruthEval',
    'boot0B0CoversRel',
    'boot0B0CoversCharge',
    'boot0B0CoversObl',
    'boot0B0CoversArith',
    'boot0B0CoversMode',
    'boot0B0CoversRoute',
    'boot0B0CoversHash',
    'boot0B0CoversImport',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (!(typeof generatedNF.boot0B0FamilyCount === 'number' && generatedNF.boot0B0FamilyCount >= 12)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'boot0B0FamilyCount'], 'GeneratedPCCPackexp0 NF must certify complete B0 family count', {
      actual: generatedNF.boot0B0FamilyCount,
    });
  }

  if (!(typeof generatedNF.boot0B0RequiredFamilyCount === 'number' && generatedNF.boot0B0RequiredFamilyCount === 12)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'boot0B0RequiredFamilyCount'], 'GeneratedPCCPackexp0 NF must certify expected B0 required family count', {
      actual: generatedNF.boot0B0RequiredFamilyCount,
    });
  }

  if (!Array.isArray(generatedNF.boot0B0Families)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'boot0B0Families'], 'GeneratedPCCPackexp0 NF must expose B0 family list', {
      actual: typeof generatedNF.boot0B0Families,
    });
  }

  for (const family of [
    'BIface',
    'BSched',
    'BNF',
    'BTruthEval',
    'BRel',
    'BCharge',
    'BObl',
    'BArith',
    'BMode',
    'BRoute',
    'BHash',
    'BImport',
  ]) {
    if (!generatedNF.boot0B0Families.includes(family)) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'boot0B0Families'], 'GeneratedPCCPackexp0 NF B0 family list is missing a required family', {
        family,
        actual: generatedNF.boot0B0Families,
      });
    }
  }

  if (!sameDigestHex0(generatedNF.boot0B0Digest, generatedNF.boot0BootBatchDigest)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'boot0B0Digest'], 'GeneratedPCCPackexp0 NF B0 digest must match Boot0 boot-batch digest', {
      expected: generatedNF.boot0BootBatchDigest,
      actual: generatedNF.boot0B0Digest,
    });
  }

  for (const field of [
    'generatedPackageKernelSeed0',
    'kernelSeed0Accepted',
    'kernelSeed0AllRequiredRulesPresent',
    'kernelSeed0HasEq',
    'kernelSeed0HasSubst',
    'kernelSeed0HasRecord',
    'kernelSeed0HasDAGInd',
    'kernelSeed0HasLedgerInd',
    'kernelSeed0HasOblTopoInd',
    'kernelSeed0HasTraceInd',
    'kernelSeed0HasFiniteExhaust',
    'kernelSeed0HasDPInd',
    'kernelSeed0HasHall',
    'kernelSeed0HasRankInd',
    'kernelSeed0HasMinCounterexample',
    'kernelSeed0HasIntArith',
    'kernelSeed0HasTransport',
    'kernelSeed0HasTruthVec',
    'kernelSeed0HasFiniteRel',
    'kernelSeed0AllRequiredProofNodeKindsPresent',
    'kernelSeed0ProofRefsRejectOpaque',
    'kernelSeed0ProofRefsTypedAcyclic',
    'kernelSeed0ProofRefsHashIndependent',
    'kernelSeed0PiBootDigestMatches',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.kernelSeed0Kind !== 'KernelSeed0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'kernelSeed0Kind'], 'GeneratedPCCPackexp0 NF must certify KernelSeed0 kind', {
      actual: generatedNF.kernelSeed0Kind,
    });
  }

  if (!(typeof generatedNF.kernelSeed0RuleCount === 'number' && generatedNF.kernelSeed0RuleCount === 16)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'kernelSeed0RuleCount'], 'GeneratedPCCPackexp0 NF must certify complete KernelSeed0 primitive rule count', {
      actual: generatedNF.kernelSeed0RuleCount,
    });
  }

  if (!(typeof generatedNF.kernelSeed0RequiredRuleCount === 'number' && generatedNF.kernelSeed0RequiredRuleCount === 16)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'kernelSeed0RequiredRuleCount'], 'GeneratedPCCPackexp0 NF must certify expected KernelSeed0 required rule count', {
      actual: generatedNF.kernelSeed0RequiredRuleCount,
    });
  }

  if (!Array.isArray(generatedNF.kernelSeed0Rules)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'kernelSeed0Rules'], 'GeneratedPCCPackexp0 NF must expose KernelSeed0 rule list', {
      actual: typeof generatedNF.kernelSeed0Rules,
    });
  }

  for (const rule of [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
    'LedgerInd',
    'OblTopoInd',
    'TraceInd',
    'FiniteExhaust',
    'DPInd',
    'Hall',
    'RankInd',
    'MinCounterexample',
    'IntArith',
    'Transport',
    'TruthVec',
    'FiniteRel',
  ]) {
    if (!generatedNF.kernelSeed0Rules.includes(rule)) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'kernelSeed0Rules'], 'GeneratedPCCPackexp0 NF KernelSeed0 rule list is missing a required primitive rule', {
        rule,
        actual: generatedNF.kernelSeed0Rules,
      });
    }
  }

  if (!Array.isArray(generatedNF.kernelSeed0ProofNodeKinds)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'kernelSeed0ProofNodeKinds'], 'GeneratedPCCPackexp0 NF must expose KernelSeed0 proof node kinds', {
      actual: typeof generatedNF.kernelSeed0ProofNodeKinds,
    });
  }

  for (const proofNodeKind of [
    'PrimitiveRule',
    'SigmaInstance',
    'ReflectionInstance',
    'RowProof',
    'PackageTheorem',
  ]) {
    if (!generatedNF.kernelSeed0ProofNodeKinds.includes(proofNodeKind)) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'kernelSeed0ProofNodeKinds'], 'GeneratedPCCPackexp0 NF KernelSeed0 proof node kinds are incomplete', {
        proofNodeKind,
        actual: generatedNF.kernelSeed0ProofNodeKinds,
      });
    }
  }

  const generatedKernelSeed0 = generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.MaterializedBoot0?.KernelSeed0 ?? null;

  if (!sameDigestHex0(generatedNF.kernelSeed0Digest, digestCanonical0(generatedKernelSeed0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'kernelSeed0Digest'], 'GeneratedPCCPackexp0 NF kernelSeed0Digest must match generated package KernelSeed0 bytes', {
      expected: digestCanonical0(generatedKernelSeed0),
      actual: generatedNF.kernelSeed0Digest,
    });
  }

  for (const field of [
    'generatedPackageCodec0',
    'codec0Accepted',
    'codec0Canonical',
    'codec0TopLevelConsumesAllBytes',
    'codec0PiBootDigestMatches',
    'generatedPackageDigest0',
    'digest0Accepted',
    'digest0EqualityNotObjectEquality',
    'digest0FullKeyComparisonAfterHashLookup',
    'digest0PiBootDigestMatches',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.codec0Kind !== 'Codec0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'codec0Kind'], 'GeneratedPCCPackexp0 NF must certify Codec0 kind', {
      actual: generatedNF.codec0Kind,
    });
  }

  if (generatedNF.codec0NaturalEncoding !== 'u32be-length-shortest-big-endian-magnitude') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'codec0NaturalEncoding'], 'GeneratedPCCPackexp0 NF must certify canonical natural encoding', {
      actual: generatedNF.codec0NaturalEncoding,
    });
  }

  if (generatedNF.codec0IntegerEncoding !== 'sign-byte-plus-canonical-natural-no-negative-zero') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'codec0IntegerEncoding'], 'GeneratedPCCPackexp0 NF must certify canonical integer encoding', {
      actual: generatedNF.codec0IntegerEncoding,
    });
  }

  if (generatedNF.codec0StringEncoding !== 'utf8-nfc-length-prefixed') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'codec0StringEncoding'], 'GeneratedPCCPackexp0 NF must certify UTF-8 NFC length-prefixed string encoding', {
      actual: generatedNF.codec0StringEncoding,
    });
  }

  if (generatedNF.codec0NormalFormSerialization !== 'canonical-json-v0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'codec0NormalFormSerialization'], 'GeneratedPCCPackexp0 NF must certify canonical-json-v0 normal-form serialization', {
      actual: generatedNF.codec0NormalFormSerialization,
    });
  }

  if (generatedNF.digest0Kind !== 'Digest0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'digest0Kind'], 'GeneratedPCCPackexp0 NF must certify Digest0 kind', {
      actual: generatedNF.digest0Kind,
    });
  }

  if (generatedNF.digest0Alg !== 'SHA256') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'digest0Alg'], 'GeneratedPCCPackexp0 NF must certify SHA256 digest algorithm', {
      actual: generatedNF.digest0Alg,
    });
  }

  if (generatedNF.digest0Bytes !== 'canonical-json-v0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'digest0Bytes'], 'GeneratedPCCPackexp0 NF must certify canonical-json-v0 digest byte discipline', {
      actual: generatedNF.digest0Bytes,
    });
  }

  const generatedCodec0 = generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.MaterializedBoot0?.Codec0 ?? null;
  const generatedDigest0 = generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.MaterializedBoot0?.Digest0 ?? null;

  if (!sameDigestHex0(generatedNF.codec0Digest, digestCanonical0(generatedCodec0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'codec0Digest'], 'GeneratedPCCPackexp0 NF codec0Digest must match generated package Codec0 bytes', {
      expected: digestCanonical0(generatedCodec0),
      actual: generatedNF.codec0Digest,
    });
  }

  if (!sameDigestHex0(generatedNF.digest0Digest, digestCanonical0(generatedDigest0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'digest0Digest'], 'GeneratedPCCPackexp0 NF digest0Digest must match generated package Digest0 bytes', {
      expected: digestCanonical0(generatedDigest0),
      actual: generatedNF.digest0Digest,
    });
  }

  for (const field of [
    'generatedPackageIfaceDict0',
    'ifaceDict0Accepted',
    'ifaceDict0RequiredForbiddenSymbolsPresent',
    'ifaceDict0NoExecutableMinSymbols',
    'ifaceDict0PublicConstructorsPresent',
    'ifaceDict0CriticalKindsPresent',
    'ifaceDict0RouteTokensPresent',
    'ifaceDict0PiBootDigestMatches',
    'generatedPackageSched0',
    'sched0Accepted',
    'sched0CoreMatchesExpected',
    'sched0ScaleFactorsPresent',
    'sched0SelectorBoundsPresent',
    'sched0PiBootDigestMatches',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.ifaceDict0Kind !== 'IfaceDict0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'ifaceDict0Kind'], 'GeneratedPCCPackexp0 NF must certify IfaceDict0 kind', {
      actual: generatedNF.ifaceDict0Kind,
    });
  }

  if (!(typeof generatedNF.ifaceDict0ForbiddenSymbolCount === 'number' && generatedNF.ifaceDict0ForbiddenSymbolCount >= 11)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'ifaceDict0ForbiddenSymbolCount'], 'GeneratedPCCPackexp0 NF must certify hidden-minimization forbidden symbol inventory', {
      actual: generatedNF.ifaceDict0ForbiddenSymbolCount,
    });
  }

  if (generatedNF.sched0Kind !== 'Sched0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'sched0Kind'], 'GeneratedPCCPackexp0 NF must certify Sched0 kind', {
      actual: generatedNF.sched0Kind,
    });
  }

  const expectedCore = {
    sched0CoreB0: 64,
    sched0CoreK0: 512,
    sched0CoreR0: 64,
    sched0CoreH0: 128,
    sched0CoreO0: 64,
    sched0CoreRel0: 16,
  };

  for (const [field, expected] of Object.entries(expectedCore)) {
    if (generatedNF[field] !== expected) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], 'GeneratedPCCPackexp0 NF must certify fixed schedule core constants', {
        expected,
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.sched0SelectorBoundBH !== 8) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'sched0SelectorBoundBH'], 'GeneratedPCCPackexp0 NF must certify selector bound bH', {
      expected: 8,
      actual: generatedNF.sched0SelectorBoundBH,
    });
  }

  if (generatedNF.sched0SelectorBoundBTheta !== 12) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'sched0SelectorBoundBTheta'], 'GeneratedPCCPackexp0 NF must certify selector bound bTheta', {
      expected: 12,
      actual: generatedNF.sched0SelectorBoundBTheta,
    });
  }

  if (generatedNF.sched0PolynomialExponent !== 36) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'sched0PolynomialExponent'], 'GeneratedPCCPackexp0 NF must certify selector polynomial exponent', {
      expected: 36,
      actual: generatedNF.sched0PolynomialExponent,
    });
  }

  const generatedIfaceDict0 = generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.MaterializedBoot0?.IfaceDict0 ?? null;
  const generatedSched0 = generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.MaterializedBoot0?.Sched0 ?? null;

  if (!sameDigestHex0(generatedNF.ifaceDict0Digest, digestCanonical0(generatedIfaceDict0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'ifaceDict0Digest'], 'GeneratedPCCPackexp0 NF ifaceDict0Digest must match generated package IfaceDict0 bytes', {
      expected: digestCanonical0(generatedIfaceDict0),
      actual: generatedNF.ifaceDict0Digest,
    });
  }

  if (!sameDigestHex0(generatedNF.sched0Digest, digestCanonical0(generatedSched0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'sched0Digest'], 'GeneratedPCCPackexp0 NF sched0Digest must match generated package Sched0 bytes', {
      expected: digestCanonical0(generatedSched0),
      actual: generatedNF.sched0Digest,
    });
  }

  for (const field of [
    'generatedPackageByteLang0',
    'byteLang0Accepted',
    'byteLang0TagsUnique',
    'byteLang0RequiredTagsPresent',
    'byteLang0RequiredSortsPresent',
    'byteLang0RequiredConstructorsPresent',
    'byteLang0RequiredRecordAritiesPresent',
    'byteLang0PiBootDigestMatches',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.byteLang0Kind !== 'ByteLang0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'byteLang0Kind'], 'GeneratedPCCPackexp0 NF must certify ByteLang0 kind', {
      actual: generatedNF.byteLang0Kind,
    });
  }

  if (!(typeof generatedNF.byteLang0TagCount === 'number' && generatedNF.byteLang0TagCount >= 12)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'byteLang0TagCount'], 'GeneratedPCCPackexp0 NF must certify required ByteLang0 tag inventory', {
      actual: generatedNF.byteLang0TagCount,
    });
  }

  if (!(typeof generatedNF.byteLang0SortCount === 'number' && generatedNF.byteLang0SortCount >= 8)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'byteLang0SortCount'], 'GeneratedPCCPackexp0 NF must certify required ByteLang0 sorts', {
      actual: generatedNF.byteLang0SortCount,
    });
  }

  if (!(typeof generatedNF.byteLang0ConstructorCount === 'number' && generatedNF.byteLang0ConstructorCount >= 7)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'byteLang0ConstructorCount'], 'GeneratedPCCPackexp0 NF must certify required ByteLang0 constructors', {
      actual: generatedNF.byteLang0ConstructorCount,
    });
  }

  if (!(typeof generatedNF.byteLang0RecordCount === 'number' && generatedNF.byteLang0RecordCount >= 9)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'byteLang0RecordCount'], 'GeneratedPCCPackexp0 NF must certify required ByteLang0 record arities', {
      actual: generatedNF.byteLang0RecordCount,
    });
  }

  const generatedByteLang0 = generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.MaterializedBoot0?.ByteLang0 ?? null;

  if (!sameDigestHex0(generatedNF.byteLang0Digest, digestCanonical0(generatedByteLang0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'byteLang0Digest'], 'GeneratedPCCPackexp0 NF byteLang0Digest must match generated package ByteLang0 bytes', {
      expected: digestCanonical0(generatedByteLang0),
      actual: generatedNF.byteLang0Digest,
    });
  }

  for (const field of [
    'generatedPackageBootAudit0',
    'bootAudit0Accepted',
    'bootAudit0DigestMatchesNF',
    'bootAudit0CoversB0Accept',
    'bootAudit0CoversB0MissingCoverageReject',
    'bootAudit0CoversB0HashKeyTamperReject',
    'generatedPackagePiBoot0',
    'piBoot0Accepted',
    'piBoot0Materialized',
    'piBoot0ExternalJson',
    'piBoot0AllBootRefsPresent',
    'piBoot0RefsMatchBootObjects',
    'piBoot0RefsIncludeByteLang0',
    'piBoot0RefsIncludeCodec0',
    'piBoot0RefsIncludeDigest0',
    'piBoot0RefsIncludeIfaceDict0',
    'piBoot0RefsIncludeSched0',
    'piBoot0RefsIncludeKernelSeed0',
    'piBoot0RefsIncludeB0',
    'piBoot0RefsIncludeBootAudit0',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.bootAudit0Checker !== 'CheckVerifierFrag0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'bootAudit0Checker'], 'GeneratedPCCPackexp0 NF must certify CheckVerifierFrag0 BootAudit0 checker', {
      actual: generatedNF.bootAudit0Checker,
    });
  }

  if (generatedNF.bootAudit0NFKind !== 'VerifierFrag0AuditNF') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'bootAudit0NFKind'], 'GeneratedPCCPackexp0 NF must certify BootAudit0 NF kind', {
      actual: generatedNF.bootAudit0NFKind,
    });
  }

  if (generatedNF.bootAudit0SuiteId !== 'boot0.materialized.audit') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'bootAudit0SuiteId'], 'GeneratedPCCPackexp0 NF must certify BootAudit0 suite ID', {
      actual: generatedNF.bootAudit0SuiteId,
    });
  }

  if (generatedNF.bootAudit0CaseCount !== 3) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'bootAudit0CaseCount'], 'GeneratedPCCPackexp0 NF must certify BootAudit0 case count', {
      expected: 3,
      actual: generatedNF.bootAudit0CaseCount,
    });
  }

  if (generatedNF.bootAudit0PositiveCount !== 1) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'bootAudit0PositiveCount'], 'GeneratedPCCPackexp0 NF must certify BootAudit0 positive case count', {
      expected: 1,
      actual: generatedNF.bootAudit0PositiveCount,
    });
  }

  if (generatedNF.bootAudit0NegativeCount !== 2) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'bootAudit0NegativeCount'], 'GeneratedPCCPackexp0 NF must certify BootAudit0 negative case count', {
      expected: 2,
      actual: generatedNF.bootAudit0NegativeCount,
    });
  }

  if (generatedNF.piBoot0Kind !== 'PiBoot0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'piBoot0Kind'], 'GeneratedPCCPackexp0 NF must certify PiBoot0 kind', {
      actual: generatedNF.piBoot0Kind,
    });
  }

  if (!(typeof generatedNF.piBoot0RefCount === 'number' && generatedNF.piBoot0RefCount >= 8)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'piBoot0RefCount'], 'GeneratedPCCPackexp0 NF must certify all PiBoot bootstrap refs', {
      actual: generatedNF.piBoot0RefCount,
    });
  }

  const generatedBootAudit0 = generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.MaterializedBoot0?.BootAudit0 ?? null;
  const generatedPiBoot0 = generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.MaterializedBoot0?.PiBoot ?? null;

  if (!sameDigestHex0(generatedNF.bootAudit0Digest, digestFromRecord0(generatedBootAudit0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'bootAudit0Digest'], 'GeneratedPCCPackexp0 NF bootAudit0Digest must match generated package BootAudit0 record digest', {
      expected: digestFromRecord0(generatedBootAudit0),
      actual: generatedNF.bootAudit0Digest,
    });
  }

  if (!sameDigestHex0(generatedNF.piBoot0Digest, digestCanonical0(generatedPiBoot0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'piBoot0Digest'], 'GeneratedPCCPackexp0 NF piBoot0Digest must match generated package PiBoot bytes', {
      expected: digestCanonical0(generatedPiBoot0),
      actual: generatedNF.piBoot0Digest,
    });
  }

  for (const field of [
    'generatedPackageConcreteKBundle0',
    'concreteKBundle0Accepted',
    'concreteKBundle0KernelRuleCoverageComplete',
    'concreteKBundle0SigmaCoverageComplete',
    'concreteKBundle0SigmaProofRefsResolve',
    'concreteKBundle0ReflectionCoverageComplete',
    'concreteKBundle0ReflectionProofRefsResolve',
    'concreteKBundle0NoOpaqueProofRefs',
    'concreteKBundle0NoExecutableMinSymbols',
    'concreteKBundle0LinkedToGeneratedBoot0',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.concreteKBundle0Checker !== 'CheckConcreteMaterializedKBundle0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0Checker'], 'GeneratedPCCPackexp0 NF must certify concrete KBundle checker', {
      actual: generatedNF.concreteKBundle0Checker,
    });
  }

  if (generatedNF.concreteKBundle0KernelRuleCount !== 16) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0KernelRuleCount'], 'GeneratedPCCPackexp0 NF must certify complete PCC-K primitive rule count', {
      expected: 16,
      actual: generatedNF.concreteKBundle0KernelRuleCount,
    });
  }

  if (generatedNF.concreteKBundle0ConformanceNodeCount !== 16) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0ConformanceNodeCount'], 'GeneratedPCCPackexp0 NF must certify complete PCC-K conformance node count', {
      expected: 16,
      actual: generatedNF.concreteKBundle0ConformanceNodeCount,
    });
  }

  if (generatedNF.concreteKBundle0SigmaTheoremCount !== 2) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0SigmaTheoremCount'], 'GeneratedPCCPackexp0 NF must certify PCC-K Sigma theorem count', {
      expected: 2,
      actual: generatedNF.concreteKBundle0SigmaTheoremCount,
    });
  }

  if (!(typeof generatedNF.concreteKBundle0ReflectionCount === 'number' && generatedNF.concreteKBundle0ReflectionCount >= 5)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0ReflectionCount'], 'GeneratedPCCPackexp0 NF must certify reflection registry coverage count', {
      actual: generatedNF.concreteKBundle0ReflectionCount,
    });
  }

  const generatedMaterializedPCCPack = generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope ?? null;
  const generatedKBundleEnvelope = generatedMaterializedPCCPack?.KBundleEnvelope ?? null;
  const generatedConcreteKBundleBoot0 = generatedMaterializedPCCPack?.MaterializedBoot0 ?? generatedMaterializedPCCPack?.PCCPack?.Boot0 ?? null;

  if (!sameDigestHex0(generatedNF.concreteKBundle0BootDigest, digestCanonical0(generatedConcreteKBundleBoot0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0BootDigest'], 'GeneratedPCCPackexp0 NF concrete KBundle Boot0 digest must match generated package Boot0 bytes', {
      expected: digestCanonical0(generatedConcreteKBundleBoot0),
      actual: generatedNF.concreteKBundle0BootDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteKBundle0MaterializedKBundleDigest, digestCanonical0(generatedKBundleEnvelope?.MaterializedKBundleEnvelope ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0MaterializedKBundleDigest'], 'GeneratedPCCPackexp0 NF concrete KBundle materialized digest must match generated package KBundle bytes', {
      expected: digestCanonical0(generatedKBundleEnvelope?.MaterializedKBundleEnvelope ?? null),
      actual: generatedNF.concreteKBundle0MaterializedKBundleDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteKBundle0KImplDigest, digestCanonical0(generatedKBundleEnvelope?.KImpl ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0KImplDigest'], 'GeneratedPCCPackexp0 NF KImpl digest must match generated package KImpl bytes', {
      expected: digestCanonical0(generatedKBundleEnvelope?.KImpl ?? null),
      actual: generatedNF.concreteKBundle0KImplDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteKBundle0K0Digest, digestCanonical0(generatedKBundleEnvelope?.K0 ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0K0Digest'], 'GeneratedPCCPackexp0 NF K0 digest must match generated package K0 bytes', {
      expected: digestCanonical0(generatedKBundleEnvelope?.K0 ?? null),
      actual: generatedNF.concreteKBundle0K0Digest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteKBundle0SigmaDigest, digestCanonical0(generatedKBundleEnvelope?.PSigma ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0SigmaDigest'], 'GeneratedPCCPackexp0 NF Sigma digest must match generated package PΣ bytes', {
      expected: digestCanonical0(generatedKBundleEnvelope?.PSigma ?? null),
      actual: generatedNF.concreteKBundle0SigmaDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteKBundle0ReflectionDigest, digestCanonical0(generatedKBundleEnvelope?.ReflectionRegistry ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0ReflectionDigest'], 'GeneratedPCCPackexp0 NF reflection digest must match generated package reflection registry bytes', {
      expected: digestCanonical0(generatedKBundleEnvelope?.ReflectionRegistry ?? null),
      actual: generatedNF.concreteKBundle0ReflectionDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteKBundle0ProofInventoryDigest, digestCanonical0(generatedKBundleEnvelope?.ProofInventory ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteKBundle0ProofInventoryDigest'], 'GeneratedPCCPackexp0 NF proof inventory digest must match generated package proof inventory bytes', {
      expected: digestCanonical0(generatedKBundleEnvelope?.ProofInventory ?? null),
      actual: generatedNF.concreteKBundle0ProofInventoryDigest,
    });
  }

  for (const field of [
    'generatedPackageConcreteHard0',
    'concreteHard0Accepted',
    'concreteHard0CheckerCoverageComplete',
    'concreteHard0RowKeyCoverageComplete',
    'concreteHard0RoutePriorityComplete',
    'concreteHard0ProofRefPolicyComplete',
    'concreteHard0HashDisciplineComplete',
    'concreteHard0NoMinCoverageComplete',
    'concreteHard0ImportPolicyComplete',
    'concreteHard0ReflectionPolicyComplete',
    'concreteHard0BoundsPolicyComplete',
    'concreteHard0DiagnosticsPolicyComplete',
    'concreteHard0LinkedToPCCPack',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.concreteHard0Checker !== 'CheckConcreteMaterializedHard0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteHard0Checker'], 'GeneratedPCCPackexp0 NF must certify concrete HardCheck checker', {
      actual: generatedNF.concreteHard0Checker,
    });
  }

  if (generatedNF.concreteHard0CheckerCount !== 13) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteHard0CheckerCount'], 'GeneratedPCCPackexp0 NF must certify complete hardened checker inventory', {
      expected: 13,
      actual: generatedNF.concreteHard0CheckerCount,
    });
  }

  if (generatedNF.concreteHard0RowKeyFieldCount !== 17) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteHard0RowKeyFieldCount'], 'GeneratedPCCPackexp0 NF must certify complete row-key field inventory', {
      expected: 17,
      actual: generatedNF.concreteHard0RowKeyFieldCount,
    });
  }

  if (generatedNF.concreteHard0ForbiddenSymbolCount !== 11) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteHard0ForbiddenSymbolCount'], 'GeneratedPCCPackexp0 NF must certify no-hidden-minimization forbidden symbol inventory', {
      expected: 11,
      actual: generatedNF.concreteHard0ForbiddenSymbolCount,
    });
  }

  if (generatedNF.concreteHard0ForbiddenImportEdgeCount !== 6) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteHard0ForbiddenImportEdgeCount'], 'GeneratedPCCPackexp0 NF must certify forbidden import edge inventory', {
      expected: 6,
      actual: generatedNF.concreteHard0ForbiddenImportEdgeCount,
    });
  }

  const generatedMaterializedPCCPackForHard0 =
    generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope ?? null;
  const generatedHardEnvelope =
    generatedMaterializedPCCPackForHard0?.HardEnvelope ?? null;

  if (!sameDigestHex0(generatedNF.concreteHard0MaterializedHardDigest, digestCanonical0(generatedHardEnvelope?.MaterializedHardEnvelope ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteHard0MaterializedHardDigest'], 'GeneratedPCCPackexp0 NF concrete HardCheck materialized digest must match generated package HardEnvelope bytes', {
      expected: digestCanonical0(generatedHardEnvelope?.MaterializedHardEnvelope ?? null),
      actual: generatedNF.concreteHard0MaterializedHardDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteHard0HardCheckDigest, digestCanonical0(generatedHardEnvelope?.HardCheck ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteHard0HardCheckDigest'], 'GeneratedPCCPackexp0 NF concrete HardCheck digest must match generated package HardCheck bytes', {
      expected: digestCanonical0(generatedHardEnvelope?.HardCheck ?? null),
      actual: generatedNF.concreteHard0HardCheckDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteHard0CoverageDigest, digestCanonical0(generatedHardEnvelope?.Coverage ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteHard0CoverageDigest'], 'GeneratedPCCPackexp0 NF concrete HardCheck coverage digest must match generated package coverage bytes', {
      expected: digestCanonical0(generatedHardEnvelope?.Coverage ?? null),
      actual: generatedNF.concreteHard0CoverageDigest,
    });
  }

  if (!sameDigestHex0(digestCanonical0(generatedMaterializedPCCPackForHard0?.PCCPack?.HardCheck ?? null), digestCanonical0(generatedHardEnvelope?.HardCheck ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteHard0LinkedToPCCPack'], 'GeneratedPCCPackexp0 NF concrete HardCheck linkage must match PCCPack.HardCheck bytes', {
      expected: digestCanonical0(generatedMaterializedPCCPackForHard0?.PCCPack?.HardCheck ?? null),
      actual: digestCanonical0(generatedHardEnvelope?.HardCheck ?? null),
    });
  }

  for (const field of [
    'generatedPackageConcreteRows0',
    'concreteRows0Accepted',
    'concreteRows0ConcreteIfaceHash',
    'concreteRows0LinkedToGeneratedBoot0',
    'concreteRows0LinkedToPCCPack',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.concreteRows0Checker !== 'CheckConcreteMaterializedRows0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0Checker'], 'GeneratedPCCPackexp0 NF must certify concrete Rows checker', {
      actual: generatedNF.concreteRows0Checker,
    });
  }

  if (generatedNF.concreteRows0RowCount !== 39) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0RowCount'], 'GeneratedPCCPackexp0 NF must certify complete concrete row coverage', {
      expected: 39,
      actual: generatedNF.concreteRows0RowCount,
    });
  }

  if (generatedNF.concreteRows0BatchCount !== 13) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0BatchCount'], 'GeneratedPCCPackexp0 NF must certify B0 through B12 batch coverage', {
      expected: 13,
      actual: generatedNF.concreteRows0BatchCount,
    });
  }

  if (generatedNF.concreteRows0FamilyCount !== 39) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0FamilyCount'], 'GeneratedPCCPackexp0 NF must certify complete row-family coverage', {
      expected: 39,
      actual: generatedNF.concreteRows0FamilyCount,
    });
  }

  if (generatedNF.concreteRows0SyntheticIfaceHashCount !== 0) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0SyntheticIfaceHashCount'], 'GeneratedPCCPackexp0 NF must certify no synthetic row IfaceHash markers', {
      expected: 0,
      actual: generatedNF.concreteRows0SyntheticIfaceHashCount,
    });
  }

  if (generatedNF.concreteRows0ScaffoldMarkerCount !== 0) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0ScaffoldMarkerCount'], 'GeneratedPCCPackexp0 NF must certify no row scaffold markers', {
      expected: 0,
      actual: generatedNF.concreteRows0ScaffoldMarkerCount,
    });
  }

  const generatedMaterializedPCCPackForRows0 =
    generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope ?? null;
  const generatedRowsEnvelope =
    generatedMaterializedPCCPackForRows0?.RowsEnvelope ?? null;
  const generatedRowsBoot0 =
    generatedMaterializedPCCPackForRows0?.MaterializedBoot0 ??
    generatedMaterializedPCCPackForRows0?.PCCPack?.Boot0 ??
    null;

  if (!sameDigestHex0(generatedNF.concreteRows0BootDigest, digestCanonical0(generatedRowsBoot0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0BootDigest'], 'GeneratedPCCPackexp0 NF concrete Rows Boot0 digest must match generated package Boot0 bytes', {
      expected: digestCanonical0(generatedRowsBoot0),
      actual: generatedNF.concreteRows0BootDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteRows0RowPackObjectDigest, digestCanonical0(generatedRowsEnvelope?.RowPack ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0RowPackObjectDigest'], 'GeneratedPCCPackexp0 NF concrete RowPack object digest must match generated package RowPack bytes', {
      expected: digestCanonical0(generatedRowsEnvelope?.RowPack ?? null),
      actual: generatedNF.concreteRows0RowPackObjectDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteRows0IfaceHash, digestCanonical0(generatedRowsBoot0?.IfaceDict0 ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0IfaceHash'], 'GeneratedPCCPackexp0 NF concrete Rows IfaceHash must match generated Boot0 IfaceDict0 digest', {
      expected: digestCanonical0(generatedRowsBoot0?.IfaceDict0 ?? null),
      actual: generatedNF.concreteRows0IfaceHash,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteRows0SchedHash, digestCanonical0(generatedRowsBoot0?.Sched0 ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0SchedHash'], 'GeneratedPCCPackexp0 NF concrete Rows SchedHash must match generated Boot0 Sched0 digest', {
      expected: digestCanonical0(generatedRowsBoot0?.Sched0 ?? null),
      actual: generatedNF.concreteRows0SchedHash,
    });
  }

  if (!sameDigestHex0(
    digestCanonical0(generatedMaterializedPCCPackForRows0?.PCCPack?.RowPack ?? null),
    digestCanonical0(generatedRowsEnvelope?.RowPack ?? null),
  )) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteRows0LinkedToPCCPack'], 'GeneratedPCCPackexp0 NF concrete Rows linkage must match PCCPack.RowPack bytes', {
      expected: digestCanonical0(generatedMaterializedPCCPackForRows0?.PCCPack?.RowPack ?? null),
      actual: digestCanonical0(generatedRowsEnvelope?.RowPack ?? null),
    });
  }

  for (const field of [
    'generatedPackageConcreteGlobalProofDAG0',
    'concreteGlobalProofDAG0Accepted',
    'concreteGlobalProofDAG0KBundleKernelRuleCoverageComplete',
    'concreteGlobalProofDAG0KBundleSigmaProofRefsResolve',
    'concreteGlobalProofDAG0KBundleReflectionProofRefsResolve',
    'concreteGlobalProofDAG0NodeCountMinimum',
    'concreteGlobalProofDAG0FinalPackageSoundness',
    'concreteGlobalProofDAG0FinalGeneratedPackageSufficiency',
    'concreteGlobalProofDAG0FinalAcceptedPackageImpliesSATinP',
    'concreteGlobalProofDAG0FinalAcceptedPackageImpliesPEqualsNP',
    'concreteGlobalProofDAG0IfaceMatchesRows',
    'concreteGlobalProofDAG0SchedMatchesKImpl',
    'concreteGlobalProofDAG0NoForbiddenMarkers',
    'concreteGlobalProofDAG0LinkedToGeneratedBoot0',
    'concreteGlobalProofDAG0LinkedToKImpl',
    'concreteGlobalProofDAG0LinkedToConcreteRows',
    'concreteGlobalProofDAG0LinkedToLocalPackages',
    'concreteGlobalProofDAG0LinkedToGlobalFirewalls',
    'concreteGlobalProofDAG0LinkedToPCCPack',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.concreteGlobalProofDAG0Checker !== 'CheckConcreteMaterializedGlobalProofDAG0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0Checker'], 'GeneratedPCCPackexp0 NF must certify concrete GlobalProofDAG checker', {
      actual: generatedNF.concreteGlobalProofDAG0Checker,
    });
  }

  if (!(typeof generatedNF.concreteGlobalProofDAG0NodeCount === 'number' && generatedNF.concreteGlobalProofDAG0NodeCount >= 90)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0NodeCount'], 'GeneratedPCCPackexp0 NF must certify complete concrete GlobalProofDAG node inventory', {
      minimum: 90,
      actual: generatedNF.concreteGlobalProofDAG0NodeCount,
    });
  }

  if (generatedNF.concreteGlobalProofDAG0FinalTheoremCount !== 4) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0FinalTheoremCount'], 'GeneratedPCCPackexp0 NF must certify four final theorem nodes', {
      expected: 4,
      actual: generatedNF.concreteGlobalProofDAG0FinalTheoremCount,
    });
  }

  if (generatedNF.concreteGlobalProofDAG0ForbiddenMarkerCount !== 0) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0ForbiddenMarkerCount'], 'GeneratedPCCPackexp0 NF must certify no forbidden GlobalProofDAG scaffold markers', {
      expected: 0,
      actual: generatedNF.concreteGlobalProofDAG0ForbiddenMarkerCount,
    });
  }

  const generatedMaterializedPCCPackForGlobalDAG0 =
    generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope ?? null;

  const generatedGlobalProofDAGEnvelopeForGlobalDAG0 =
    generatedMaterializedPCCPackForGlobalDAG0?.GlobalProofDAGEnvelope ?? null;

  const generatedGlobalProofDAGForGlobalDAG0 =
    generatedGlobalProofDAGEnvelopeForGlobalDAG0?.GlobalProofDAG ??
    generatedGlobalProofDAGEnvelopeForGlobalDAG0?.MaterializedGlobalProofDAGEnvelope?.GlobalProofDAG ??
    null;

  const generatedKBundleEnvelopeForGlobalDAG0 =
    generatedMaterializedPCCPackForGlobalDAG0?.KBundleEnvelope ?? null;

  const generatedRowsEnvelopeForGlobalDAG0 =
    generatedMaterializedPCCPackForGlobalDAG0?.RowsEnvelope ?? null;

  const generatedLocalPackagesEnvelopeForGlobalDAG0 =
    generatedMaterializedPCCPackForGlobalDAG0?.LocalPackagesEnvelope ?? null;

  const generatedGlobalFirewallsEnvelopeForGlobalDAG0 =
    generatedMaterializedPCCPackForGlobalDAG0?.GlobalFirewallsEnvelope ?? null;

  const generatedKImplForGlobalDAG0 =
    generatedKBundleEnvelopeForGlobalDAG0?.KImpl ??
    generatedKBundleEnvelopeForGlobalDAG0?.kimpl ??
    generatedKBundleEnvelopeForGlobalDAG0?.KBundle?.KImpl ??
    generatedKBundleEnvelopeForGlobalDAG0?.MaterializedKBundleEnvelope?.KImpl ??
    generatedKBundleEnvelopeForGlobalDAG0?.MaterializedKBundleEnvelope?.KBundle?.KImpl ??
    null;

  const generatedRowPackForGlobalDAG0 =
    generatedRowsEnvelopeForGlobalDAG0?.RowPack ??
    generatedRowsEnvelopeForGlobalDAG0?.rowPack ??
    null;

  const generatedLocalPackagesForGlobalDAG0 =
    generatedLocalPackagesEnvelopeForGlobalDAG0?.LocalPackages ??
    generatedLocalPackagesEnvelopeForGlobalDAG0?.localPackages ??
    generatedLocalPackagesEnvelopeForGlobalDAG0?.LocalPackagePack ??
    generatedLocalPackagesEnvelopeForGlobalDAG0?.localPackagePack ??
    null;

  const generatedGlobalFirewallsForGlobalDAG0 =
    generatedGlobalFirewallsEnvelopeForGlobalDAG0?.GlobalFirewalls ??
    generatedGlobalFirewallsEnvelopeForGlobalDAG0?.globalFirewalls ??
    generatedGlobalFirewallsEnvelopeForGlobalDAG0?.GlobalFirewallPack ??
    generatedGlobalFirewallsEnvelopeForGlobalDAG0?.globalFirewallPack ??
    null;

  if (!sameDigestHex0(generatedNF.concreteGlobalProofDAG0GlobalProofDAGObjectDigest, digestCanonical0(generatedGlobalProofDAGForGlobalDAG0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0GlobalProofDAGObjectDigest'], 'GeneratedPCCPackexp0 NF concrete GlobalProofDAG object digest must match generated package GlobalProofDAG bytes', {
      expected: digestCanonical0(generatedGlobalProofDAGForGlobalDAG0),
      actual: generatedNF.concreteGlobalProofDAG0GlobalProofDAGObjectDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteGlobalProofDAG0MaterializedGlobalProofDAGDigest, digestCanonical0(generatedGlobalProofDAGEnvelopeForGlobalDAG0?.MaterializedGlobalProofDAGEnvelope ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0MaterializedGlobalProofDAGDigest'], 'GeneratedPCCPackexp0 NF materialized GlobalProofDAG digest must match generated package bytes', {
      expected: digestCanonical0(generatedGlobalProofDAGEnvelopeForGlobalDAG0?.MaterializedGlobalProofDAGEnvelope ?? null),
      actual: generatedNF.concreteGlobalProofDAG0MaterializedGlobalProofDAGDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteGlobalProofDAG0KImplDigest, digestCanonical0(generatedKImplForGlobalDAG0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0KImplDigest'], 'GeneratedPCCPackexp0 NF KImpl digest must match generated package KImpl bytes', {
      expected: digestCanonical0(generatedKImplForGlobalDAG0),
      actual: generatedNF.concreteGlobalProofDAG0KImplDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteGlobalProofDAG0RowPackDigest, digestCanonical0(generatedRowPackForGlobalDAG0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0RowPackDigest'], 'GeneratedPCCPackexp0 NF row-pack digest must match generated package RowPack bytes', {
      expected: digestCanonical0(generatedRowPackForGlobalDAG0),
      actual: generatedNF.concreteGlobalProofDAG0RowPackDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteGlobalProofDAG0LocalPackagesDigest, digestCanonical0(generatedLocalPackagesForGlobalDAG0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0LocalPackagesDigest'], 'GeneratedPCCPackexp0 NF local-packages digest must match generated package local package bytes', {
      expected: digestCanonical0(generatedLocalPackagesForGlobalDAG0),
      actual: generatedNF.concreteGlobalProofDAG0LocalPackagesDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteGlobalProofDAG0GlobalFirewallsDigest, digestCanonical0(generatedGlobalFirewallsForGlobalDAG0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0GlobalFirewallsDigest'], 'GeneratedPCCPackexp0 NF global-firewalls digest must match generated package global firewall bytes', {
      expected: digestCanonical0(generatedGlobalFirewallsForGlobalDAG0),
      actual: generatedNF.concreteGlobalProofDAG0GlobalFirewallsDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteGlobalProofDAG0KBundleProofInventoryDigest, digestCanonical0(generatedKBundleEnvelopeForGlobalDAG0?.ProofInventory ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0KBundleProofInventoryDigest'], 'GeneratedPCCPackexp0 NF KBundle proof-inventory digest must match generated package proof inventory bytes', {
      expected: digestCanonical0(generatedKBundleEnvelopeForGlobalDAG0?.ProofInventory ?? null),
      actual: generatedNF.concreteGlobalProofDAG0KBundleProofInventoryDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteGlobalProofDAG0IfaceHash, generatedRowPackForGlobalDAG0?.IfaceHash)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0IfaceHash'], 'GeneratedPCCPackexp0 NF GlobalProofDAG IfaceHash must match generated RowPack IfaceHash', {
      expected: generatedRowPackForGlobalDAG0?.IfaceHash,
      actual: generatedNF.concreteGlobalProofDAG0IfaceHash,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteGlobalProofDAG0SchedHash, generatedKImplForGlobalDAG0?.SchedHash)) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0SchedHash'], 'GeneratedPCCPackexp0 NF GlobalProofDAG SchedHash must match generated KImpl SchedHash', {
      expected: generatedKImplForGlobalDAG0?.SchedHash,
      actual: generatedNF.concreteGlobalProofDAG0SchedHash,
    });
  }

  if (!sameDigestHex0(
    digestCanonical0(generatedMaterializedPCCPackForGlobalDAG0?.PCCPack?.GlobalProofDAG ?? null),
    digestCanonical0(generatedGlobalProofDAGForGlobalDAG0),
  )) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteGlobalProofDAG0LinkedToPCCPack'], 'GeneratedPCCPackexp0 NF concrete GlobalProofDAG linkage must match PCCPack.GlobalProofDAG bytes', {
      expected: digestCanonical0(generatedMaterializedPCCPackForGlobalDAG0?.PCCPack?.GlobalProofDAG ?? null),
      actual: digestCanonical0(generatedGlobalProofDAGForGlobalDAG0),
    });
  }

  for (const field of [
    'generatedPackageConcreteFinalIntegration0',
    'concreteFinalIntegration0Accepted',
    'concreteFinalIntegration0ConcreteGlobalProofDAG',
    'concreteFinalIntegration0ConcreteKBundle',
    'concreteFinalIntegration0ConcreteRows',
    'concreteFinalIntegration0ConcreteLocalPackages',
    'concreteFinalIntegration0ConcreteGlobalFirewalls',
    'concreteFinalIntegration0KBundleKernelRuleCoverageComplete',
    'concreteFinalIntegration0KBundleSigmaProofRefsResolve',
    'concreteFinalIntegration0KBundleReflectionProofRefsResolve',
    'concreteFinalIntegration0GPackFieldCoverageComplete',
    'concreteFinalIntegration0RowFamGCoverageComplete',
    'concreteFinalIntegration0FinalIntegrationUsesGPack',
    'concreteFinalIntegration0RowFamGUsesGPack',
    'concreteFinalIntegration0FinalTheoremUsesFinalIntegration',
    'concreteFinalIntegration0RowFamFinalUsesFinalTheorem',
    'concreteFinalIntegration0FinalMatchUsesGPack',
    'concreteFinalIntegration0SATDecisionUsesGPack',
    'concreteFinalIntegration0NoForbiddenMarkers',
    'concreteFinalIntegration0LinkedToGeneratedGlobalProofDAG',
    'concreteFinalIntegration0LinkedToGPack',
    'concreteFinalIntegration0LinkedToRowFamG',
    'concreteFinalIntegration0LinkedToFinalIntegration',
    'concreteFinalIntegration0LinkedToFinalTheorem',
    'concreteFinalIntegration0LinkedToRowFamFinal',
    'concreteFinalIntegration0LinkedToPCCPack',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.concreteFinalIntegration0Checker !== 'CheckConcreteMaterializedFinalIntegration0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteFinalIntegration0Checker'], 'GeneratedPCCPackexp0 NF must certify concrete FinalIntegration checker', {
      actual: generatedNF.concreteFinalIntegration0Checker,
    });
  }

  if (generatedNF.concreteFinalIntegration0ForbiddenMarkerCount !== 0) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteFinalIntegration0ForbiddenMarkerCount'], 'GeneratedPCCPackexp0 NF must certify no forbidden FinalIntegration scaffold markers', {
      expected: 0,
      actual: generatedNF.concreteFinalIntegration0ForbiddenMarkerCount,
    });
  }

  const generatedMaterializedPCCPackForFinalIntegration0 =
    generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope ?? null;

  const generatedPCCPackForFinalIntegration0 =
    generatedMaterializedPCCPackForFinalIntegration0?.PCCPack ?? null;

  const generatedFinalIntegrationEnvelopeForFinalIntegration0 =
    generatedMaterializedPCCPackForFinalIntegration0?.FinalIntegrationEnvelope ?? null;

  if (!sameDigestHex0(generatedNF.concreteFinalIntegration0ConcreteGlobalProofDAGDigest, digestCanonical0(generatedMaterializedPCCPackForFinalIntegration0?.GlobalProofDAGEnvelope ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteFinalIntegration0ConcreteGlobalProofDAGDigest'], 'GeneratedPCCPackexp0 NF concrete FinalIntegration GlobalProofDAG digest must match generated package GlobalProofDAG envelope bytes', {
      expected: digestCanonical0(generatedMaterializedPCCPackForFinalIntegration0?.GlobalProofDAGEnvelope ?? null),
      actual: generatedNF.concreteFinalIntegration0ConcreteGlobalProofDAGDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteFinalIntegration0MaterializedFinalIntegrationDigest, digestCanonical0(generatedFinalIntegrationEnvelopeForFinalIntegration0?.FinalIntegrationEnvelope ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteFinalIntegration0MaterializedFinalIntegrationDigest'], 'GeneratedPCCPackexp0 NF concrete FinalIntegration materialized digest must match generated package final-integration envelope bytes', {
      expected: digestCanonical0(generatedFinalIntegrationEnvelopeForFinalIntegration0?.FinalIntegrationEnvelope ?? null),
      actual: generatedNF.concreteFinalIntegration0MaterializedFinalIntegrationDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteFinalIntegration0GPackDigest, digestCanonical0(generatedPCCPackForFinalIntegration0?.GPack ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteFinalIntegration0GPackDigest'], 'GeneratedPCCPackexp0 NF GPack digest must match PCCPack.GPack bytes', {
      expected: digestCanonical0(generatedPCCPackForFinalIntegration0?.GPack ?? null),
      actual: generatedNF.concreteFinalIntegration0GPackDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteFinalIntegration0RowFamGDigest, digestCanonical0(generatedPCCPackForFinalIntegration0?.RowFamG ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteFinalIntegration0RowFamGDigest'], 'GeneratedPCCPackexp0 NF RowFamG digest must match PCCPack.RowFamG bytes', {
      expected: digestCanonical0(generatedPCCPackForFinalIntegration0?.RowFamG ?? null),
      actual: generatedNF.concreteFinalIntegration0RowFamGDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteFinalIntegration0FinalIntegrationDigest, digestCanonical0(generatedPCCPackForFinalIntegration0?.FinalIntegration ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteFinalIntegration0FinalIntegrationDigest'], 'GeneratedPCCPackexp0 NF FinalIntegration digest must match PCCPack.FinalIntegration bytes', {
      expected: digestCanonical0(generatedPCCPackForFinalIntegration0?.FinalIntegration ?? null),
      actual: generatedNF.concreteFinalIntegration0FinalIntegrationDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteFinalIntegration0FinalTheoremDigest, digestCanonical0(generatedPCCPackForFinalIntegration0?.FinalTheorem ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteFinalIntegration0FinalTheoremDigest'], 'GeneratedPCCPackexp0 NF FinalTheorem digest must match PCCPack.FinalTheorem bytes', {
      expected: digestCanonical0(generatedPCCPackForFinalIntegration0?.FinalTheorem ?? null),
      actual: generatedNF.concreteFinalIntegration0FinalTheoremDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteFinalIntegration0RowFamFinalDigest, digestCanonical0(generatedPCCPackForFinalIntegration0?.RowFamFinal ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteFinalIntegration0RowFamFinalDigest'], 'GeneratedPCCPackexp0 NF RowFamFinal digest must match PCCPack.RowFamFinal bytes', {
      expected: digestCanonical0(generatedPCCPackForFinalIntegration0?.RowFamFinal ?? null),
      actual: generatedNF.concreteFinalIntegration0RowFamFinalDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.concreteFinalIntegration0ConcreteLinksDigest, digestCanonical0(generatedFinalIntegrationEnvelopeForFinalIntegration0?.ConcreteLinks ?? null))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'concreteFinalIntegration0ConcreteLinksDigest'], 'GeneratedPCCPackexp0 NF ConcreteLinks digest must match generated package ConcreteLinks bytes', {
      expected: digestCanonical0(generatedFinalIntegrationEnvelopeForFinalIntegration0?.ConcreteLinks ?? null),
      actual: generatedNF.concreteFinalIntegration0ConcreteLinksDigest,
    });
  }

  for (const field of [
    'generatedPackageCheckPCCPackexp0',
    'checkPCCPackexp0Accepted',
    'checkPCCPackexp0MaterializedPath',
    'checkPCCPackexp0SyntheticRunAll',
    'checkPCCPackexp0PublicConclusionOnlyAfterAcceptRun',
    'checkPCCPackexp0PublicConclusionEmitted',
    'checkPCCPackexp0NoPrematurePublicConclusion',
    'checkPCCPackexp0ClaimBoundaryConditional',
    'checkPCCPackexp0GeneratedPackageImplication',
    'checkPCCPackexp0ConcretePCCPack',
    'checkPCCPackexp0ConcreteKBundle',
    'checkPCCPackexp0ConcreteHardCheck',
    'checkPCCPackexp0ConcreteRows',
    'checkPCCPackexp0ConcreteLocalPackages',
    'checkPCCPackexp0ConcreteGlobalFirewalls',
    'checkPCCPackexp0ConcreteGlobalProofDAG',
    'checkPCCPackexp0ConcreteFinalIntegration',
    'checkPCCPackexp0KBundleCoverageComplete',
    'checkPCCPackexp0HardCoverageComplete',
    'checkPCCPackexp0FinalIntegrationCoverageComplete',
    'checkPCCPackexp0PCCPackLinkageComplete',
    'checkPCCPackexp0ConcreteCoverageComplete',
    'checkPCCPackexp0ConcretePCCPackRecordAccepted',
  ]) {
    if (generatedNF[field] !== true) {
      return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', field], `GeneratedPCCPackexp0 NF must certify ${field}`, {
        actual: generatedNF[field],
      });
    }
  }

  if (generatedNF.checkPCCPackexp0Checker !== 'CheckPCCPackexp0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'checkPCCPackexp0Checker'], 'GeneratedPCCPackexp0 NF must certify central CheckPCCPackexp0 checker', {
      actual: generatedNF.checkPCCPackexp0Checker,
    });
  }

  if (generatedNF.checkPCCPackexp0PackageKind !== 'PCCPack0') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'checkPCCPackexp0PackageKind'], 'GeneratedPCCPackexp0 NF must certify PCCPack0 package kind', {
      actual: generatedNF.checkPCCPackexp0PackageKind,
    });
  }

  if (generatedNF.checkPCCPackexp0ClaimBoundaryAntecedent !== 'CheckPCCPackexp(GeneratePCCPack())=accept') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'checkPCCPackexp0ClaimBoundaryAntecedent'], 'GeneratedPCCPackexp0 NF must certify generated package implication antecedent', {
      actual: generatedNF.checkPCCPackexp0ClaimBoundaryAntecedent,
    });
  }

  if (generatedNF.checkPCCPackexp0ClaimBoundaryConsequent !== 'P = NP') {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'checkPCCPackexp0ClaimBoundaryConsequent'], 'GeneratedPCCPackexp0 NF must certify P = NP consequent', {
      actual: generatedNF.checkPCCPackexp0ClaimBoundaryConsequent,
    });
  }

  const materializedPCCPackForCheckPCCPackexp0 =
    generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope ??
    generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPack ??
    null;

  const pccPackForCheckPCCPackexp0 =
    materializedPCCPackForCheckPCCPackexp0?.PCCPack ??
    generatedPCCPackexpEnvelope.GeneratedPCCPack?.PCCPack ??
    null;

  if (!sameDigestHex0(generatedNF.checkPCCPackexp0Digest, digestFromRecord0(generatedPCCPackexpEnvelope.CheckPCCPackexpRecord))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'checkPCCPackexp0Digest'], 'GeneratedPCCPackexp0 NF CheckPCCPackexp0 digest must match materialized CheckPCCPackexpRecord digest', {
      expected: digestFromRecord0(generatedPCCPackexpEnvelope.CheckPCCPackexpRecord),
      actual: generatedNF.checkPCCPackexp0Digest,
    });
  }

  if (!sameDigestHex0(generatedNF.checkPCCPackexp0PCCPackDigest, digestCanonical0(pccPackForCheckPCCPackexp0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'checkPCCPackexp0PCCPackDigest'], 'GeneratedPCCPackexp0 NF PCCPack digest must match generated PCCPack bytes', {
      expected: digestCanonical0(pccPackForCheckPCCPackexp0),
      actual: generatedNF.checkPCCPackexp0PCCPackDigest,
    });
  }

  if (!sameDigestHex0(generatedNF.checkPCCPackexp0MaterializedPCCPackDigest, digestCanonical0(materializedPCCPackForCheckPCCPackexp0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'checkPCCPackexp0MaterializedPCCPackDigest'], 'GeneratedPCCPackexp0 NF materialized PCCPack digest must match generated materialized package bytes', {
      expected: digestCanonical0(materializedPCCPackForCheckPCCPackexp0),
      actual: generatedNF.checkPCCPackexp0MaterializedPCCPackDigest,
    });
  }

  const generatedBoot0 = generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.MaterializedBoot0 ?? null;

  if (!sameDigestHex0(generatedNF.boot0Digest, digestCanonical0(generatedBoot0))) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'NF', 'boot0Digest'], 'GeneratedPCCPackexp0 NF boot0Digest must match generated package Boot0 bytes', {
      expected: digestCanonical0(generatedBoot0),
      actual: generatedNF.boot0Digest,
    });
  }

  if (!sameDigestHex0(
    generatedNF.boot0Digest,
    generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.PCCPack?.Core?.artefactDigests?.Boot0 ?? null,
  )) {
    return validationReject0(['GeneratedPCCPackexpEnvelope', 'GeneratedPCCPack', 'PCCPack', 'Core', 'artefactDigests', 'Boot0'], 'GeneratedPCCPackexp0 Boot0 digest must match PCCPack core digest map', {
      expected: generatedNF.boot0Digest,
      actual: generatedPCCPackexpEnvelope.GeneratedPCCPack?.MaterializedPCCPackEnvelope?.PCCPack?.Core?.artefactDigests?.Boot0 ?? null,
    });
  }

  return validationAccept0({
    kind: 'ConcreteGeneratedAcceptRunGeneratedPCCPackexpEnvelope0NF',
    generatedPCCPackexpEnvelopeDigest: digestCanonical0(generatedPCCPackexpEnvelope),
    generatedPCCPackexpRecordDigest: digestFromRecord0(generatedPCCPackexpRecord),
    generatedPackageDigest: digestCanonical0(generatedPCCPackexpEnvelope.GeneratedPCCPack),
    checkPCCPackexpRecordDigest: digestFromRecord0(checkPCCPackexpRecord),
  });
}

function validateMaterializedCheckGeneratedPCCPackexpRecord0(actual, expected) {
  if (!isPlainObject(actual)) {
    return validationReject0(['CheckGeneratedPCCPackexpRecord'], 'ConcreteMaterializedGeneratedAcceptRun0 must include CheckGeneratedPCCPackexpRecord', {
      actual: typeof actual,
    });
  }

  if (actual.tag !== 'accept') {
    return validationReject0(['CheckGeneratedPCCPackexpRecord', 'tag'], 'CheckGeneratedPCCPackexpRecord must be accepted', {
      actual: actual.tag,
    });
  }

  if (actual.checker !== 'CheckGeneratedPCCPackexp0') {
    return validationReject0(['CheckGeneratedPCCPackexpRecord', 'checker'], 'CheckGeneratedPCCPackexpRecord checker mismatch', {
      actual: actual.checker,
    });
  }

  const actualNF = actual.NF ?? actual.nf;
  const expectedNF = expected?.NF ?? expected?.nf;

  if (!isPlainObject(actualNF)) {
    return validationReject0(['CheckGeneratedPCCPackexpRecord', 'NF'], 'CheckGeneratedPCCPackexpRecord must expose NF', {
      actual: typeof actualNF,
    });
  }

  if (!isPlainObject(expectedNF)) {
    return validationReject0(['CheckGeneratedPCCPackexpRecord'], 'fresh CheckGeneratedPCCPackexp0 record must expose NF', {
      actual: typeof expectedNF,
    });
  }

  const actualDigest = digestFromRecord0(actual);
  const actualNFDigest = digestCanonical0(actualNF);

  if (!sameDigestHex0(actualDigest, actualNFDigest)) {
    return validationReject0(['CheckGeneratedPCCPackexpRecord', 'Digest'], 'CheckGeneratedPCCPackexpRecord Digest must match its NF', {
      expected: actualNFDigest,
      actual: actualDigest,
    });
  }

  if (stableStringify0(actualNF) !== stableStringify0(expectedNF)) {
    return validationReject0(['CheckGeneratedPCCPackexpRecord', 'NF'], 'materialized CheckGeneratedPCCPackexpRecord must match fresh CheckGeneratedPCCPackexp0 replay', {
      expectedDigest: digestCanonical0(expectedNF),
      actualDigest: digestCanonical0(actualNF),
    });
  }

  if (!sameDigestHex0(actualDigest, digestFromRecord0(expected))) {
    return validationReject0(['CheckGeneratedPCCPackexpRecord', 'Digest'], 'materialized CheckGeneratedPCCPackexpRecord digest must match fresh replay digest', {
      expected: digestFromRecord0(expected),
      actual: actualDigest,
    });
  }

  return validationAccept0({
    kind: 'ConcreteGeneratedAcceptRunCheckGeneratedPCCPackexpRecord0NF',
    checkGeneratedPCCPackexpRecordDigest: actualDigest,
    generatedPackageDigest: actualNF.generatedPackageDigest ?? null,
    checkPCCPackexpRecordDigest: actualNF.checkPCCPackexpRecordDigest ?? null,
  });
}

function validateLinkage0(envelope, concreteChain) {
  if (envelope.Linkage === null || envelope.Linkage === undefined) {
    return validationAccept0({
      kind: 'ConcreteGeneratedAcceptRunLinkage0NF',
      present: false,
    });
  }

  if (!isPlainObject(envelope.Linkage)) {
    return validationReject0(['Linkage'], 'ConcreteMaterializedGeneratedAcceptRun0 Linkage must be an object when present', {
      actual: typeof envelope.Linkage,
    });
  }

  const generated = envelope.GeneratedAcceptRunEnvelope;

  const expected = {
    generatedAcceptRunEnvelopeDigest: digestCanonical0(generated),
    materializedPCCPackDigest: digestCanonical0(generated.MaterializedPCCPack),
    pccPackDigest: digestCanonical0(resolvePCCPack0(generated.MaterializedPCCPack)),
    acceptRunDigest: digestCanonical0(generated.AcceptRun),
    generatedPackageDigest: digestCanonical0(generated.GeneratedPackage),
    checkPCCPackexpRecordDigest: digestFromRecord0(envelope.CheckPCCPackexpRecord),
    generatedPCCPackexpEnvelopeDigest: (
      isPlainObject(envelope.GeneratedPCCPackexpEnvelope)
        ? digestCanonical0(envelope.GeneratedPCCPackexpEnvelope)
        : null
    ),
    generatedPCCPackDigest: (
      isPlainObject(envelope.GeneratedPCCPackexpEnvelope?.GeneratedPCCPack)
        ? digestCanonical0(envelope.GeneratedPCCPackexpEnvelope.GeneratedPCCPack)
        : null
    ),
    checkGeneratedPCCPackexpRecordDigest: digestFromRecord0(envelope.CheckGeneratedPCCPackexpRecord),
    concreteChainDigest: digestCanonical0(concreteChain),
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
    kind: 'ConcreteGeneratedAcceptRunLinkage0NF',
    present: true,
    ...expected,
  });
}

async function writeJsonFile0(filePath, value) {
  await fs.writeFile(filePath, `${stableStringify0(value)}\n`, 'utf8');
}

function resolvePCCPack0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'PCCPack0'
    ? value
    : value.PCCPack ?? value.pccPack ?? value.Pgen ?? null;
}

function resolveRowPack0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'RowPack0'
    ? value
    : value.RowPack ?? value.rowPack ?? null;
}

function resolveLocalPackages0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'LocalPackagePack0'
    ? value
    : value.LocalPackages ?? value.localPackages ?? value.LocalPackagePack ?? null;
}

function resolveGlobalFirewalls0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'GlobalFirewalls0'
    ? value
    : value.GlobalFirewalls ?? value.globalFirewalls ?? null;
}

function resolveGlobalProofDAG0(value) {
  if (!isPlainObject(value)) {
    return null;
  }

  return value.kind === 'GlobalProofDAG0'
    ? value
    : value.GlobalProofDAG ?? value.globalProofDAG ?? null;
}

function allTrue0(...values) {
  return values.every((value) => value === true);
}

function digestFromRecord0(record) {
  if (!isPlainObject(record)) {
    return null;
  }

  return record.Digest ?? record.digest ?? null;
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

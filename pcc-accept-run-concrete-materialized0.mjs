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

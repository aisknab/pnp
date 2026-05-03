
import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckPCCPackexp0,
  makeCheckPCCPackexpConfig0,
} from '../pcc-check-pcc-pack-exp0.mjs';

import {
  makeConcreteMaterializedPCCPack0,
  summarizeConcretePCCPackCoverage0,
} from '../pcc-pack-concrete-materialized0.mjs';

test('CheckPCCPackexp0 accepts a concrete materialized PCCPack candidate', async () => {
  const envelope = await makeConcreteMaterializedPCCPack0();
  const out = await CheckPCCPackexp0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckPCCPackexp0');
  assert.equal(out.NF.kind, 'CheckPCCPackexp0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.checkPCCPackexp, true);
  assert.equal(out.NF.packageKind, 'PCCPack0');
  assert.equal(out.NF.publicConclusionOnlyAfterAcceptRun, true);
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
  assert.equal(out.NF.publicConclusion.conditional, true);

  assert.equal(out.NF.concretePCCPack, true);
  assert.equal(out.NF.concreteKBundle, true);
  assert.equal(out.NF.kBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.kBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.kBundleReflectionProofRefsResolve, true);
  assert.equal(out.NF.kBundleNoOpaqueProofRefs, true);
  assert.equal(out.NF.kBundleNoExecutableMinSymbols, true);

  assert.equal(out.NF.concreteHardCheck, true);
  assert.equal(out.NF.hardCheckerCoverageComplete, true);
  assert.equal(out.NF.hardRowKeyCoverageComplete, true);
  assert.equal(out.NF.hardRoutePriorityComplete, true);
  assert.equal(out.NF.hardProofRefPolicyComplete, true);
  assert.equal(out.NF.hardHashDisciplineComplete, true);
  assert.equal(out.NF.hardNoMinCoverageComplete, true);
  assert.equal(out.NF.hardImportPolicyComplete, true);
  assert.equal(out.NF.hardReflectionPolicyComplete, true);
  assert.equal(out.NF.hardBoundsPolicyComplete, true);
  assert.equal(out.NF.hardDiagnosticsPolicyComplete, true);

  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteGlobalFirewalls, true);
  assert.equal(out.NF.concreteGlobalProofDAG, true);

  assert.equal(out.NF.concreteFinalIntegration, true);
  assert.equal(out.NF.finalIntegrationConcreteGlobalProofDAG, true);
  assert.equal(out.NF.finalIntegrationGPackFieldCoverageComplete, true);
  assert.equal(out.NF.finalIntegrationRowFamGCoverageComplete, true);
  assert.equal(out.NF.finalIntegrationUsesGPack, true);
  assert.equal(out.NF.rowFamGUsesGPack, true);
  assert.equal(out.NF.finalTheoremUsesFinalIntegration, true);
  assert.equal(out.NF.rowFamFinalUsesFinalTheorem, true);
  assert.equal(out.NF.finalMatchUsesGPack, true);
  assert.equal(out.NF.satDecisionUsesGPack, true);

  assert.equal(out.NF.pccPackLinkedToKBundle, true);
  assert.equal(out.NF.pccPackLinkedToHardCheck, true);
  assert.equal(out.NF.pccPackLinkedToRows, true);
  assert.equal(out.NF.pccPackLinkedToLocalPackages, true);
  assert.equal(out.NF.pccPackLinkedToGlobalFirewalls, true);
  assert.equal(out.NF.pccPackLinkedToGlobalProofDAG, true);
  assert.equal(out.NF.pccPackLinkedToGPack, true);
  assert.equal(out.NF.pccPackLinkedToFinalIntegration, true);
  assert.equal(out.NF.pccPackLinkedToFinalTheorem, true);

  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concreteCoverageDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.NF.concretePCCPackRecordDigest.hex, /^[0-9a-f]{64}$/);
});

test('CheckPCCPackexp0 accepts a raw MaterializedPCCPack0 through concrete normalization', async () => {
  const envelope = await makeConcreteMaterializedPCCPack0();
  const out = await CheckPCCPackexp0(envelope.MaterializedPCCPackEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckPCCPackexp0');
  assert.equal(out.NF.materializedPCCPackKind, 'MaterializedPCCPack0');
  assert.equal(out.NF.concretePCCPack, true);
  assert.equal(out.NF.publicConclusionOnlyAfterAcceptRun, true);
});

test('makeCheckPCCPackexpConfig0 fills default booleans and nested config', () => {
  const config = makeCheckPCCPackexpConfig0({
    checkJsonMaterialized: false,
  });

  assert.equal(config.kind, 'CheckPCCPackexpConfig0');
  assert.equal(config.checkConcreteMaterializedPCCPack, true);
  assert.equal(config.checkJsonMaterialized, false);
  assert.equal(typeof config.concretePCCPackConfig, 'object');
});

test('CheckPCCPackexp0 rejects package candidates whose public conclusion is not accept-run gated', async () => {
  const envelope = await makeConcreteMaterializedPCCPack0();

  envelope.MaterializedPCCPackEnvelope = {
    ...envelope.MaterializedPCCPackEnvelope,
    PCCPack: {
      ...envelope.MaterializedPCCPackEnvelope.PCCPack,
      Manifest: {
        ...envelope.MaterializedPCCPackEnvelope.PCCPack.Manifest,
        publicConclusionOnlyAfterAcceptRun: false,
      },
    },
  };

  envelope.PCCPack = envelope.MaterializedPCCPackEnvelope.PCCPack;
  envelope.ConcreteCoverage = summarizeConcretePCCPackCoverage0(envelope.MaterializedPCCPackEnvelope);
  envelope.Linkage = {
    ...envelope.Linkage,
    materializedPCCPackDigest: undefined,
    pccPackDigest: undefined,
    manifestDigest: undefined,
    concreteCoverageDigest: undefined,
  };

  const out = await CheckPCCPackexp0(envelope, {
    checkConcreteMaterializedPCCPack: false,
    checkRecordAlignment: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPCCPackexp0');
  assert.equal(out.Coord, 'CheckPCCPackexp0.concreteCoverage');
  assert.deepEqual(out.Path, ['ConcreteCoverage', 'publicConclusionOnlyAfterAcceptRun']);
});

test('CheckPCCPackexp0 surfaces inner concrete PCCPack rejection diagnostics', async () => {
  const envelope = await makeConcreteMaterializedPCCPack0();

  envelope.MaterializedPCCPackEnvelope = {
    ...envelope.MaterializedPCCPackEnvelope,
    PCCPack: {
      ...envelope.MaterializedPCCPackEnvelope.PCCPack,
      HardCheck: {
        ...envelope.MaterializedPCCPackEnvelope.PCCPack.HardCheck,
        DriftWitness: 'changed-hard-check',
      },
    },
  };

  envelope.PCCPack = envelope.MaterializedPCCPackEnvelope.PCCPack;
  envelope.ConcreteCoverage = summarizeConcretePCCPackCoverage0(envelope.MaterializedPCCPackEnvelope);
  envelope.Linkage = {
    ...envelope.Linkage,
    materializedPCCPackDigest: undefined,
    pccPackDigest: undefined,
    concreteCoverageDigest: undefined,
  };

  const out = await CheckPCCPackexp0(envelope, {
    concretePCCPackConfig: {
      checkMaterializedPCCPack: false,
      checkLinkage: false,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckPCCPackexp0');
  assert.equal(out.Coord, 'CheckPCCPackexp0.ConcretePCCPack');
  assert.deepEqual(out.Path, ['PCCPack']);
  assert.equal(out.Witness.detail.inner.coord, 'CheckConcreteMaterializedPCCPack0.concreteCoverage');
  assert.deepEqual(out.Witness.detail.inner.path, ['ConcreteCoverage', 'pccPackLinkedToHardCheck']);
});

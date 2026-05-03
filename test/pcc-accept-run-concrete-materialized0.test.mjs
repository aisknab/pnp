import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedGeneratedAcceptRun0,
  makeConcreteMaterializedGeneratedAcceptRun0,
  summarizeConcreteGeneratedAcceptRunChain0,
  writeConcreteMaterializedGeneratedAcceptRunFiles0,
} from '../pcc-accept-run-concrete-materialized0.mjs';

import {
  CheckMaterializedGeneratedAcceptRun0,
} from '../pcc-accept-run-materialized0.mjs';

test('CheckConcreteMaterializedGeneratedAcceptRun0 accepts an accept run over the concrete package chain', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();
  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedGeneratedAcceptRun0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteGlobalFirewalls, true);
  assert.equal(out.NF.concreteGlobalProofDAG, true);

  assert.equal(out.NF.concreteKBundle, true);
  assert.equal(out.NF.kBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.kBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.kBundleReflectionProofRefsResolve, true);

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

  assert.equal(out.NF.pccPackLinkedToAcceptRun, true);
  assert.equal(out.NF.rowPackLinkedToPCCPack, true);
  assert.equal(out.NF.localPackagesLinkedToPCCPack, true);
  assert.equal(out.NF.globalFirewallsLinkedToPCCPack, true);
  assert.equal(out.NF.globalProofDAGLinkedToPCCPack, true);

  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner materialized generated accept-run accepts the concrete-chain run', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();
  const out = await CheckMaterializedGeneratedAcceptRun0(envelope.GeneratedAcceptRunEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedGeneratedAcceptRun0');
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects a non-concrete global proof DAG envelope', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedAcceptRunEnvelope = {
    ...envelope.GeneratedAcceptRunEnvelope,
    MaterializedPCCPack: {
      ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      GlobalProofDAGEnvelope: {
        ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.GlobalProofDAGEnvelope,
        kind: 'MaterializedGlobalProofDAG0',
      },
    },
  };

  envelope.ConcreteChain = summarizeConcreteGeneratedAcceptRunChain0(
    envelope.GeneratedAcceptRunEnvelope,
  );

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedAcceptRunEnvelopeDigest: undefined,
    materializedPCCPackDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'concreteGlobalProofDAG']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects stale ConcreteChain summary', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedAcceptRunEnvelope = {
    ...envelope.GeneratedAcceptRunEnvelope,
    MaterializedPCCPack: {
      ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      RowsEnvelope: {
        ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.RowsEnvelope,
        kind: 'MaterializedRows0',
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedAcceptRunEnvelopeDigest: undefined,
    materializedPCCPackDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain']);
});

test('writeConcreteMaterializedGeneratedAcceptRunFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-accept-run-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedGeneratedAcceptRunFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.generatedAcceptRunPath,
    result.files.concreteChainPath,
    result.files.acceptRunPath,
    result.files.pccPackPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects incomplete concrete HardCheck coverage', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedAcceptRunEnvelope = {
    ...envelope.GeneratedAcceptRunEnvelope,
    MaterializedPCCPack: {
      ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      HardEnvelope: {
        ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.HardEnvelope,
        Coverage: {
          ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.HardEnvelope.Coverage,
          noMinCoverageComplete: false,
        },
      },
    },
  };

  envelope.ConcreteChain = summarizeConcreteGeneratedAcceptRunChain0(
    envelope.GeneratedAcceptRunEnvelope,
  );

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedAcceptRunEnvelopeDigest: undefined,
    materializedPCCPackDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'hardNoMinCoverageComplete']);
});

test('CheckConcreteMaterializedGeneratedAcceptRun0 rejects incomplete concrete final-integration coverage', async () => {
  const envelope = await makeConcreteMaterializedGeneratedAcceptRun0();

  envelope.GeneratedAcceptRunEnvelope = {
    ...envelope.GeneratedAcceptRunEnvelope,
    MaterializedPCCPack: {
      ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack,
      FinalIntegrationEnvelope: {
        ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.FinalIntegrationEnvelope,
        ConcreteLinks: {
          ...envelope.GeneratedAcceptRunEnvelope.MaterializedPCCPack.FinalIntegrationEnvelope.ConcreteLinks,
          rowFamGCoverageComplete: false,
        },
      },
    },
  };

  envelope.ConcreteChain = summarizeConcreteGeneratedAcceptRunChain0(
    envelope.GeneratedAcceptRunEnvelope,
  );

  envelope.Linkage = {
    ...envelope.Linkage,
    generatedAcceptRunEnvelopeDigest: undefined,
    materializedPCCPackDigest: undefined,
    concreteChainDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGeneratedAcceptRun0(envelope, {
    checkGeneratedAcceptRun: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGeneratedAcceptRun0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGeneratedAcceptRun0.concreteChain');
  assert.deepEqual(out.Path, ['ConcreteChain', 'finalIntegrationRowFamGCoverageComplete']);
});

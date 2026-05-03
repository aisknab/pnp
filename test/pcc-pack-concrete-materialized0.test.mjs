import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedPCCPack0,
  makeConcreteMaterializedPCCPack0,
  summarizeConcretePCCPackCoverage0,
  writeConcreteMaterializedPCCPackFiles0,
} from '../pcc-pack-concrete-materialized0.mjs';

import {
  CheckMaterializedPCCPack0,
} from '../pcc-pack-materialized0.mjs';

test('CheckConcreteMaterializedPCCPack0 accepts the full concrete package chain', async () => {
  const envelope = await makeConcreteMaterializedPCCPack0();
  const out = await CheckConcreteMaterializedPCCPack0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedPCCPack0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedPCCPack0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.concreteKBundle, true);
  assert.equal(out.NF.kBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.kBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.kBundleReflectionProofRefsResolve, true);

  assert.equal(out.NF.concreteHardCheck, true);
  assert.equal(out.NF.hardCheckerCoverageComplete, true);
  assert.equal(out.NF.hardNoMinCoverageComplete, true);
  assert.equal(out.NF.hardImportPolicyComplete, true);

  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteGlobalFirewalls, true);
  assert.equal(out.NF.concreteGlobalProofDAG, true);

  assert.equal(out.NF.concreteFinalIntegration, true);
  assert.equal(out.NF.finalIntegrationGPackFieldCoverageComplete, true);
  assert.equal(out.NF.finalIntegrationRowFamGCoverageComplete, true);

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
});

test('inner MaterializedPCCPack checker accepts the concrete package envelope', async () => {
  const envelope = await makeConcreteMaterializedPCCPack0();
  const out = await CheckMaterializedPCCPack0(envelope.MaterializedPCCPackEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedPCCPack0');
});

test('CheckConcreteMaterializedPCCPack0 rejects incomplete HardCheck coverage', async () => {
  const envelope = await makeConcreteMaterializedPCCPack0();

  envelope.MaterializedPCCPackEnvelope = {
    ...envelope.MaterializedPCCPackEnvelope,
    HardEnvelope: {
      ...envelope.MaterializedPCCPackEnvelope.HardEnvelope,
      Coverage: {
        ...envelope.MaterializedPCCPackEnvelope.HardEnvelope.Coverage,
        noMinCoverageComplete: false,
      },
    },
  };

  envelope.ConcreteCoverage = summarizeConcretePCCPackCoverage0(envelope.MaterializedPCCPackEnvelope);
  envelope.Linkage = {
    ...envelope.Linkage,
    materializedPCCPackDigest: undefined,
    concreteCoverageDigest: undefined,
  };

  const out = await CheckConcreteMaterializedPCCPack0(envelope, {
    checkMaterializedPCCPack: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedPCCPack0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedPCCPack0.concreteCoverage');
  assert.deepEqual(out.Path, ['ConcreteCoverage', 'hardNoMinCoverageComplete']);
});

test('CheckConcreteMaterializedPCCPack0 rejects incomplete final-integration coverage', async () => {
  const envelope = await makeConcreteMaterializedPCCPack0();

  envelope.MaterializedPCCPackEnvelope = {
    ...envelope.MaterializedPCCPackEnvelope,
    FinalIntegrationEnvelope: {
      ...envelope.MaterializedPCCPackEnvelope.FinalIntegrationEnvelope,
      ConcreteLinks: {
        ...envelope.MaterializedPCCPackEnvelope.FinalIntegrationEnvelope.ConcreteLinks,
        rowFamGCoverageComplete: false,
      },
    },
  };

  envelope.ConcreteCoverage = summarizeConcretePCCPackCoverage0(envelope.MaterializedPCCPackEnvelope);
  envelope.Linkage = {
    ...envelope.Linkage,
    materializedPCCPackDigest: undefined,
    concreteCoverageDigest: undefined,
  };

  const out = await CheckConcreteMaterializedPCCPack0(envelope, {
    checkMaterializedPCCPack: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedPCCPack0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedPCCPack0.concreteCoverage');
  assert.deepEqual(out.Path, ['ConcreteCoverage', 'finalIntegrationRowFamGCoverageComplete']);
});

test('CheckConcreteMaterializedPCCPack0 rejects PCCPack/component drift', async () => {
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
    pccPackDigest: undefined,
    concreteCoverageDigest: undefined,
  };

  const out = await CheckConcreteMaterializedPCCPack0(envelope, {
    checkMaterializedPCCPack: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedPCCPack0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedPCCPack0.concreteCoverage');
  assert.deepEqual(out.Path, ['ConcreteCoverage', 'pccPackLinkedToHardCheck']);
});

test('CheckConcreteMaterializedPCCPack0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeConcreteMaterializedPCCPack0({
    overrides: {
      GateNote: 'synthetic marker must reject in strict marker mode',
    },
  });

  const out = await CheckConcreteMaterializedPCCPack0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedPCCPack0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedPCCPack0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteMaterializedPCCPackFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-pcc-pack-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedPCCPackFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.materializedPCCPackPath,
    result.files.pccPackPath,
    result.files.coveragePath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

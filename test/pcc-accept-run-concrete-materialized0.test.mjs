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

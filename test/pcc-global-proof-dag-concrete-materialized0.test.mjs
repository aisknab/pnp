import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedGlobalProofDAG0,
  makeConcreteMaterializedGlobalProofDAG0,
  writeConcreteMaterializedGlobalProofDAGFiles0,
} from '../pcc-global-proof-dag-concrete-materialized0.mjs';

import {
  CheckGlobalProofDAG0,
} from '../pcc-global-proof-dag0.mjs';

test('CheckConcreteMaterializedGlobalProofDAG0 accepts a global proof DAG over the concrete chain', async () => {
  const envelope = await makeConcreteMaterializedGlobalProofDAG0();
  const out = await CheckConcreteMaterializedGlobalProofDAG0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedGlobalProofDAG0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedGlobalProofDAG0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteGlobalFirewalls, true);
  assert.ok(out.NF.nodeCount > 0);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner CheckGlobalProofDAG0 accepts the concrete global proof DAG core', async () => {
  const envelope = await makeConcreteMaterializedGlobalProofDAG0();
  const out = await CheckGlobalProofDAG0(envelope.GlobalProofDAG);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalProofDAG0');
  assert.equal(out.NF.kind, 'GlobalProofDAG0NF');
  assert.equal(out.NF.nodeCount, envelope.GlobalProofDAG.Nodes.length);
});

test('CheckConcreteMaterializedGlobalProofDAG0 exposes concrete global firewall failures', async () => {
  const envelope = await makeConcreteMaterializedGlobalProofDAG0();

  envelope.ConcreteGlobalFirewallsEnvelope = {
    ...envelope.ConcreteGlobalFirewallsEnvelope,
    GlobalFirewalls: {
      ...envelope.ConcreteGlobalFirewallsEnvelope.GlobalFirewalls,
      SchedHash: {
        alg: 'SHA256',
        bytes: 'canonical-json-v0',
        hex: '0000000000000000000000000000000000000000000000000000000000000000',
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteGlobalFirewallsDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGlobalProofDAG0(envelope, {
    checkMaterializedGlobalProofDAG: false,
    checkGlobalProofDAG: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGlobalProofDAG0.ConcreteGlobalFirewalls');
});

test('CheckConcreteMaterializedGlobalProofDAG0 rejects a stale global proof DAG IfaceHash', async () => {
  const envelope = await makeConcreteMaterializedGlobalProofDAG0();

  envelope.GlobalProofDAG = {
    ...envelope.GlobalProofDAG,
    IfaceHash: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  envelope.MaterializedGlobalProofDAGEnvelope = {
    ...envelope.MaterializedGlobalProofDAGEnvelope,
    GlobalProofDAG: envelope.GlobalProofDAG,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    globalProofDAGDigest: undefined,
    materializedGlobalProofDAGDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGlobalProofDAG0(envelope, {
    checkMaterializedGlobalProofDAG: false,
    checkGlobalProofDAG: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGlobalProofDAG0.linkage');
  assert.deepEqual(out.Path, ['GlobalProofDAG', 'IfaceHash']);
});

test('CheckConcreteMaterializedGlobalProofDAG0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeConcreteMaterializedGlobalProofDAG0();

  envelope.GlobalProofDAG = {
    ...envelope.GlobalProofDAG,
    PiGlobalDAG: {
      ...envelope.GlobalProofDAG.PiGlobalDAG,
      note: 'synthetic marker must reject in strict marker mode',
    },
  };

  envelope.MaterializedGlobalProofDAGEnvelope = {
    ...envelope.MaterializedGlobalProofDAGEnvelope,
    GlobalProofDAG: envelope.GlobalProofDAG,
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    globalProofDAGDigest: undefined,
    materializedGlobalProofDAGDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGlobalProofDAG0(envelope, {
    allowSyntheticScaffoldMarker: false,
    checkMaterializedGlobalProofDAG: false,
    checkGlobalProofDAG: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGlobalProofDAG0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteMaterializedGlobalProofDAGFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-global-dag-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedGlobalProofDAGFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.globalProofDAGPath,
    result.files.materializedDAGPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('makeConcreteMaterializedGlobalProofDAG0 uses concrete KBundle proof coverage by default', async () => {
  const envelope = await makeConcreteMaterializedGlobalProofDAG0();

  assert.equal(envelope.KBundleEnvelope.kind, 'ConcreteMaterializedKBundle0');
  assert.equal(envelope.KBundleEnvelope.ProofInventory.kernelRuleCoverageComplete, true);
  assert.equal(envelope.KBundleEnvelope.ProofInventory.sigmaProofRefsResolve, true);
  assert.equal(envelope.KBundleEnvelope.ProofInventory.reflectionProofRefsResolve, true);

  const out = await CheckConcreteMaterializedGlobalProofDAG0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.concreteKBundle, true);
  assert.equal(out.NF.kBundleEnvelopeKind, 'ConcreteMaterializedKBundle0');
  assert.equal(out.NF.kBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.kBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.kBundleReflectionProofRefsResolve, true);
});

test('CheckConcreteMaterializedGlobalProofDAG0 rejects a non-concrete KBundle envelope', async () => {
  const envelope = await makeConcreteMaterializedGlobalProofDAG0();

  envelope.KBundleEnvelope = {
    ...envelope.KBundleEnvelope,
    kind: 'MaterializedKBundle0',
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    kBundleDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGlobalProofDAG0(envelope, {
    checkConcreteKBundle: false,
    checkKBundle: false,
    checkMaterializedGlobalProofDAG: false,
    checkGlobalProofDAG: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGlobalProofDAG0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGlobalProofDAG0.linkage');
  assert.deepEqual(out.Path, ['KBundleEnvelope', 'kind']);
});

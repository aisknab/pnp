import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedKBundle0,
  makeConcreteKBundleProofInventory0,
  makeConcreteMaterializedKBundle0,
  writeConcreteMaterializedKBundleFiles0,
} from '../pcc-k-concrete-materialized0.mjs';

import {
  CheckMaterializedKBundle0,
} from '../pcc-k-materialized0.mjs';

import {
  KERNEL_RULES0,
  REFLECTION_REQUIRED_CHECKERS0,
  SIGMA_REQUIRED_THEOREMS0,
} from '../pcc-kimpl0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

function refreshEnvelope0(envelope) {
  envelope.ProofInventory = makeConcreteKBundleProofInventory0(
    envelope.MaterializedKBundleEnvelope,
  );

  envelope.Boot0 = envelope.MaterializedKBundleEnvelope.Boot0;
  envelope.KImpl = envelope.MaterializedKBundleEnvelope.KImpl;
  envelope.K0 = envelope.MaterializedKBundleEnvelope.K0;
  envelope.PSigma = envelope.MaterializedKBundleEnvelope.PSigma;
  envelope.ReflectionRegistry = envelope.MaterializedKBundleEnvelope.ReflectionRegistry;

  envelope.Linkage = {
    ...envelope.Linkage,
    materializedKBundleDigest: digestCanonical0(envelope.MaterializedKBundleEnvelope),
    bootDigest: digestCanonical0(envelope.Boot0),
    kimplDigest: digestCanonical0(envelope.KImpl),
    k0Digest: digestCanonical0(envelope.K0),
    sigmaDigest: digestCanonical0(envelope.PSigma),
    reflectionDigest: digestCanonical0(envelope.ReflectionRegistry),
    proofInventoryDigest: digestCanonical0(envelope.ProofInventory),
    kernelRuleCount: envelope.ProofInventory.kernelRuleCount,
    conformanceNodeCount: envelope.ProofInventory.conformanceNodeCount,
    sigmaTheoremCount: envelope.ProofInventory.sigmaTheoremCount,
    reflectionCount: envelope.ProofInventory.reflectionCount,
  };

  return envelope;
}

test('CheckConcreteMaterializedKBundle0 accepts concrete proof coverage over the materialized KBundle', async () => {
  const envelope = await makeConcreteMaterializedKBundle0();
  const out = await CheckConcreteMaterializedKBundle0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedKBundle0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedKBundle0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.kernelRuleCoverageComplete, true);
  assert.equal(out.NF.sigmaCoverageComplete, true);
  assert.equal(out.NF.sigmaProofRefsResolve, true);
  assert.equal(out.NF.reflectionCoverageComplete, true);
  assert.equal(out.NF.reflectionProofRefsResolve, true);
  assert.equal(out.NF.noOpaqueProofRefs, true);
  assert.equal(out.NF.noExecutableMinSymbols, true);

  assert.equal(out.NF.kernelRuleCount, KERNEL_RULES0.length);
  assert.equal(out.NF.sigmaTheoremCount, SIGMA_REQUIRED_THEOREMS0.length);
  assert.equal(out.NF.reflectionCount, REFLECTION_REQUIRED_CHECKERS0.length);

  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner materialized KBundle checker accepts the concrete KBundle envelope core', async () => {
  const envelope = await makeConcreteMaterializedKBundle0();
  const out = await CheckMaterializedKBundle0(envelope.MaterializedKBundleEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedKBundle0');
  assert.equal(out.NF.kind, 'MaterializedKBundle0NF');
});

test('CheckConcreteMaterializedKBundle0 rejects unresolved Sigma proof references', async () => {
  const envelope = await makeConcreteMaterializedKBundle0();

  envelope.MaterializedKBundleEnvelope = {
    ...envelope.MaterializedKBundleEnvelope,
    PSigma: {
      ...envelope.MaterializedKBundleEnvelope.PSigma,
      theorems: envelope.MaterializedKBundleEnvelope.PSigma.theorems.map((entry, index) => (
        index === 0
          ? {
              ...entry,
              proofRefs: ['missing.k0.proof.ref'],
            }
          : entry
      )),
    },
  };

  refreshEnvelope0(envelope);

  const out = await CheckConcreteMaterializedKBundle0(envelope, {
    checkMaterializedKBundle: false,
    checkKBundle: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedKBundle0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedKBundle0.proofInventory');
  assert.deepEqual(out.Path, ['ProofInventory', 'sigmaProofRefsResolve']);
});

test('CheckConcreteMaterializedKBundle0 rejects unresolved reflection proof references', async () => {
  const envelope = await makeConcreteMaterializedKBundle0();

  envelope.MaterializedKBundleEnvelope = {
    ...envelope.MaterializedKBundleEnvelope,
    ReflectionRegistry: {
      ...envelope.MaterializedKBundleEnvelope.ReflectionRegistry,
      reflections: envelope.MaterializedKBundleEnvelope.ReflectionRegistry.reflections.map((entry, index) => (
        index === 0
          ? {
              ...entry,
              proofRefs: ['missing.k0.reflection.ref'],
            }
          : entry
      )),
    },
  };

  refreshEnvelope0(envelope);

  const out = await CheckConcreteMaterializedKBundle0(envelope, {
    checkMaterializedKBundle: false,
    checkKBundle: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedKBundle0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedKBundle0.proofInventory');
  assert.deepEqual(out.Path, ['ProofInventory', 'reflectionProofRefsResolve']);
});

test('CheckConcreteMaterializedKBundle0 rejects stale proof inventory', async () => {
  const envelope = await makeConcreteMaterializedKBundle0();

  envelope.MaterializedKBundleEnvelope = {
    ...envelope.MaterializedKBundleEnvelope,
    K0: {
      ...envelope.MaterializedKBundleEnvelope.K0,
      nodes: envelope.MaterializedKBundleEnvelope.K0.nodes.slice(1),
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    materializedKBundleDigest: undefined,
    k0Digest: undefined,
  };

  const out = await CheckConcreteMaterializedKBundle0(envelope, {
    checkMaterializedKBundle: false,
    checkKBundle: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedKBundle0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedKBundle0.proofInventory');
  assert.deepEqual(out.Path, ['ProofInventory']);
});

test('CheckConcreteMaterializedKBundle0 rejects opaque proof marker text', async () => {
  const envelope = await makeConcreteMaterializedKBundle0();

  envelope.MaterializedKBundleEnvelope = {
    ...envelope.MaterializedKBundleEnvelope,
    K0: {
      ...envelope.MaterializedKBundleEnvelope.K0,
      nodes: envelope.MaterializedKBundleEnvelope.K0.nodes.map((node, index) => (
        index === 0
          ? {
              ...node,
              Payload: {
                ...node.Payload,
                note: 'opaque-proof marker must reject',
              },
            }
          : node
      )),
    },
  };

  refreshEnvelope0(envelope);

  const out = await CheckConcreteMaterializedKBundle0(envelope, {
    checkMaterializedKBundle: false,
    checkKBundle: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedKBundle0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedKBundle0.proofInventory');
  assert.deepEqual(out.Path, ['ProofInventory', 'noOpaqueProofRefs']);
});

test('CheckConcreteMaterializedKBundle0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeConcreteMaterializedKBundle0({
    overrides: {
      GateNote: 'synthetic marker must reject in strict marker mode',
    },
  });

  const out = await CheckConcreteMaterializedKBundle0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedKBundle0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedKBundle0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteMaterializedKBundleFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-kbundle-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedKBundleFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.materializedKBundlePath,
    result.files.proofInventoryPath,
    result.files.kimplPath,
    result.files.k0Path,
    result.files.sigmaPath,
    result.files.reflectionPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

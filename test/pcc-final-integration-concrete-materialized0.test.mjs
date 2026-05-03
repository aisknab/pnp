import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedFinalIntegration0,
  makeConcreteFinalIntegrationLinks0,
  makeConcreteMaterializedFinalIntegration0,
  writeConcreteMaterializedFinalIntegrationFiles0,
} from '../pcc-final-integration-concrete-materialized0.mjs';

import {
  CheckMaterializedFinalIntegration0,
} from '../pcc-final-integration-materialized0.mjs';

test('CheckConcreteMaterializedFinalIntegration0 accepts final integration over the concrete DAG chain', async () => {
  const envelope = await makeConcreteMaterializedFinalIntegration0();
  const out = await CheckConcreteMaterializedFinalIntegration0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalIntegration0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedFinalIntegration0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);

  assert.equal(out.NF.concreteGlobalProofDAG, true);
  assert.equal(out.NF.concreteKBundle, true);
  assert.equal(out.NF.concreteRows, true);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteGlobalFirewalls, true);

  assert.equal(out.NF.kBundleKernelRuleCoverageComplete, true);
  assert.equal(out.NF.kBundleSigmaProofRefsResolve, true);
  assert.equal(out.NF.kBundleReflectionProofRefsResolve, true);

  assert.equal(out.NF.gpackFieldCoverageComplete, true);
  assert.equal(out.NF.rowFamGCoverageComplete, true);
  assert.equal(out.NF.finalIntegrationUsesGPack, true);
  assert.equal(out.NF.rowFamGUsesGPack, true);
  assert.equal(out.NF.finalTheoremUsesFinalIntegration, true);
  assert.equal(out.NF.rowFamFinalUsesFinalTheorem, true);
  assert.equal(out.NF.finalMatchUsesGPack, true);
  assert.equal(out.NF.satDecisionUsesGPack, true);

  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner materialized final integration checker accepts the concrete final integration core', async () => {
  const envelope = await makeConcreteMaterializedFinalIntegration0();
  const out = await CheckMaterializedFinalIntegration0(envelope.FinalIntegrationEnvelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedFinalIntegration0');
  assert.equal(out.NF.kind, 'MaterializedFinalIntegration0NF');
});

test('CheckConcreteMaterializedFinalIntegration0 rejects stale concrete links', async () => {
  const envelope = await makeConcreteMaterializedFinalIntegration0();

  envelope.FinalIntegrationEnvelope = {
    ...envelope.FinalIntegrationEnvelope,
    RowFamG: {
      ...envelope.FinalIntegrationEnvelope.RowFamG,
      rows: envelope.FinalIntegrationEnvelope.RowFamG.rows.slice(1),
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    materializedFinalIntegrationDigest: undefined,
    concreteLinksDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalIntegration0(envelope, {
    checkConcreteGlobalProofDAG: false,
    checkMaterializedFinalIntegration: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalIntegration0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalIntegration0.concreteLinks');
  assert.deepEqual(out.Path, ['ConcreteLinks']);
});

test('CheckConcreteMaterializedFinalIntegration0 rejects non-concrete global proof DAG link', async () => {
  const envelope = await makeConcreteMaterializedFinalIntegration0();

  envelope.ConcreteGlobalProofDAGEnvelope = {
    ...envelope.ConcreteGlobalProofDAGEnvelope,
    kind: 'MaterializedGlobalProofDAG0',
  };

  envelope.ConcreteLinks = makeConcreteFinalIntegrationLinks0({
    concreteGlobalProofDAGEnvelope: envelope.ConcreteGlobalProofDAGEnvelope,
    finalIntegrationEnvelope: envelope.FinalIntegrationEnvelope,
  });

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteGlobalProofDAGDigest: undefined,
    concreteLinksDigest: undefined,
  };

  const out = await CheckConcreteMaterializedFinalIntegration0(envelope, {
    checkConcreteGlobalProofDAG: false,
    checkMaterializedFinalIntegration: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalIntegration0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalIntegration0.concreteLinks');
  assert.deepEqual(out.Path, ['ConcreteLinks', 'concreteGlobalProofDAG']);
});

test('CheckConcreteMaterializedFinalIntegration0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeConcreteMaterializedFinalIntegration0({
    overrides: {
      GateNote: 'synthetic marker must reject in strict marker mode',
    },
  });

  const out = await CheckConcreteMaterializedFinalIntegration0(envelope, {
    allowSyntheticScaffoldMarker: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedFinalIntegration0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedFinalIntegration0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteMaterializedFinalIntegrationFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-final-integration-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedFinalIntegrationFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.finalIntegrationEnvelopePath,
    result.files.concreteGlobalProofDAGPath,
    result.files.gpackPath,
    result.files.finalTheoremPath,
    result.files.linksPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

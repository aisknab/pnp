import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedScaffoldBurndown0,
  makeMaterializedScaffoldBurndown0,
  makeMaterializedScaffoldInventory0,
  writeMaterializedScaffoldBurndownFiles0,
} from '../pcc-materialized-scaffold-burndown0.mjs';

const makeHistoricalScaffold0 = (options = {}) => makeMaterializedScaffoldBurndown0({
  ...options,
  historicalReplay: true,
});
const CheckHistoricalScaffold0 = (input, config = {}) => CheckMaterializedScaffoldBurndown0(input, {
  ...config,
  historicalReplay: true,
});
const writeHistoricalScaffold0 = (dir, options = {}) => writeMaterializedScaffoldBurndownFiles0(dir, {
  ...options,
  historicalReplay: true,
});

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

function refreshEnvelope0(envelope) {
  envelope.Inventory = makeMaterializedScaffoldInventory0(
    envelope.FinalCertificatePublicStatusEnvelope,
  );

  envelope.Linkage = {
    ...envelope.Linkage,
    targetDigest: digestCanonical0(envelope.FinalCertificatePublicStatusEnvelope),
    inventoryDigest: digestCanonical0(envelope.Inventory),
    markerHitCount: envelope.Inventory.hitCount,
    syntheticMarkerCount: envelope.Inventory.syntheticMarkerCount,
    forbiddenMarkerCount: envelope.Inventory.forbiddenMarkerCount,
  };

  return envelope;
}

test('CheckMaterializedScaffoldBurndown0 accepts the current materialized chain in audit mode', async () => {
  const envelope = await makeHistoricalScaffold0();
  const out = await CheckHistoricalScaffold0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedScaffoldBurndown0');
  assert.equal(out.NF.kind, 'MaterializedScaffoldBurndown0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.ok(['clean', 'scaffolded'].includes(out.NF.status));
  assert.equal(Number.isInteger(out.NF.markerHitCount), true);
  assert.equal(out.NF.markerHitCount >= 0, true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedScaffoldBurndown0 strict mode rejects a synthetic scaffold marker', async () => {
  const envelope = await makeHistoricalScaffold0();

  envelope.FinalCertificatePublicStatusEnvelope = {
    ...envelope.FinalCertificatePublicStatusEnvelope,
    ScaffoldWitness: 'synthetic scaffold marker for strict-mode rejection',
  };

  refreshEnvelope0(envelope);

  const out = await CheckHistoricalScaffold0(envelope, {
    mode: 'strict',
    checkFinalCertificatePublicStatus: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedScaffoldBurndown0');
  assert.equal(out.Coord, 'CheckMaterializedScaffoldBurndown0.policy');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('CheckMaterializedScaffoldBurndown0 audit mode rejects forbidden marker text', async () => {
  const envelope = await makeHistoricalScaffold0();

  envelope.FinalCertificatePublicStatusEnvelope = {
    ...envelope.FinalCertificatePublicStatusEnvelope,
    BadScaffoldWitness: 'todo marker must reject',
  };

  refreshEnvelope0(envelope);

  const out = await CheckHistoricalScaffold0(envelope, {
    checkFinalCertificatePublicStatus: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedScaffoldBurndown0');
  assert.equal(out.Coord, 'CheckMaterializedScaffoldBurndown0.policy');
  assert.equal(out.Witness.detail.hit.marker, 'todo');
});

test('CheckMaterializedScaffoldBurndown0 rejects stale marker inventory', async () => {
  const envelope = await makeHistoricalScaffold0();

  envelope.FinalCertificatePublicStatusEnvelope = {
    ...envelope.FinalCertificatePublicStatusEnvelope,
    ScaffoldWitness: 'synthetic marker after stale inventory',
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    targetDigest: undefined,
  };

  const out = await CheckHistoricalScaffold0(envelope, {
    checkFinalCertificatePublicStatus: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedScaffoldBurndown0');
  assert.equal(out.Coord, 'CheckMaterializedScaffoldBurndown0.inventory');
  assert.deepEqual(out.Path, ['Inventory']);
});

test('writeMaterializedScaffoldBurndownFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-scaffold-burndown-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeHistoricalScaffold0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.inventoryPath,
    result.files.targetPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

test('materialized scaffold burndown routes reject without historical replay opt-in', async () => {
  const made = await makeMaterializedScaffoldBurndown0();
  const checked = await CheckMaterializedScaffoldBurndown0();
  const written = await writeMaterializedScaffoldBurndownFiles0('/tmp/not-written-without-opt-in');
  for (const out of [made, checked, written]) {
    assert.equal(out.tag, 'reject');
    assert.match(out.coord, /\.HistoricalReplayRequired$/u);
  }
});

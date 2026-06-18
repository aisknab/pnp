import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedAcceptanceBridge0,
  CheckMaterializedAcceptanceBridgeFile0,
  MATERIALIZED_ACCEPTANCE_BRIDGE_PHASES0,
  makeAcceptedMaterializedAcceptanceBridge0,
  makeMaterializedAcceptanceBridge0,
} from '../pcc-materialized-acceptance-bridge0.mjs';

import {
  MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
  sha256Utf8DigestRecord0,
} from '../pcc-materialized-pack0.mjs';

import {
  stableStringify0,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedAcceptanceBridge0 accepts pending bridge without public conclusion', async () => {
  const out = await CheckMaterializedAcceptanceBridge0(makeMaterializedAcceptanceBridge0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridge0');
  assert.equal(out.NF.kind, 'MaterializedAcceptanceBridge0NF');
  assert.deepEqual(out.NF.phaseOrder, MATERIALIZED_ACCEPTANCE_BRIDGE_PHASES0);
  assert.equal(out.NF.checkPCCPackexpStatus, 'pending-real-check');
  assert.equal(out.NF.replayVerdict, 'pending');
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion, null);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedAcceptanceBridge0 accepts accepted replay and emits conditional public conclusion', async () => {
  const out = await CheckMaterializedAcceptanceBridge0(makeAcceptedMaterializedAcceptanceBridge0());

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridge0');
  assert.equal(out.NF.checkPCCPackexpStatus, 'accepted');
  assert.equal(out.NF.replayVerdict, 'accept');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.deepEqual(out.NF.publicConclusion, MATERIALIZED_PACK_PUBLIC_BOUNDARY0);
});

test('CheckMaterializedAcceptanceBridgeFile0 accepts an accepted bridge file', async (t) => {
  const filePath = await writeTempBridgeFile0(t, makeAcceptedMaterializedAcceptanceBridge0());

  const out = await CheckMaterializedAcceptanceBridgeFile0(filePath);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.NF.kind, 'MaterializedAcceptanceBridgeFile0NF');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.replayVerdict, 'accept');
});

test('CheckMaterializedAcceptanceBridge0 rejects public conclusion before accepted replay', async () => {
  const bridge = makeMaterializedAcceptanceBridge0();

  bridge.BridgeVerdict = {
    ...bridge.BridgeVerdict,
    verdict: 'accept',
    publicConclusionEmitted: true,
    publicConclusion: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
  };

  const out = await CheckMaterializedAcceptanceBridge0(bridge);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridge0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptanceBridge0.BridgeVerdict');
  assert.deepEqual(out.Path, ['BridgeVerdict', 'verdict']);
  assert.equal(out.Witness.reason, 'BridgeVerdict verdict does not match acceptance and replay state');
});

test('CheckMaterializedAcceptanceBridge0 rejects accepted replay without accepted CheckPCCPackexp precondition', async () => {
  const bridge = makeMaterializedAcceptanceBridge0({
    replayVerdict: 'accept',
  });

  bridge.ExternalAcceptRunReplay = {
    ...bridge.ExternalAcceptRunReplay,
    replayAccepted: true,
    RejectLog: [],
  };

  const out = await CheckMaterializedAcceptanceBridge0(bridge);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridge0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptanceBridge0.ExternalAcceptRunReplay');
  assert.deepEqual(out.Path, ['ExternalAcceptRunReplay', 'verdict']);
  assert.equal(out.Witness.reason, 'external accept replay requires accepted CheckPCCPackexp precondition');
});

test('CheckMaterializedAcceptanceBridge0 rejects CheckPCCPackexp using digest-only equality', async () => {
  const bridge = makeMaterializedAcceptanceBridge0();

  bridge.CheckPCCPackexp = {
    ...bridge.CheckPCCPackexp,
    noDigestOnlyEquality: false,
  };

  const out = await CheckMaterializedAcceptanceBridge0(bridge);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridge0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptanceBridge0.CheckPCCPackexp');
  assert.deepEqual(out.Path, ['CheckPCCPackexp', 'noDigestOnlyEquality']);
  assert.equal(out.Witness.reason, 'CheckPCCPackexp bridge must certify noDigestOnlyEquality');
});

test('CheckMaterializedAcceptanceBridge0 rejects if aggregate precondition fails', async () => {
  const bridge = makeMaterializedAcceptanceBridge0();
  const pack = JSON.parse(bridge.Shell.PackBytes);

  pack.Manifest.packageImportEdges = [
    {
      from: 'O',
      to: 'G',
    },
  ];

  bridge.Shell.PackBytes = stableStringify0(pack);
  bridge.Shell.PackDigest = sha256Utf8DigestRecord0(bridge.Shell.PackBytes);

  const out = await CheckMaterializedAcceptanceBridge0(bridge);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridge0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptanceBridge0.aggregate');
  assert.deepEqual(out.Path, ['Shell']);
  assert.equal(out.Witness.reason, 'CheckMaterializedAggregate0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterializedAggregate0.CheckMaterializedImports0');
});

test('CheckMaterializedAcceptanceBridge0 rejects direct public conclusion emission by replay record', async () => {
  const bridge = makeAcceptedMaterializedAcceptanceBridge0();

  bridge.ExternalAcceptRunReplay = {
    ...bridge.ExternalAcceptRunReplay,
    publicConclusionEmitted: true,
    publicConclusion: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
  };

  const out = await CheckMaterializedAcceptanceBridge0(bridge);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridge0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptanceBridge0.ExternalAcceptRunReplay');
  assert.deepEqual(out.Path, ['ExternalAcceptRunReplay', 'publicConclusion']);
  assert.equal(out.Witness.reason, 'ExternalAcceptRunReplay must not emit the public conclusion directly');
});

test('CheckMaterializedAcceptanceBridge0 accepts rejected bridge but emits no public conclusion', async () => {
  const bridge = makeMaterializedAcceptanceBridge0({
    checkStatus: 'rejected',
    replayVerdict: 'reject',
  });

  const out = await CheckMaterializedAcceptanceBridge0(bridge);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridge0');
  assert.equal(out.NF.checkPCCPackexpStatus, 'rejected');
  assert.equal(out.NF.replayVerdict, 'reject');
  assert.equal(out.NF.publicConclusionEmitted, false);
  assert.equal(out.NF.publicConclusion, null);
});

test('CheckMaterializedAcceptanceBridgeFile0 rejects invalid JSON bridge file', async (t) => {
  const filePath = await writeTempTextFile0(t, '{ not json');

  const out = await CheckMaterializedAcceptanceBridgeFile0(filePath);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.Coord, 'CheckMaterializedAcceptanceBridgeFile0.load');
  assert.deepEqual(out.Path, ['file']);
  assert.equal(out.Witness.reason, 'materialized acceptance bridge file must parse as JSON');
});

async function writeTempBridgeFile0(t, bridge) {
  return writeTempTextFile0(t, JSON.stringify(bridge, null, 2));
}

async function writeTempTextFile0(t, text) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-acceptance-bridge-'));
  const filePath = path.join(dir, 'MaterializedAcceptanceBridge0.json');

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  await fs.writeFile(filePath, text, 'utf8');

  return filePath;
}
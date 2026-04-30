import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { fileURLToPath } from 'node:url';

import {
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

test('bin/check-materialized-acceptance-bridge0.mjs accepts a pending bridge and emits no public conclusion', async (t) => {
  const filePath = await writeTempBridgeFile0(t, makeMaterializedAcceptanceBridge0());
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-acceptance-bridge0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.replayVerdict, 'pending');
  assert.equal(out.publicConclusionEmitted, false);
  assert.match(out.fileDigest.hex, /^[0-9a-f]{64}$/);
  assert.match(out.digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/check-materialized-acceptance-bridge0.mjs accepts an accepted bridge and records public conclusion emission', async (t) => {
  const filePath = await writeTempBridgeFile0(t, makeAcceptedMaterializedAcceptanceBridge0());
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-acceptance-bridge0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.replayVerdict, 'accept');
  assert.equal(out.publicConclusionEmitted, true);
  assert.match(out.bridgeDigest.hex, /^[0-9a-f]{64}$/);
});

test('bin/check-materialized-acceptance-bridge0.mjs --full emits the complete accepted bridge record', async (t) => {
  const filePath = await writeTempBridgeFile0(t, makeAcceptedMaterializedAcceptanceBridge0());
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-acceptance-bridge0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath, '--full'], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.NF.kind, 'MaterializedAcceptanceBridgeFile0NF');
  assert.equal(out.NF.publicConclusionEmitted, true);
  assert.equal(out.NF.replayVerdict, 'accept');
  assert.equal(Array.isArray(out.Ledger), true);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('bin/check-materialized-acceptance-bridge0.mjs accepts a rejected bridge but emits no public conclusion', async (t) => {
  const bridge = makeMaterializedAcceptanceBridge0({
    checkStatus: 'rejected',
    replayVerdict: 'reject',
  });

  const filePath = await writeTempBridgeFile0(t, bridge);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-acceptance-bridge0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 0, child.stderr);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.replayVerdict, 'reject');
  assert.equal(out.publicConclusionEmitted, false);
});

test('bin/check-materialized-acceptance-bridge0.mjs rejects public conclusion before accepted replay', async (t) => {
  const bridge = makeMaterializedAcceptanceBridge0();

  bridge.BridgeVerdict = {
    ...bridge.BridgeVerdict,
    verdict: 'accept',
    publicConclusionEmitted: true,
    publicConclusion: {
      ...MATERIALIZED_PACK_PUBLIC_BOUNDARY0,
    },
  };

  const filePath = await writeTempBridgeFile0(t, bridge);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-acceptance-bridge0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.coord, 'CheckMaterializedAcceptanceBridgeFile0.bridge');
  assert.equal(out.witness.detail.inner.coord, 'CheckMaterializedAcceptanceBridge0.BridgeVerdict');
});

test('bin/check-materialized-acceptance-bridge0.mjs rejects if aggregate precondition fails', async (t) => {
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

  const filePath = await writeTempBridgeFile0(t, bridge);
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-acceptance-bridge0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.coord, 'CheckMaterializedAcceptanceBridgeFile0.bridge');
  assert.equal(out.witness.detail.inner.coord, 'CheckMaterializedAcceptanceBridge0.aggregate');
});

test('bin/check-materialized-acceptance-bridge0.mjs rejects invalid JSON bridge file', async (t) => {
  const filePath = await writeTempTextFile0(t, '{ not json');
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-acceptance-bridge0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath, filePath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedAcceptanceBridgeFile0');
  assert.equal(out.coord, 'CheckMaterializedAcceptanceBridgeFile0.load');
  assert.equal(out.witness.reason, 'materialized acceptance bridge file must parse as JSON');
});

test('bin/check-materialized-acceptance-bridge0.mjs exits nonzero without a file path', () => {
  const cliPath = fileURLToPath(new URL('../bin/check-materialized-acceptance-bridge0.mjs', import.meta.url));

  const child = spawnSync(process.execPath, [cliPath], {
    encoding: 'utf8',
  });

  assert.equal(child.status, 1);

  const out = JSON.parse(child.stdout);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'check-materialized-acceptance-bridge0');
  assert.equal(out.coord, 'check-materialized-acceptance-bridge0.args');
});

async function writeTempBridgeFile0(t, bridge) {
  return writeTempTextFile0(t, JSON.stringify(bridge, null, 2));
}

async function writeTempTextFile0(t, text) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-acceptance-bridge-cli-'));
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
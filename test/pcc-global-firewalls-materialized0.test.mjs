import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedGlobalFirewalls0,
  makeMaterializedGlobalFirewalls0,
  writeMaterializedGlobalFirewallsFiles0,
} from '../pcc-global-firewalls-materialized0.mjs';

import {
  CheckBounds0,
  CheckGlobalFirewalls0,
  CheckImportGraph0,
  CheckNoHiddenMin0,
  GLOBAL_FIREWALL_PHASES0,
} from '../pcc-global-firewalls0.mjs';

test('CheckMaterializedGlobalFirewalls0 accepts a materialized global-firewalls envelope', async () => {
  const envelope = makeMaterializedGlobalFirewalls0();
  const out = await CheckMaterializedGlobalFirewalls0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedGlobalFirewalls0');
  assert.equal(out.NF.kind, 'MaterializedGlobalFirewalls0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.deepEqual(out.NF.phases, GLOBAL_FIREWALL_PHASES0);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner GlobalFirewalls checker accepts the materialized firewalls core', async () => {
  const envelope = makeMaterializedGlobalFirewalls0();
  const out = await CheckGlobalFirewalls0(envelope.GlobalFirewalls);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckGlobalFirewalls0');
  assert.equal(out.NF.kind, 'GlobalFirewalls0NF');
  assert.deepEqual(out.NF.phases, GLOBAL_FIREWALL_PHASES0);
});

test('materialized subphase checkers accept ImportGraph, NoHiddenMinScan, and Bounds', async () => {
  const envelope = makeMaterializedGlobalFirewalls0();

  const importGraph = await CheckImportGraph0(envelope.GlobalFirewalls.ImportGraph);
  const noHiddenMin = await CheckNoHiddenMin0(envelope.GlobalFirewalls.NoHiddenMinScan);
  const bounds = await CheckBounds0(envelope.GlobalFirewalls.Bounds);

  assert.equal(importGraph.tag, 'accept');
  assert.equal(noHiddenMin.tag, 'accept');
  assert.equal(bounds.tag, 'accept');
});

test('CheckMaterializedGlobalFirewalls0 exposes forbidden import edge failures', async () => {
  const envelope = makeMaterializedGlobalFirewalls0();

  envelope.GlobalFirewalls = {
    ...envelope.GlobalFirewalls,
    ImportGraph: {
      ...envelope.GlobalFirewalls.ImportGraph,
      edges: [
        ...envelope.GlobalFirewalls.ImportGraph.edges,
        {
          from: 'O',
          to: 'G',
          kind: 'Import',
          reason: 'forbidden test edge',
        },
      ],
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    globalFirewallsDigest: undefined,
  };

  const out = await CheckMaterializedGlobalFirewalls0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGlobalFirewalls0');
  assert.equal(out.Coord, 'CheckMaterializedGlobalFirewalls0.GlobalFirewalls');
  assert.equal(out.Witness.detail.inner.coord, 'CheckGlobalFirewalls0.imports');
});

test('CheckMaterializedGlobalFirewalls0 rejects forbidden fixture marker text', async () => {
  const envelope = makeMaterializedGlobalFirewalls0();

  envelope.GlobalFirewalls = {
    ...envelope.GlobalFirewalls,
    PiFirewalls: {
      ...envelope.GlobalFirewalls.PiFirewalls,
      note: 'todo marker must reject',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    globalFirewallsDigest: undefined,
  };

  const out = await CheckMaterializedGlobalFirewalls0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGlobalFirewalls0');
  assert.equal(out.Coord, 'CheckMaterializedGlobalFirewalls0.fixtureMarkers');
});

test('CheckMaterializedGlobalFirewalls0 rejects stale local linkage', async () => {
  const envelope = makeMaterializedGlobalFirewalls0();

  envelope.GlobalFirewalls = {
    ...envelope.GlobalFirewalls,
    SchedHash: {
      alg: 'SHA256',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    globalFirewallsDigest: undefined,
  };

  const out = await CheckMaterializedGlobalFirewalls0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGlobalFirewalls0');
  assert.equal(out.Coord, 'CheckMaterializedGlobalFirewalls0.linkage');
  assert.deepEqual(out.Path, ['GlobalFirewalls', 'SchedHash']);
});

test('CheckMaterializedGlobalFirewalls0 rejects stale linkage digest', async () => {
  const envelope = makeMaterializedGlobalFirewalls0();

  envelope.Linkage = {
    ...envelope.Linkage,
    globalFirewallsDigest: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckMaterializedGlobalFirewalls0(envelope);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedGlobalFirewalls0');
  assert.equal(out.Coord, 'CheckMaterializedGlobalFirewalls0.linkage');
  assert.deepEqual(out.Path, ['Linkage', 'globalFirewallsDigest']);
});

test('writeMaterializedGlobalFirewallsFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-global-firewalls-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeMaterializedGlobalFirewallsFiles0(dir);

  assert.equal(result.checked.tag, 'accept');

  for (const filePath of [
    result.files.envelopePath,
    result.files.localPackagesPath,
    result.files.globalFirewallsPath,
    result.files.importGraphPath,
    result.files.noHiddenMinPath,
    result.files.boundsPath,
    result.files.checkPath,
  ]) {
    const text = await fs.readFile(filePath, 'utf8');
    const value = JSON.parse(text);

    assert.equal(typeof value, 'object');
  }
});

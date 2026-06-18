import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckConcreteMaterializedGlobalFirewalls0,
  makeConcreteMaterializedGlobalFirewalls0,
  writeConcreteMaterializedGlobalFirewallsFiles0,
} from '../pcc-global-firewalls-concrete-materialized0.mjs';

import {
  CheckGlobalFirewalls0,
  CheckImportGraph0,
  CheckNoHiddenMin0,
  CheckBounds0,
  GLOBAL_FIREWALL_PHASES0,
} from '../pcc-global-firewalls0.mjs';

test('CheckConcreteMaterializedGlobalFirewalls0 accepts global firewalls over concrete local packages', async () => {
  const envelope = await makeConcreteMaterializedGlobalFirewalls0();
  const out = await CheckConcreteMaterializedGlobalFirewalls0(envelope);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckConcreteMaterializedGlobalFirewalls0');
  assert.equal(out.NF.kind, 'ConcreteMaterializedGlobalFirewalls0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.concreteLocalPackages, true);
  assert.equal(out.NF.concreteLocalPackagesEnvelopeKind, 'ConcreteMaterializedLocalPackages0');
  assert.deepEqual(out.NF.phases, GLOBAL_FIREWALL_PHASES0);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('inner global firewall and subphase checkers accept the concrete global firewall core', async () => {
  const envelope = await makeConcreteMaterializedGlobalFirewalls0();

  const global = await CheckGlobalFirewalls0(envelope.GlobalFirewalls);
  const imports = await CheckImportGraph0(envelope.GlobalFirewalls.ImportGraph);
  const noMin = await CheckNoHiddenMin0(envelope.GlobalFirewalls.NoHiddenMinScan);
  const bounds = await CheckBounds0(envelope.GlobalFirewalls.Bounds);

  assert.equal(global.tag, 'accept');
  assert.equal(imports.tag, 'accept');
  assert.equal(noMin.tag, 'accept');
  assert.equal(bounds.tag, 'accept');
});

test('CheckConcreteMaterializedGlobalFirewalls0 exposes concrete local-package failures', async () => {
  const envelope = await makeConcreteMaterializedGlobalFirewalls0();

  envelope.ConcreteLocalPackagesEnvelope = {
    ...envelope.ConcreteLocalPackagesEnvelope,
    LocalPackages: {
      ...envelope.ConcreteLocalPackagesEnvelope.LocalPackages,
      RowPackDigest: {
        alg: 'SHA256',
        bytes: 'canonical-json-v0',
        hex: '0000000000000000000000000000000000000000000000000000000000000000',
      },
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    concreteLocalPackagesDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGlobalFirewalls0(envelope, {
    checkMaterializedGlobalFirewalls: false,
    checkGlobalFirewalls: false,
    checkSubphases: false,
    checkLinkage: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGlobalFirewalls0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGlobalFirewalls0.ConcreteLocalPackages');
  assert.equal(out.Witness.detail.inner.coord, 'CheckConcreteMaterializedLocalPackages0.MaterializedLocalPackages');
});

test('CheckConcreteMaterializedGlobalFirewalls0 rejects a stale SchedHash linkage', async () => {
  const envelope = await makeConcreteMaterializedGlobalFirewalls0();

  envelope.GlobalFirewalls = {
    ...envelope.GlobalFirewalls,
    SchedHash: {
      alg: 'SHA256',
      bytes: 'canonical-json-v0',
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    globalFirewallsDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGlobalFirewalls0(envelope, {
    checkMaterializedGlobalFirewalls: false,
    checkGlobalFirewalls: false,
    checkSubphases: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGlobalFirewalls0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGlobalFirewalls0.linkage');
  assert.deepEqual(out.Path, ['GlobalFirewalls', 'SchedHash']);
});

test('CheckConcreteMaterializedGlobalFirewalls0 strictly rejects an injected synthetic scaffold marker', async () => {
  const envelope = await makeConcreteMaterializedGlobalFirewalls0();

  envelope.GlobalFirewalls = {
    ...envelope.GlobalFirewalls,
    PiFirewalls: {
      ...envelope.GlobalFirewalls.PiFirewalls,
      note: 'synthetic marker must reject in strict marker mode',
    },
  };

  envelope.Linkage = {
    ...envelope.Linkage,
    globalFirewallsDigest: undefined,
  };

  const out = await CheckConcreteMaterializedGlobalFirewalls0(envelope, {
    allowSyntheticScaffoldMarker: false,
    checkMaterializedGlobalFirewalls: false,
    checkGlobalFirewalls: false,
    checkSubphases: false,
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckConcreteMaterializedGlobalFirewalls0');
  assert.equal(out.Coord, 'CheckConcreteMaterializedGlobalFirewalls0.fixtureMarkers');
  assert.equal(out.Witness.detail.hit.marker, 'synthetic');
});

test('writeConcreteMaterializedGlobalFirewallsFiles0 writes replayable JSON artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-concrete-global-firewalls-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const result = await writeConcreteMaterializedGlobalFirewallsFiles0(dir);

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

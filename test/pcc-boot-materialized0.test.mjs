import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedBoot0,
  makeMaterializedBoot0,
  makeMaterializedBootAuditSuite0,
  writeMaterializedBoot0Files0,
} from '../pcc-boot-materialized0.mjs';

import {
  makeAcceptCase,
} from '../pcc-verifier-frag0.mjs';

test('CheckMaterializedBoot0 accepts a JSON-materialized Boot0 seed', async () => {
  const boot = await makeMaterializedBoot0();
  const out = await CheckMaterializedBoot0(boot);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedBoot0');
  assert.equal(out.NF.kind, 'MaterializedBoot0NF');
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.jsonMaterializable, true);
  assert.equal(out.NF.precomputedAudit, true);
  assert.equal(out.NF.noFixtureMarkers, true);
  assert.equal(out.NF.rowCount, boot.B0.rows.length);
  assert.equal(out.NF.kernelRuleCount, 16);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('makeMaterializedBoot0 embeds concrete interface digest in every B0 row', async () => {
  const boot = await makeMaterializedBoot0();
  const out = await CheckMaterializedBoot0(boot);

  assert.equal(out.tag, 'accept');

  for (const row of boot.B0.rows) {
    assert.equal(row.IfaceHash, out.NF.ifaceDigest.hex);
  }
});

test('CheckMaterializedBoot0 rejects non-JSON audit suites with functions', async () => {
  const boot = await makeMaterializedBoot0();

  boot.BootAudit0 = {
    kind: 'VerifierFrag0',
    version: 0,
    suiteId: 'boot0.materialized.audit.raw-suite',
    cases: [
      makeAcceptCase({
        id: 'boot0.materialized.raw-suite.accepts',
        target: 'raw-suite',
        run: () => ({ tag: 'accept' }),
      }),
    ],
  };

  const out = await CheckMaterializedBoot0(boot);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckMaterializedBoot0.json');
  assert.deepEqual(out.Path, ['BootAudit0', 'cases', 0, 'run']);
});

test('CheckMaterializedBoot0 rejects fixture marker strings', async () => {
  const boot = await makeMaterializedBoot0();

  boot.PiBoot.marker = 'synthetic';

  const out = await CheckMaterializedBoot0(boot);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckMaterializedBoot0.noFixtureMarkers');
  assert.deepEqual(out.Path, ['PiBoot', 'marker']);
});

test('materialized Boot0 audit suite accepts B0 and rejects negative tamper cases', async () => {
  const boot = await makeMaterializedBoot0();
  const suite = makeMaterializedBootAuditSuite0({
    B0: boot.B0,
  });

  assert.equal(suite.kind, 'VerifierFrag0');
  assert.equal(suite.suiteId, 'boot0.materialized.audit');
  assert.equal(suite.cases.length, 3);
});

test('writeMaterializedBoot0Files0 writes deterministic JSON artefacts', async () => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-boot0-'));

  try {
    const out = await writeMaterializedBoot0Files0(dir);

    assert.equal(out.tag, 'accept');
    assert.equal(out.checker, 'WriteMaterializedBoot0Files0');
    assert.equal(out.NF.files.length, 2);

    const bootPath = path.join(dir, 'Boot0.json');
    const checkPath = path.join(dir, 'MaterializedBoot0.check.json');
    const bootText = await fs.readFile(bootPath, 'utf8');
    const checkText = await fs.readFile(checkPath, 'utf8');

    assert.doesNotThrow(() => JSON.parse(bootText));
    assert.doesNotThrow(() => JSON.parse(checkText));
    assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
  } finally {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  }
});

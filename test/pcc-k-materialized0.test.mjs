import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { test } from 'node:test';

import {
  CheckMaterializedKBundle0,
  MATERIALIZED_KBUNDLE_PHASES0,
  MATERIALIZED_KBUNDLE_REQUIRED_FILES0,
  makeMaterializedKBundle0,
  writeMaterializedKBundleFiles0,
} from '../pcc-k-materialized0.mjs';

import {
  KERNEL_RULES0,
} from '../pcc-kimpl0.mjs';

test('CheckMaterializedKBundle0 accepts a JSON-materialized KImpl/K0/Sigma/reflection bundle', async () => {
  const bundle = await makeMaterializedKBundle0();
  const out = await CheckMaterializedKBundle0(bundle);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterializedKBundle0');
  assert.equal(out.NF.kind, 'MaterializedKBundle0NF');
  assert.deepEqual(out.NF.phaseOrder, MATERIALIZED_KBUNDLE_PHASES0);
  assert.equal(out.NF.materializedPath, true);
  assert.equal(out.NF.syntheticRunAll, false);
  assert.equal(out.NF.bootLinked, true);
  assert.equal(out.NF.jsonMaterializable, true);
  assert.equal(out.NF.noFixtureMarkers, true);
  assert.equal(out.NF.kernelRuleCount, KERNEL_RULES0.length);
  assert.equal(out.NF.conformanceNodeCount, KERNEL_RULES0.length);
  assert.equal(out.NF.sigmaTheoremCount, 2);
  assert.equal(out.NF.reflectionCount, 5);
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterializedKBundle0 rejects when KImpl does not link to the materialized Boot0 IfaceDict digest', async () => {
  const bundle = await makeMaterializedKBundle0();

  bundle.KImpl = {
    ...bundle.KImpl,
    IfaceHash: {
      ...bundle.KImpl.IfaceHash,
      hex: '0000000000000000000000000000000000000000000000000000000000000000',
    },
  };

  const out = await CheckMaterializedKBundle0(bundle);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedKBundle0');
  assert.equal(out.Coord, 'CheckMaterializedKBundle0.bootLinks');
  assert.deepEqual(out.Path, ['KImpl', 'IfaceHash']);
});

test('CheckMaterializedKBundle0 rejects fixture-marker text in the materialized K bundle', async () => {
  const bundle = await makeMaterializedKBundle0();

  bundle.KImpl = {
    ...bundle.KImpl,
    PiK: {
      ...bundle.KImpl.PiK,
      note: 'synthetic marker should not occur in materialized kernel data',
    },
  };

  const out = await CheckMaterializedKBundle0(bundle);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedKBundle0');
  assert.equal(out.Coord, 'CheckMaterializedKBundle0.noFixtureMarkers');
  assert.equal(out.Witness.detail.marker, 'synthetic');
});

test('CheckMaterializedKBundle0 rejects missing Sigma theorem coverage through CheckKBundle0', async () => {
  const bundle = await makeMaterializedKBundle0();

  bundle.PSigma = {
    ...bundle.PSigma,
    theorems: bundle.PSigma.theorems.filter((entry) => !String(entry.id).includes('V54')),
  };

  const out = await CheckMaterializedKBundle0(bundle);

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterializedKBundle0');
  assert.equal(out.Coord, 'CheckMaterializedKBundle0.CheckKBundle0');
  assert.equal(out.Witness.reason, 'CheckKBundle0 rejected');
});

test('writeMaterializedKBundleFiles0 writes deterministic materialized K bundle artefacts', async (t) => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'pnp-materialized-kbundle-'));

  t.after(async () => {
    await fs.rm(dir, {
      recursive: true,
      force: true,
    });
  });

  const out = await writeMaterializedKBundleFiles0(dir);

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'WriteMaterializedKBundleFiles0');
  assert.equal(out.NF.fileCount, MATERIALIZED_KBUNDLE_REQUIRED_FILES0.length);

  for (const fileName of MATERIALIZED_KBUNDLE_REQUIRED_FILES0) {
    const text = await fs.readFile(path.join(dir, fileName), 'utf8');
    assert.equal(text.endsWith('\n'), true);
    assert.doesNotThrow(() => JSON.parse(text));
  }
});

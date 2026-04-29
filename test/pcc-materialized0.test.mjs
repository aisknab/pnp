import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckMaterialized0,
  makeMaterializedGateConfig0,
} from '../pcc-materialized0.mjs';

import {
  RunAll0,
  makeSyntheticRunAllInput0,
} from '../pcc-runall0.mjs';

test('CheckMaterialized0 accepts a concrete non-synthetic object', async () => {
  const out = await CheckMaterialized0({
    kind: 'ConcreteObject0',
    version: 0,
    digest: {
      alg: 'SHA256',
      hex: '0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef',
    },
    payload: {
      value: 'materialized-object',
    },
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckMaterialized0');
  assert.equal(out.NF.kind, 'Materialized0NF');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckMaterialized0 rejects synthetic text', async () => {
  const out = await CheckMaterialized0({
    kind: 'ConcreteObject0',
    payload: {
      label: 'sched.synthetic',
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterialized0');
  assert.equal(out.Coord, 'CheckMaterialized0.scan');
  assert.deepEqual(out.Path, ['payload', 'label']);
  assert.equal(out.Witness.reason, 'materialized mode rejects synthetic or placeholder text');
});

test('CheckMaterialized0 rejects placeholder note fields', async () => {
  const out = await CheckMaterialized0({
    kind: 'ConcreteObject0',
    proof: {
      note: 'real proof goes here',
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterialized0');
  assert.equal(out.Coord, 'CheckMaterialized0.scan');
  assert.deepEqual(out.Path, ['proof', 'note']);
  assert.equal(out.Witness.reason, 'materialized mode rejects placeholder note fields');
});

test('CheckMaterialized0 rejects non-SHA digest hex fields', async () => {
  const out = await CheckMaterialized0({
    kind: 'ConcreteObject0',
    digest: {
      alg: 'SHA256',
      hex: 'sched.synthetic',
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterialized0');
  assert.equal(out.Coord, 'CheckMaterialized0.scan');
  assert.deepEqual(out.Path, ['digest', 'hex']);
  assert.equal(out.Witness.reason, 'materialized mode requires SHA256 hex digest fields to be concrete');
});

test('CheckMaterialized0 rejects opaque proof material', async () => {
  const out = await CheckMaterialized0({
    kind: 'ConcreteObject0',
    proofBlob: {
      bytes: 'not allowed',
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckMaterialized0');
  assert.equal(out.Coord, 'CheckMaterialized0.scan');
  assert.deepEqual(out.Path, ['proofBlob']);
  assert.equal(out.Witness.reason, 'materialized mode rejects opaque proof material');
});

test('RunAll0 still accepts synthetic engineering fixtures by default', async () => {
  const out = await RunAll0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.NF.requireMaterialized, false);
});

test('RunAll0 materialized mode rejects the synthetic pipeline before integration replay', async () => {
  const out = await RunAll0(makeSyntheticRunAllInput0({
    RequireMaterialized: true,
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.Coord, 'RunAll0.materialized');
  assert.deepEqual(out.Path.slice(0, 1), ['Pipeline']);
  assert.equal(out.Witness.reason, 'CheckMaterialized0 rejected');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterialized0.scan');
});

test('RunAll0 validates materialized config shape', async () => {
  const out = await RunAll0(makeSyntheticRunAllInput0({
    RequireMaterialized: true,
    MaterializedConfig: {
      ...makeMaterializedGateConfig0(),
      rejectSyntheticText: 'yes',
    },
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.Coord, 'RunAll0.materialized');
  assert.equal(out.Witness.detail.inner.coord, 'CheckMaterialized0.config');
  assert.deepEqual(out.Witness.detail.inner.path, ['rejectSyntheticText']);
});
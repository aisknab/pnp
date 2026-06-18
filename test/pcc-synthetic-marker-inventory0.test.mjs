import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckSyntheticMarkerInventory0,
  SYNTHETIC_MARKER_ALLOWED_CLASSES0,
  classifySyntheticMarkerHit0,
  findSyntheticMarkersInValue0,
  makeSyntheticMarkerInventoryConfig0,
} from '../pcc-synthetic-marker-inventory0.mjs';

import {
  makeSyntheticRunAllInput0,
} from '../pcc-runall0.mjs';

import {
  digestCanonical0,
} from '../pcc-verifier-frag0.mjs';

test('CheckSyntheticMarkerInventory0 accepts the current classified synthetic marker inventory', async () => {
  const out = await CheckSyntheticMarkerInventory0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckSyntheticMarkerInventory0');
  assert.equal(out.NF.kind, 'SyntheticMarkerInventory0NF');
  assert.equal(out.NF.sourceHitCount > 0, true);
  assert.equal(out.NF.valueHitCount > 0, true);
  assert.equal(out.NF.materializedBlockerCount > 0, true);
  assert.equal(out.NF.materializedGateRejected, true);
  assert.equal(out.NF.materializedGateCoord, 'RunAll0.materialized');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('findSyntheticMarkersInValue0 finds synthetic and note markers in synthetic RunAll input', () => {
  const hits = findSyntheticMarkersInValue0(makeSyntheticRunAllInput0(), {
    rootPath: ['RunAllInput0'],
  });

  assert.equal(hits.length > 0, true);
  assert.equal(hits.some((hit) => hit.marker === 'synthetic'), true);
  assert.equal(hits.some((hit) => hit.path.includes('note')), true);
});

test('classifySyntheticMarkerHit0 classifies value markers as materialized blockers', () => {
  const classification = classifySyntheticMarkerHit0({
    sourceKind: 'value',
    path: ['RunAllInput0', 'Pipeline'],
    marker: 'synthetic',
    value: 'sched.synthetic',
  });

  assert.equal(classification, 'materialized-mode-blocker');
  assert.equal(SYNTHETIC_MARKER_ALLOWED_CLASSES0.includes(classification), true);
});

test('classifySyntheticMarkerHit0 classifies test source markers as engineering fixtures', () => {
  const classification = classifySyntheticMarkerHit0({
    sourceKind: 'test',
    file: 'test/example.test.mjs',
    marker: 'synthetic',
  });

  assert.equal(classification, 'engineering-fixture-test');
  assert.equal(SYNTHETIC_MARKER_ALLOWED_CLASSES0.includes(classification), true);
});

test('classifySyntheticMarkerHit0 classifies implementation source markers as engineering fixtures', () => {
  const classification = classifySyntheticMarkerHit0({
    sourceKind: 'source',
    file: 'pcc-runall0.mjs',
    marker: 'synthetic',
  });

  assert.equal(classification, 'engineering-fixture-source');
  assert.equal(SYNTHETIC_MARKER_ALLOWED_CLASSES0.includes(classification), true);
});

test('CheckSyntheticMarkerInventory0 rejects if the materialized gate does not reject synthetic input', async () => {
  const out = await CheckSyntheticMarkerInventory0(makeSyntheticMarkerInventoryConfig0({
    scanSourceFiles: false,
    scanTests: false,
    materializedRunner: async () => ({
      tag: 'accept',
      kind: 'accept',
      checker: 'BadMaterializedRunner0',
      NF: {
        kind: 'BadMaterializedRunner0NF',
      },
      Digest: digestCanonical0({
        kind: 'BadMaterializedRunner0NF',
      }),
      Ledger: [],
    }),
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckSyntheticMarkerInventory0');
  assert.equal(out.Coord, 'CheckSyntheticMarkerInventory0.materializedGate');
  assert.deepEqual(out.Path, ['RunAll0']);
  assert.equal(out.Witness.reason, 'materialized gate did not reject the synthetic RunAll input');
});

test('CheckSyntheticMarkerInventory0 validates config shape', async () => {
  const out = await CheckSyntheticMarkerInventory0({
    ...makeSyntheticMarkerInventoryConfig0(),
    scanTests: 'yes',
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckSyntheticMarkerInventory0');
  assert.equal(out.Coord, 'CheckSyntheticMarkerInventory0.config');
  assert.deepEqual(out.Path, ['scanTests']);
  assert.equal(out.Witness.reason, 'SyntheticMarkerInventoryConfig0 scanTests must be boolean');
});
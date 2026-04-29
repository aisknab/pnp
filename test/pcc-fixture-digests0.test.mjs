import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  findInvalidFixtureDigestHexLiterals0,
  fixtureDigestHex0,
  fixtureDigestRecord0,
  isSha256Hex0,
} from '../pcc-fixture-digests0.mjs';

import {
  RunAll0,
} from '../pcc-runall0.mjs';

test('fixtureDigestHex0 emits deterministic SHA256-shaped hex strings', () => {
  const first = fixtureDigestHex0('sched.synthetic');
  const second = fixtureDigestHex0('sched.synthetic');
  const third = fixtureDigestHex0('iface.synthetic');

  assert.equal(first, second);
  assert.notEqual(first, third);
  assert.equal(isSha256Hex0(first), true);
  assert.match(first, /^[0-9a-f]{64}$/);
});

test('fixtureDigestRecord0 emits digest records with concrete hex', () => {
  const digest = fixtureDigestRecord0('rowpack.synthetic');

  assert.equal(digest.alg, 'SHA256');
  assert.equal(isSha256Hex0(digest.hex), true);
});

test('implementation modules contain no static non-SHA digest hex literals', async () => {
  const invalid = await findInvalidFixtureDigestHexLiterals0();

  assert.deepEqual(invalid, []);
});

test('RunAll0 still accepts synthetic engineering fixtures after fixture digest hardening', async () => {
  const out = await RunAll0();

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'RunAll0');
  assert.equal(out.NF.status, 'complete');
  assert.equal(out.NF.finalVerdict, 'accept');
  assert.equal(out.NF.publicConclusion.consequent, 'P = NP');
});
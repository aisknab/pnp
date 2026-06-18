import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckVerifierFrag0,
  makeAcceptCase,
  makeAuditCase,
  makeRejectCase,
} from '../pcc-verifier-frag0.mjs';

test('CheckVerifierFrag0 accepts a passing mixed audit suite', async () => {
  const out = await CheckVerifierFrag0({
    kind: 'VerifierFrag0',
    version: 0,
    suiteId: 'frag0.runner.accept',
    cases: [
      makeAuditCase({
        id: 'assertion.pass',
        target: 'runner',
        polarity: 'positive',
        run: () => {
          assert.equal(1 + 1, 2);
        },
      }),
      makeAcceptCase({
        id: 'accept.record',
        target: 'runner',
        run: () => ({
          tag: 'accept',
          payload: {
            ok: true,
          },
        }),
      }),
      makeRejectCase({
        id: 'reject.record',
        target: 'runner',
        run: () => ({
          tag: 'reject',
          coord: 'synthetic.reject',
        }),
      }),
      makeRejectCase({
        id: 'reject.throw',
        target: 'runner',
        run: () => {
          throw new Error('synthetic rejection');
        },
      }),
    ],
  });

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckVerifierFrag0');
  assert.equal(out.NF.caseCount, 4);
  assert.equal(out.NF.positiveCount, 2);
  assert.equal(out.NF.negativeCount, 2);
  assert.equal(out.Ledger.length, 4);
  assert.equal(out.Ledger.every((entry) => entry.status === 'pass'), true);
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckVerifierFrag0 rejects at the unique first failing case', async () => {
  const out = await CheckVerifierFrag0({
    kind: 'VerifierFrag0',
    version: 0,
    suiteId: 'frag0.runner.first-failure',
    cases: [
      makeAuditCase({
        id: 'case.a',
        target: 'runner',
        run: () => {
          assert.equal(true, true);
        },
      }),
      makeAuditCase({
        id: 'case.b',
        target: 'runner',
        run: () => {
          assert.equal(10, 11);
        },
      }),
      makeAuditCase({
        id: 'case.c',
        target: 'runner',
        run: () => {
          assert.equal(false, false);
        },
      }),
    ],
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.checker, 'CheckVerifierFrag0');
  assert.match(out.Coord, /CheckVerifierFrag0\.case\.0001\.case\.b/);
  assert.deepEqual(out.Path, ['cases', 1, 'case.b']);
  assert.equal(out.Ledger.length, 2);
  assert.equal(out.Ledger[0].status, 'pass');
  assert.equal(out.Ledger[1].status, 'fail');
  assert.equal(out.Witness.id, 'case.b');
  assert.equal(out.Digest.alg, 'SHA256');
  assert.match(out.Digest.hex, /^[0-9a-f]{64}$/);
});

test('CheckVerifierFrag0 fails a negative case that does not reject', async () => {
  const out = await CheckVerifierFrag0({
    kind: 'VerifierFrag0',
    version: 0,
    suiteId: 'frag0.runner.bad-negative',
    cases: [
      makeRejectCase({
        id: 'negative.accepted',
        target: 'runner',
        run: () => ({
          tag: 'accept',
        }),
      }),
    ],
  });

  assert.equal(out.tag, 'reject');
  assert.match(out.Coord, /negative\.accepted/);
  assert.equal(out.Witness.expected, 'reject');
  assert.equal(out.Witness.observed, 'accept-record');
});

test('CheckVerifierFrag0 rejects duplicate case ids before running cases', async () => {
  const out = await CheckVerifierFrag0({
    kind: 'VerifierFrag0',
    version: 0,
    suiteId: 'frag0.runner.duplicate-id',
    cases: [
      makeAuditCase({
        id: 'duplicate',
        target: 'runner',
        run: () => undefined,
      }),
      makeAuditCase({
        id: 'duplicate',
        target: 'runner',
        run: () => undefined,
      }),
    ],
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckVerifierFrag0.input');
  assert.deepEqual(out.Path, ['cases', 1, 'id']);
  assert.equal(out.Witness.reason, 'case ids must be unique');
});
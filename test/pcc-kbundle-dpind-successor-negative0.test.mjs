import assert from 'node:assert/strict';
import { test } from 'node:test';

import { makeKImplFiniteExhaustSuccessor0 } from '../pcc-kimpl-finiteexhaust-successor0.mjs';
import {
  CheckKBundleDPIndFinalTheoremReadiness0,
  CheckKBundleDPIndSuccessor0,
  makeKBundleDPIndSuccessor0,
} from '../pcc-kbundle-dpind-successor0.mjs';

test('explicit DPInd KBundle final gate rejects a development record', async () => {
  const out = await CheckKBundleDPIndFinalTheoremReadiness0(
    makeKBundleDPIndSuccessor0(),
  );
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleDPIndFinalTheoremReadiness0.purpose');
});

test('DPInd KBundle rejects caller readiness assertions', async () => {
  const input = makeKBundleDPIndSuccessor0();
  input.finalTheoremReady = true;
  const out = await CheckKBundleDPIndSuccessor0(input);
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleDPIndSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
});

test('DPInd KBundle rejects a stale FiniteExhaust child', async () => {
  const input = makeKBundleDPIndSuccessor0();
  input.SemanticKImpl = makeKImplFiniteExhaustSuccessor0();
  const out = await CheckKBundleDPIndSuccessor0(input);
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleDPIndSuccessor0.semanticKImpl');
  assert.equal(
    out.Witness.inner.witness.reason,
    'DPInd successor KImpl kind must be KImplSemanticDPIndSuccessor0',
  );
});

test('DPInd KBundle rejects weakened policy and propagates Sigma failure', async () => {
  const weakened = makeKBundleDPIndSuccessor0();
  weakened.Policy.predecessorKBundleCannotImplyDPIndReadiness = false;
  const weakenedOut = await CheckKBundleDPIndSuccessor0(weakened);
  assert.equal(weakenedOut.tag, 'reject');
  assert.deepEqual(weakenedOut.Path, ['Policy']);

  const badSigma = makeKBundleDPIndSuccessor0();
  badSigma.PSigma.theorems = badSigma.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );
  const sigmaOut = await CheckKBundleDPIndSuccessor0(badSigma);
  assert.equal(sigmaOut.tag, 'reject');
  assert.equal(sigmaOut.Coord, 'CheckKBundleDPIndSuccessor0.predecessorKBundle');
});

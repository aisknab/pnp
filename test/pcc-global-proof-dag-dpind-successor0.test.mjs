import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleFiniteExhaustSuccessor0,
} from '../pcc-kbundle-finiteexhaust-successor0.mjs';

import {
  CheckGlobalProofDAGDPIndFinalTheoremReadiness0,
  CheckGlobalProofDAGDPIndSuccessor0,
  makeGlobalProofDAGDPIndSuccessor0,
} from '../pcc-global-proof-dag-dpind-successor0.mjs';

test('DPInd global gate accepts development input', async () => {
  const out = await CheckGlobalProofDAGDPIndSuccessor0(
    makeGlobalProofDAGDPIndSuccessor0(),
  );
  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.semanticOverlay.semanticKernelNodeIds.includes('K.DPInd'), true);
  assert.equal(out.NF.semanticOverlay.blockedKernelNodeIds.length, 7);
  assert.deepEqual(out.NF.activeFinalNodeIds, []);
  assert.equal(out.NF.legacyFinalNodesQuarantined, true);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
});

test('DPInd global gate rejects final purpose while readiness is blocked', async () => {
  const out = await CheckGlobalProofDAGDPIndSuccessor0(
    makeGlobalProofDAGDPIndSuccessor0({ Purpose: 'final-theorem' }),
  );
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGDPIndSuccessor0.semanticReadiness');
  assert.equal(out.Witness.blockers.length, 2);
});

test('explicit DPInd global final gate rejects a development record', async () => {
  const out = await CheckGlobalProofDAGDPIndFinalTheoremReadiness0(
    makeGlobalProofDAGDPIndSuccessor0(),
  );
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGDPIndFinalTheoremReadiness0.purpose');
});

test('DPInd global gate rejects caller readiness and stale bundle state', async () => {
  const asserted = makeGlobalProofDAGDPIndSuccessor0();
  asserted.finalTheoremReady = true;
  const assertedOut = await CheckGlobalProofDAGDPIndSuccessor0(asserted);
  assert.equal(assertedOut.tag, 'reject');
  assert.deepEqual(assertedOut.Path, ['finalTheoremReady']);

  const stale = makeGlobalProofDAGDPIndSuccessor0();
  stale.KBundle = makeKBundleFiniteExhaustSuccessor0();
  const staleOut = await CheckGlobalProofDAGDPIndSuccessor0(stale);
  assert.equal(staleOut.tag, 'reject');
  assert.equal(staleOut.Coord, 'CheckGlobalProofDAGDPIndSuccessor0.semanticKBundle');
});

test('DPInd global gate rejects weakened quarantine policy', async () => {
  const input = makeGlobalProofDAGDPIndSuccessor0();
  input.Policy.predecessorGlobalGateCannotImplyDPIndReadiness = false;
  const out = await CheckGlobalProofDAGDPIndSuccessor0(input);
  assert.equal(out.tag, 'reject');
  assert.deepEqual(out.Path, ['Policy']);
});

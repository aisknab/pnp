import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
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
});

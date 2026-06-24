import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckGlobalProofDAGFinalPrefixSuccessor0,
} from '../pcc-global-proof-dag-final-prefix-successor0.mjs';

import {
  makeFinalPrefixSuccessorInput0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

test('final-prefix overlay binds both nodes to checked refinement digests', async () => {
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(
    makeFinalPrefixSuccessorInput0(),
  );

  assert.equal(out.tag, 'accept');
  const byId = new Map(
    out.NF.globalFinalPrefixRefinementDigests.map((entry) => [entry.nodeId, entry]),
  );
  for (const binding of out.NF.semanticOverlay.semanticFinalPrefixBindings) {
    const refinement = byId.get(binding.nodeId);
    assert.equal(binding.refinementDigest.hex, refinement.digest.hex);
    assert.equal(binding.globalNodeDigest.hex, refinement.globalNodeDigest.hex);
    assert.equal(binding.dependencyNodeDigest.hex, refinement.dependencyNodeDigest.hex);
    assert.equal(binding.sourceRecordDigest.hex, refinement.sourceRecordDigest.hex);
    assert.equal(binding.positiveRecordDigest.hex, refinement.positiveRecordDigest.hex);
    assert.equal(binding.negativeRecordDigest.hex, refinement.negativeRecordDigest.hex);
    assert.equal(binding.checkerContractDigest.hex, refinement.checkerContractDigest.hex);
    assert.equal(binding.conclusionDigest.hex, refinement.conclusionDigest.hex);
    assert.equal(binding.publiclyActive, false);
  }
  assert.equal(
    out.NF.computedGlobalGate.nodes.find(
      (node) => node.id === 'Gate.GlobalDAG.FinalPrefixRefinements',
    ).ready,
    true,
  );
  assert.equal(
    out.NF.computedGlobalGate.nodes.find(
      (node) => node.id === 'Gate.FinalTheorem.Readiness',
    ).ready,
    false,
  );
});

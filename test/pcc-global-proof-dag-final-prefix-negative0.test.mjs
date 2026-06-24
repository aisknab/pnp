import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKBundleSigmaSuccessor0,
} from '../pcc-kbundle-sigma-successor0.mjs';

import {
  CheckGlobalProofDAGFinalPrefixSuccessor0,
  makeGlobalProofDAGFinalPrefixSuccessor0,
} from '../pcc-global-proof-dag-final-prefix-successor0.mjs';

import {
  makeFinalPrefixSuccessorInput0,
} from './helpers/pcc-global-final-prefix-fixture0.mjs';

test('final-prefix successor rejects a final-purpose child KBundle', async () => {
  const input = makeFinalPrefixSuccessorInput0();
  input.KBundle.Purpose = 'final-theorem';
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalPrefixSuccessor0.input');
  assert.deepEqual(out.Path, ['KBundle', 'Purpose']);
});

test('final-prefix successor rejects a stale Sigma-only KBundle at the package predecessor', async () => {
  const input = makeGlobalProofDAGFinalPrefixSuccessor0({
    KBundle: makeKBundleSigmaSuccessor0(),
  });
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalPrefixSuccessor0.predecessorGlobal');
  assert.equal(
    out.Witness.reason,
    'semantic package predecessor global gate rejected before final-prefix upgrade',
  );
});

test('final-prefix successor rejects a stale prefix binding digest', async () => {
  const input = makeFinalPrefixSuccessorInput0();
  input.FinalPrefixSemanticDerivations = {
    ...input.FinalPrefixSemanticDerivations,
    refinements: input.FinalPrefixSemanticDerivations.refinements.map((entry, index) => (
      index === 1
        ? {
            ...entry,
            packCoreDigest: {
              alg: 'SHA256',
              hex: '0'.repeat(64),
            },
          }
        : entry
    )),
  };
  const out = await CheckGlobalProofDAGFinalPrefixSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckGlobalProofDAGFinalPrefixSuccessor0.semanticFinalPrefix');
  assert.equal(
    out.Witness.reason,
    'bounded semantic final-prefix refinement checker rejected',
  );
});

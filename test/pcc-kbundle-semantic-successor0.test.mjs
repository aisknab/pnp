import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckKBundleSemanticFinalTheoremReadiness0,
  CheckKBundleSemanticSuccessor0,
  makeKBundleSemanticSuccessor0,
} from '../pcc-kbundle-semantic-successor0.mjs';

test('semantic KBundle accepts partial work only as development-only', async () => {
  const out = await CheckKBundleSemanticSuccessor0(
    makeKBundleSemanticSuccessor0(),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKBundleSemanticSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.semanticKImplDevelopmentAccepted, true);
  assert.equal(out.NF.semanticKImplDevelopmentOnly, true);
  assert.equal(out.NF.semanticKImplPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.legacyBundleAccepted, true);
  assert.equal(out.NF.legacyConformanceSemanticStatus, 'structural-only');
  assert.equal(out.NF.legacySigmaSemanticStatus, 'registry-shape-only');
  assert.equal(out.NF.legacyReflectionSemanticStatus, 'mapping-shape-only');
  assert.equal(out.NF.semanticConformanceReady, false);
  assert.equal(out.NF.semanticSigmaReady, false);
  assert.equal(out.NF.semanticReflectionReady, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.deepEqual(
    out.NF.computedReadiness.blockerCoordinates,
    [
      'KImpl.SemanticRuleCoverage',
      'K0.SemanticConformance',
      'Sigma.SemanticDerivations',
      'Reflection.SemanticSoundness',
    ],
  );
  assert.deepEqual(
    out.NF.semanticKImplSupportedRules,
    ['Eq', 'Subst', 'Record', 'DAGInd'],
  );
  assert.equal(out.NF.semanticKImplMissingRules.length, 12);
});

test('semantic KBundle rejects final-theorem purpose while semantic surfaces are incomplete', async () => {
  const out = await CheckKBundleSemanticSuccessor0(
    makeKBundleSemanticSuccessor0({ Purpose: 'final-theorem' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSemanticSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['ComputedReadiness']);
  assert.equal(
    out.Witness.reason,
    'semantic KBundle is not ready for final-theorem use',
  );
  assert.equal(out.Witness.blockers.length, 4);
});

test('explicit semantic KBundle final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKBundleSemanticFinalTheoremReadiness0(
    makeKBundleSemanticSuccessor0({ Purpose: 'development' }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKBundleSemanticFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'semantic KBundle final readiness requires a final-theorem purpose record',
  );
});

test('semantic KBundle rejects caller-supplied readiness assertions', async () => {
  const input = makeKBundleSemanticSuccessor0();
  input.finalTheoremReady = true;
  input.publicTheoremEmissionAllowed = true;

  const out = await CheckKBundleSemanticSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSemanticSuccessor0.input');
  assert.deepEqual(out.Path, ['finalTheoremReady']);
  assert.equal(
    out.Witness.reason,
    'semantic KBundle rejects caller-supplied readiness assertions',
  );
});

test('semantic KBundle rejects a caller-provided final-purpose child KImpl', async () => {
  const input = makeKBundleSemanticSuccessor0();
  input.SemanticKImpl.Purpose = 'final-theorem';

  const out = await CheckKBundleSemanticSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSemanticSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKImpl', 'Purpose']);
  assert.equal(
    out.Witness.reason,
    'semantic KBundle input KImpl must remain development-purpose; final readiness is recomputed internally',
  );
});

test('semantic KBundle rejects a weakened release policy', async () => {
  const input = makeKBundleSemanticSuccessor0();
  input.Policy.finalTheoremRequiresSemanticReflectionSoundness = false;

  const out = await CheckKBundleSemanticSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSemanticSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'semantic KBundle release policy must match the fail-closed policy',
  );
});

test('semantic KBundle propagates legacy Sigma structural rejection', async () => {
  const input = makeKBundleSemanticSuccessor0();
  input.PSigma.theorems = input.PSigma.theorems.filter(
    (entry) => !String(entry.id).includes('V54'),
  );

  const out = await CheckKBundleSemanticSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSemanticSuccessor0.legacyBundle');
  assert.equal(out.Witness.reason, 'legacy KBundle structural checker rejected');
  assert.equal(out.Witness.inner.witness.reason, 'CheckSigmaRegistry0 rejected');
});

test('semantic KBundle rejects an invalid semantic proof before structural aggregation', async () => {
  const x = makeSemanticVar0('x', 'Bool');
  const y = makeSemanticVar0('y', 'Bool');
  const invalidProof = makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'eq.invalid',
      RuleName: 'Eq',
      Conclusion: makeSemanticEqJudgment0(x, y),
      Payload: { op: 'refl' },
    }),
  ]);
  const input = makeKBundleSemanticSuccessor0({
    SemanticProofDAG: invalidProof,
  });

  const out = await CheckKBundleSemanticSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKBundleSemanticSuccessor0.semanticKImpl');
  assert.equal(out.Witness.reason, 'development semantic KImpl successor rejected');
});

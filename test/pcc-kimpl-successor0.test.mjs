import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckKImplFinalTheoremReadiness0,
  CheckKImplSuccessor0,
  makeKImplSuccessor0,
} from '../pcc-kimpl-successor0.mjs';

function makeEqProof0({ invalid = false } = {}) {
  const x = makeSemanticVar0('x', 'Bool');
  const y = makeSemanticVar0('y', 'Bool');

  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'semantic.eq.refl',
      RuleName: 'Eq',
      Conclusion: makeSemanticEqJudgment0(x, invalid ? y : x),
      Payload: { op: 'refl' },
    }),
  ]);
}

test('successor KImpl accepts partial semantic work only as development-only', async () => {
  const out = await CheckKImplSuccessor0(makeKImplSuccessor0({
    SemanticProofDAG: makeEqProof0(),
    Purpose: 'development',
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.legacyKImplAccepted, true);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticKernelReady, false);
  assert.equal(out.NF.developmentOnly, true);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticRuleUniverseMatchesLegacyKImpl, true);
  assert.equal(out.NF.missingSemanticRules.includes('Record'), true);
  assert.equal(out.NF.missingSemanticRules.includes('Eq'), false);
  assert.equal(out.NF.missingSemanticRules.includes('Subst'), false);
});

test('successor KImpl rejects final-theorem purpose while semantic coverage is incomplete', async () => {
  const out = await CheckKImplSuccessor0(makeKImplSuccessor0({
    SemanticProofDAG: makeEqProof0(),
    Purpose: 'final-theorem',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(out.Witness.reason, 'successor KImpl is not ready for final-theorem use');
  assert.equal(out.Witness.missingRules.includes('Record'), true);
});

test('final-theorem gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplFinalTheoremReadiness0(makeKImplSuccessor0({
    SemanticProofDAG: makeEqProof0(),
    Purpose: 'development',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFinalTheoremReadiness0.purpose');
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'final-theorem readiness requires a final-theorem purpose record',
  );
});

test('final-theorem gate rejects an explicit final record until readiness accepts', async () => {
  const out = await CheckKImplFinalTheoremReadiness0(makeKImplSuccessor0({
    SemanticProofDAG: makeEqProof0(),
    Purpose: 'final-theorem',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplFinalTheoremReadiness0.semanticReadiness');
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('successor KImpl rejects caller-supplied readiness assertions', async () => {
  const input = makeKImplSuccessor0({
    SemanticProofDAG: makeEqProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'successor KImpl rejects caller-supplied semantic readiness assertions',
  );
});

test('successor KImpl rejects attempts to weaken the release policy', async () => {
  const input = makeKImplSuccessor0({
    SemanticProofDAG: makeEqProof0(),
  });
  input.Policy.finalTheoremRequiresCompleteSemanticKernel = false;

  const out = await CheckKImplSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'successor KImpl semantic release policy must match the fail-closed policy',
  );
});

test('successor KImpl rejects an invalid semantic proof even in development mode', async () => {
  const out = await CheckKImplSuccessor0(makeKImplSuccessor0({
    SemanticProofDAG: makeEqProof0({ invalid: true }),
    Purpose: 'development',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplSuccessor0.semanticProof');
  assert.deepEqual(out.Path, ['SemanticKernel', 'ProofDAG']);
  assert.equal(
    out.Witness.inner.witness.reason,
    'Eq.refl conclusion must have identical left and right terms',
  );
});

test('successor KImpl still requires the legacy structural KImpl checks', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'Hall'),
  });

  const out = await CheckKImplSuccessor0(makeKImplSuccessor0({
    KImpl: badKImpl,
    SemanticProofDAG: makeEqProof0(),
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplSuccessor0.legacyKImpl');
  assert.deepEqual(out.Path, ['KImpl']);
  assert.equal(
    out.Witness.inner.witness.reason,
    'kernel rule table is missing a primitive rule',
  );
});

import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckSemanticKernelProof0,
  CheckSemanticKernelReadiness0,
  makeSemanticApp0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

const v = (name, sort = 'Bool') => makeSemanticVar0(name, sort);
const eq = (left, right) => makeSemanticEqJudgment0(left, right);
const n = (id, Conclusion, Payload, Premises = [], RuleName = 'Eq') => (
  makeSemanticProofNode0({ id, Conclusion, Payload, Premises, RuleName })
);

test('semantic Eq rules accept a closed reflexive chain', () => {
  const x = v('x');
  const dag = makeSemanticProofDAG0([
    n('r', eq(x, x), { op: 'refl' }),
    n('s', eq(x, x), { op: 'symm' }, ['r']),
    n('t', eq(x, x), { op: 'trans' }, ['r', 's']),
  ]);
  const out = CheckSemanticKernelProof0(dag);
  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.semanticRuleChecking, true);
  assert.deepEqual(out.NF.supportedRules, ['Eq']);
});

test('application congruence requires one matching equality per argument', () => {
  const x = v('x');
  const y = v('y');
  const app = makeSemanticApp0('nand', [x, y], 'Bool');
  const out = CheckSemanticKernelProof0(makeSemanticProofDAG0([
    n('rx', eq(x, x), { op: 'refl' }),
    n('ry', eq(y, y), { op: 'refl' }),
    n('c', eq(app, app), { op: 'cong' }, ['rx', 'ry']),
  ]));
  assert.equal(out.tag, 'accept');
});

test('an arbitrary equality cannot be labelled reflexivity', () => {
  const out = CheckSemanticKernelProof0(makeSemanticProofDAG0([
    n('bad', eq(v('x'), v('y')), { op: 'refl' }),
  ]));
  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'Eq.refl conclusion must have identical left and right terms');
});

test('transitivity rejects nonmatching middle terms', () => {
  const x = v('x');
  const y = v('y');
  const out = CheckSemanticKernelProof0(makeSemanticProofDAG0([
    n('rx', eq(x, x), { op: 'refl' }),
    n('ry', eq(y, y), { op: 'refl' }),
    n('bad', eq(x, y), { op: 'trans' }, ['rx', 'ry']),
  ]));
  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'Eq.trans premise middle terms must be identical');
});

test('unsupported primitive rules fail closed', () => {
  const x = v('x');
  const out = CheckSemanticKernelProof0(makeSemanticProofDAG0([
    n('unsupported', eq(x, x), { op: 'refl' }, [], 'Record'),
  ]));
  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'semantic kernel rejects unsupported rule');
});

test('readiness remains rejected while primitive-rule semantics are incomplete', () => {
  const out = CheckSemanticKernelReadiness0();
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadiness0.coverage');
  assert.equal(out.Witness.missingRules.includes('Subst'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

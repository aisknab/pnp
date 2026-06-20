import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  CheckSemanticKernelProof0,
  CheckSemanticKernelReadiness0,
  CheckSemanticSubstitution0,
  makeSemanticApp0,
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticFormulaJudgment0,
  makeSemanticForallFinite0,
  makeSemanticPred0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticSubstitution0,
  makeSemanticVar0,
  substituteSemanticFormula0,
} from '../pcc-kernel-semantic0.mjs';

const v = (name, sort = 'Bool') => makeSemanticVar0(name, sort);
const c = (name, sort = 'Bool') => makeSemanticConst0(name, sort);
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
  assert.deepEqual(out.NF.supportedRules, ['Eq', 'Subst']);
});

test('application congruence requires one matching equality per argument', () => {
  const x = v('x');
  const y = v('y');
  const app = makeSemanticApp0('nand', [x, y], 'Bool');
  const out = CheckSemanticKernelProof0(makeSemanticProofDAG0([
    n('rx', eq(x, x), { op: 'refl' }),
    n('ry', eq(y, y), { op: 'refl' }),
    n('cg', eq(app, app), { op: 'cong' }, ['rx', 'ry']),
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

test('Subst accepts a typed instantiation of an earlier equality proof', () => {
  const x = v('x');
  const zero = c('false');
  const fx = makeSemanticApp0('f', [x], 'Bool');
  const fzero = makeSemanticApp0('f', [zero], 'Bool');
  const out = CheckSemanticKernelProof0(makeSemanticProofDAG0([
    n('schema', eq(fx, fx), { op: 'refl' }),
    n(
      'instance',
      eq(fzero, fzero),
      { op: 'instantiate', variable: x, replacement: zero },
      ['schema'],
      'Subst',
    ),
  ]));
  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.nodeCount, 2);
  assert.deepEqual(out.NF.supportedSubstOperations, ['instantiate']);
});

test('Subst rejects a result that is not the exact instantiated judgment', () => {
  const x = v('x');
  const zero = c('false');
  const one = c('true');
  const fx = makeSemanticApp0('f', [x], 'Bool');
  const fzero = makeSemanticApp0('f', [zero], 'Bool');
  const fone = makeSemanticApp0('f', [one], 'Bool');
  const out = CheckSemanticKernelProof0(makeSemanticProofDAG0([
    n('schema', eq(fx, fx), { op: 'refl' }),
    n(
      'bad-instance',
      eq(fzero, fone),
      { op: 'instantiate', variable: x, replacement: zero },
      ['schema'],
      'Subst',
    ),
  ]));
  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'semantic substitution result does not equal capture-avoiding substitution',
  );
});

test('Subst rejects a replacement with the wrong sort', () => {
  const x = v('x', 'Bool');
  const natZero = c('zero', 'Nat');
  const out = CheckSemanticKernelProof0(makeSemanticProofDAG0([
    n('schema', eq(x, x), { op: 'refl' }),
    n(
      'bad-sort',
      eq(x, x),
      { op: 'instantiate', variable: x, replacement: natZero },
      ['schema'],
      'Subst',
    ),
  ]));
  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'semantic substitution replacement sort must match the variable sort',
  );
});

test('formula substitution alpha-renames a binder to avoid capture', () => {
  const x = v('x');
  const y = v('y');
  const falseTerm = c('false');
  const trueTerm = c('true');
  const sourceFormula = makeSemanticForallFinite0(
    y,
    [falseTerm, trueTerm],
    makeSemanticPred0('P', [x, y]),
  );
  const expectedBinder = v('y$0');
  const expectedFormula = makeSemanticForallFinite0(
    expectedBinder,
    [falseTerm, trueTerm],
    makeSemanticPred0('P', [y, expectedBinder]),
  );

  assert.deepEqual(
    substituteSemanticFormula0(sourceFormula, x, y),
    expectedFormula,
  );

  const out = CheckSemanticSubstitution0(makeSemanticSubstitution0({
    source: makeSemanticFormulaJudgment0(sourceFormula),
    variable: x,
    replacement: y,
    result: makeSemanticFormulaJudgment0(expectedFormula),
  }));
  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.captureAvoiding, true);
  assert.equal(out.NF.alphaRenameCount, 1);
  assert.deepEqual(out.NF.alphaRenamings[0], { from: y, to: expectedBinder });
});

test('substitution checker rejects a capture-producing result', () => {
  const x = v('x');
  const y = v('y');
  const falseTerm = c('false');
  const sourceFormula = makeSemanticForallFinite0(
    y,
    [falseTerm],
    makeSemanticPred0('P', [x, y]),
  );
  const capturedResult = makeSemanticForallFinite0(
    y,
    [falseTerm],
    makeSemanticPred0('P', [y, y]),
  );
  const out = CheckSemanticSubstitution0(makeSemanticSubstitution0({
    source: makeSemanticFormulaJudgment0(sourceFormula),
    variable: x,
    replacement: y,
    result: makeSemanticFormulaJudgment0(capturedResult),
  }));
  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'semantic substitution result does not equal capture-avoiding substitution',
  );
});

test('unsupported primitive rules still fail closed', () => {
  const x = v('x');
  const out = CheckSemanticKernelProof0(makeSemanticProofDAG0([
    n('unsupported', eq(x, x), { op: 'refl' }, [], 'Record'),
  ]));
  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'semantic kernel rejects unsupported rule');
});

test('readiness remains rejected but Subst is no longer missing', () => {
  const out = CheckSemanticKernelReadiness0();
  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadiness0.coverage');
  assert.equal(out.Witness.missingRules.includes('Subst'), false);
  assert.equal(out.Witness.missingRules.includes('Record'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofRecord0,
  CheckSemanticKernelReadinessRecord0,
  makeSemanticRecordField0,
  makeSemanticRecordJudgment0,
} from '../pcc-kernel-record-semantic0.mjs';

const variable = (name) => makeSemanticVar0(name, 'Bool');
const equality = (term) => makeSemanticEqJudgment0(term, term);

function reflNode0(id, term, Premises = []) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Premises,
    Conclusion: equality(term),
    Payload: { op: Premises.length === 0 ? 'refl' : 'symm' },
  });
}

function pairRecord0(leftJudgment, rightJudgment) {
  return makeSemanticRecordJudgment0('PairEvidence0', [
    makeSemanticRecordField0('left', leftJudgment),
    makeSemanticRecordField0('right', rightJudgment),
  ]);
}

test('Record.intro assembles canonical fields from accepted premises', () => {
  const x = variable('x');
  const y = variable('y');
  const left = equality(x);
  const right = equality(y);
  const record = pairRecord0(left, right);

  const out = CheckSemanticKernelProofRecord0(makeSemanticProofDAG0([
    reflNode0('eq.x', x),
    reflNode0('eq.y', y),
    makeSemanticProofNode0({
      id: 'record.pair',
      RuleName: 'Record',
      Premises: ['eq.x', 'eq.y'],
      Conclusion: record,
      Payload: {
        op: 'intro',
        recordType: 'PairEvidence0',
        fieldNames: ['left', 'right'],
      },
    }),
  ]));

  assert.equal(out.tag, 'accept');
  assert.deepEqual(out.NF.supportedRules, ['Eq', 'Subst', 'Record']);
  assert.equal(out.NF.recordNodeCount, 1);
  assert.equal(out.NF.missingRequiredRules.includes('Record'), false);
});

test('Record.project extracts exactly the selected field judgment', () => {
  const x = variable('x');
  const y = variable('y');
  const left = equality(x);
  const right = equality(y);
  const record = pairRecord0(left, right);

  const out = CheckSemanticKernelProofRecord0(makeSemanticProofDAG0([
    reflNode0('eq.x', x),
    reflNode0('eq.y', y),
    makeSemanticProofNode0({
      id: 'record.pair',
      RuleName: 'Record',
      Premises: ['eq.x', 'eq.y'],
      Conclusion: record,
      Payload: {
        op: 'intro',
        recordType: 'PairEvidence0',
        fieldNames: ['left', 'right'],
      },
    }),
    makeSemanticProofNode0({
      id: 'record.left',
      RuleName: 'Record',
      Premises: ['record.pair'],
      Conclusion: left,
      Payload: {
        op: 'project',
        recordType: 'PairEvidence0',
        fieldName: 'left',
      },
    }),
  ]));

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.recordNodeCount, 2);
});

test('Record.intro rejects a field not proved by its corresponding premise', () => {
  const x = variable('x');
  const y = variable('y');
  const record = pairRecord0(equality(y), equality(y));

  const out = CheckSemanticKernelProofRecord0(makeSemanticProofDAG0([
    reflNode0('eq.x', x),
    reflNode0('eq.y', y),
    makeSemanticProofNode0({
      id: 'record.bad',
      RuleName: 'Record',
      Premises: ['eq.x', 'eq.y'],
      Conclusion: record,
      Payload: {
        op: 'intro',
        recordType: 'PairEvidence0',
        fieldNames: ['left', 'right'],
      },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofRecord0.node.0002.semantic');
  assert.equal(
    out.Witness.reason,
    'Record.intro field judgment must exactly equal the corresponding premise conclusion',
  );
});

test('Record.intro rejects noncanonical field order', () => {
  const x = variable('x');
  const y = variable('y');
  const record = makeSemanticRecordJudgment0('PairEvidence0', [
    makeSemanticRecordField0('right', equality(y)),
    makeSemanticRecordField0('left', equality(x)),
  ]);

  const out = CheckSemanticKernelProofRecord0(makeSemanticProofDAG0([
    reflNode0('eq.x', x),
    reflNode0('eq.y', y),
    makeSemanticProofNode0({
      id: 'record.unsorted',
      RuleName: 'Record',
      Premises: ['eq.y', 'eq.x'],
      Conclusion: record,
      Payload: {
        op: 'intro',
        recordType: 'PairEvidence0',
        fieldNames: ['right', 'left'],
      },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofRecord0.shape');
  assert.equal(out.Witness.reason, 'semantic record fields must be in canonical name order');
});

test('Record.intro rejects duplicate field names', () => {
  const x = variable('x');
  const y = variable('y');
  const record = makeSemanticRecordJudgment0('DuplicateEvidence0', [
    makeSemanticRecordField0('same', equality(x)),
    makeSemanticRecordField0('same', equality(y)),
  ]);

  const out = CheckSemanticKernelProofRecord0(makeSemanticProofDAG0([
    reflNode0('eq.x', x),
    reflNode0('eq.y', y),
    makeSemanticProofNode0({
      id: 'record.duplicate',
      RuleName: 'Record',
      Premises: ['eq.x', 'eq.y'],
      Conclusion: record,
      Payload: {
        op: 'intro',
        recordType: 'DuplicateEvidence0',
        fieldNames: ['same', 'same'],
      },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'semantic record field names must be unique');
});

test('Record.project rejects a field absent from the premise record', () => {
  const x = variable('x');
  const record = makeSemanticRecordJudgment0('OneEvidence0', [
    makeSemanticRecordField0('only', equality(x)),
  ]);

  const out = CheckSemanticKernelProofRecord0(makeSemanticProofDAG0([
    reflNode0('eq.x', x),
    makeSemanticProofNode0({
      id: 'record.one',
      RuleName: 'Record',
      Premises: ['eq.x'],
      Conclusion: record,
      Payload: {
        op: 'intro',
        recordType: 'OneEvidence0',
        fieldNames: ['only'],
      },
    }),
    makeSemanticProofNode0({
      id: 'record.missing',
      RuleName: 'Record',
      Premises: ['record.one'],
      Conclusion: equality(x),
      Payload: {
        op: 'project',
        recordType: 'OneEvidence0',
        fieldName: 'missing',
      },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'Record.project field is not present in the premise record');
});

test('Eq/Subst cannot consume a Record premise without explicit semantics', () => {
  const x = variable('x');
  const record = makeSemanticRecordJudgment0('OneEvidence0', [
    makeSemanticRecordField0('only', equality(x)),
  ]);

  const out = CheckSemanticKernelProofRecord0(makeSemanticProofDAG0([
    reflNode0('eq.x', x),
    makeSemanticProofNode0({
      id: 'record.one',
      RuleName: 'Record',
      Premises: ['eq.x'],
      Conclusion: record,
      Payload: {
        op: 'intro',
        recordType: 'OneEvidence0',
        fieldNames: ['only'],
      },
    }),
    reflNode0('eq.illegal-record-premise', x, ['record.one']),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofRecord0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst sub-DAG rejected under the base semantic checker',
  );
});

test('Record readiness is recognized but the remaining rule families still block release', () => {
  const out = CheckSemanticKernelReadinessRecord0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessRecord0.coverage');
  assert.equal(out.Witness.missingRules.includes('Record'), false);
  assert.equal(out.Witness.missingRules.includes('DAGInd'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 13);
});

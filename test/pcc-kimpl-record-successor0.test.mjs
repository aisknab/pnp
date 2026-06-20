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
  makeSemanticRecordField0,
  makeSemanticRecordJudgment0,
} from '../pcc-kernel-record-semantic0.mjs';

import {
  CheckKImplRecordFinalTheoremReadiness0,
  CheckKImplRecordSuccessor0,
  makeKImplRecordSuccessor0,
} from '../pcc-kimpl-record-successor0.mjs';

function makeRecordProof0({ invalid = false } = {}) {
  const x = makeSemanticVar0('x', 'Bool');
  const y = makeSemanticVar0('y', 'Bool');
  const eqX = makeSemanticEqJudgment0(x, x);
  const eqY = makeSemanticEqJudgment0(y, y);
  const record = makeSemanticRecordJudgment0('PairEvidence0', [
    makeSemanticRecordField0('left', invalid ? eqY : eqX),
    makeSemanticRecordField0('right', eqY),
  ]);

  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'eq.x',
      RuleName: 'Eq',
      Conclusion: eqX,
      Payload: { op: 'refl' },
    }),
    makeSemanticProofNode0({
      id: 'eq.y',
      RuleName: 'Eq',
      Conclusion: eqY,
      Payload: { op: 'refl' },
    }),
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
  ]);
}

test('record-extended successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplRecordSuccessor0(makeKImplRecordSuccessor0({
    SemanticProofDAG: makeRecordProof0(),
    Purpose: 'development',
  }));

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplRecordSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.baseSuccessorAccepted, true);
  assert.equal(out.NF.baseSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.basePublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticRecordNodeCount, 1);
  assert.equal(out.NF.semanticKernelReady, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.equal(out.NF.supportedSemanticRules.includes('Record'), true);
  assert.equal(out.NF.missingSemanticRules.includes('Record'), false);
  assert.equal(out.NF.missingSemanticRules.includes('DAGInd'), true);
});

test('record-extended successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplRecordSuccessor0(makeKImplRecordSuccessor0({
    SemanticProofDAG: makeRecordProof0(),
    Purpose: 'final-theorem',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRecordSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'record-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('Record'), false);
  assert.equal(out.Witness.missingRules.length, 13);
});

test('record-extended final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplRecordFinalTheoremReadiness0(makeKImplRecordSuccessor0({
    SemanticProofDAG: makeRecordProof0(),
    Purpose: 'development',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRecordFinalTheoremReadiness0.purpose');
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'record-extended final-theorem readiness requires a final-theorem purpose record',
  );
});

test('record-extended final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplRecordFinalTheoremReadiness0(makeKImplRecordSuccessor0({
    SemanticProofDAG: makeRecordProof0(),
    Purpose: 'final-theorem',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRecordFinalTheoremReadiness0.semanticReadiness');
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('record-extended successor rejects fake readiness fields', async () => {
  const input = makeKImplRecordSuccessor0({
    SemanticProofDAG: makeRecordProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplRecordSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRecordSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'record-extended successor rejects caller-supplied semantic readiness assertions',
  );
});

test('record-extended successor rejects a weakened release policy', async () => {
  const input = makeKImplRecordSuccessor0({
    SemanticProofDAG: makeRecordProof0(),
  });
  input.Policy.finalTheoremRequiresCompleteSemanticKernel = false;

  const out = await CheckKImplRecordSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRecordSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'record-extended successor release policy must match the fail-closed policy',
  );
});

test('record-extended successor rejects an invalid Record derivation in development mode', async () => {
  const out = await CheckKImplRecordSuccessor0(makeKImplRecordSuccessor0({
    SemanticProofDAG: makeRecordProof0({ invalid: true }),
    Purpose: 'development',
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRecordSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'Record.intro field judgment must exactly equal the corresponding premise conclusion',
  );
});

test('record-extended successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter((rule) => rule.name !== 'Hall'),
  });

  const out = await CheckKImplRecordSuccessor0(makeKImplRecordSuccessor0({
    KImpl: badKImpl,
    SemanticProofDAG: makeRecordProof0(),
  }));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplRecordSuccessor0.baseSuccessor');
  assert.equal(
    out.Witness.inner.witness.inner.witness.reason,
    'kernel rule table is missing a primitive rule',
  );
});

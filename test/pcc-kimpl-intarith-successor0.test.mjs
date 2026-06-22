import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeKernelRuleTable0,
  makeSyntheticKImpl0,
} from '../pcc-kimpl0.mjs';

import {
  makeKImplMinCounterexampleSuccessor0,
} from '../pcc-kimpl-mincounterexample-successor0.mjs';

import {
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  deriveSemanticIntArithJudgment0,
  makeSemanticIntBinding0,
  makeSemanticIntClaim0,
  makeSemanticIntEnvironment0,
  makeSemanticIntLinearExpr0,
  makeSemanticIntLinearTerm0,
} from '../pcc-kernel-intarith-semantic0.mjs';

import {
  CheckKImplIntArithFinalTheoremReadiness0,
  CheckKImplIntArithSuccessor0,
  makeKImplIntArithSuccessor0,
} from '../pcc-kimpl-intarith-successor0.mjs';

function makeIntArithProof0({ invalid = false } = {}) {
  const left = makeSemanticIntLinearExpr0({
    constant: '1',
    terms: [
      makeSemanticIntLinearTerm0({ variable: 'x', coefficient: '2' }),
      makeSemanticIntLinearTerm0({ variable: 'y', coefficient: '1' }),
    ],
  });
  const right = makeSemanticIntLinearExpr0({ constant: '19' });
  const environment = makeSemanticIntEnvironment0({
    bindings: [
      makeSemanticIntBinding0({ variable: 'x', value: '10' }),
      makeSemanticIntBinding0({ variable: 'y', value: '-2' }),
    ],
  });
  const claim = makeSemanticIntClaim0({
    claimId: 'successor.arithmetic',
    relation: 'eq',
    left,
    right,
  });
  const validConclusion = deriveSemanticIntArithJudgment0({
    environment,
    claim,
  });
  const conclusion = invalid
    ? { ...validConclusion, leftValue: '20' }
    : validConclusion;

  return makeSemanticProofDAG0([
    makeSemanticProofNode0({
      id: 'arith.prove',
      RuleName: 'IntArith',
      Conclusion: conclusion,
      Payload: { op: 'prove', environment, claim },
    }),
  ]);
}

function collectReasons0(value, out = []) {
  if (value === null || typeof value !== 'object') return out;
  if (typeof value.reason === 'string') out.push(value.reason);
  for (const child of Object.values(value)) collectReasons0(child, out);
  return out;
}

test('IntArith successor accepts valid partial work only as development-only', async () => {
  const out = await CheckKImplIntArithSuccessor0(
    makeKImplIntArithSuccessor0({
      SemanticProofDAG: makeIntArithProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'accept');
  assert.equal(out.checker, 'CheckKImplIntArithSuccessor0');
  assert.equal(out.NF.status, 'development-only');
  assert.equal(out.NF.predecessorSuccessorAccepted, true);
  assert.equal(out.NF.predecessorSuccessorDevelopmentOnly, true);
  assert.equal(out.NF.predecessorPublicTheoremEmissionAllowed, false);
  assert.equal(out.NF.semanticProofAccepted, true);
  assert.equal(out.NF.semanticIntArithNodeCount, 1);
  assert.equal(out.NF.semanticKernelReady, false);
  assert.equal(out.NF.finalTheoremReady, false);
  assert.equal(out.NF.publicTheoremEmissionAllowed, false);
  assert.deepEqual(out.NF.supportedSemanticRules, [
    'Eq',
    'Subst',
    'Record',
    'DAGInd',
    'LedgerInd',
    'OblTopoInd',
    'TraceInd',
    'FiniteExhaust',
    'DPInd',
    'Hall',
    'RankInd',
    'MinCounterexample',
    'IntArith',
  ]);
  assert.equal(out.NF.missingSemanticRules.includes('IntArith'), false);
  assert.equal(out.NF.missingSemanticRules.includes('Transport'), true);
  assert.equal(out.NF.missingSemanticRules.length, 3);
});

test('IntArith successor rejects final-theorem purpose while coverage is incomplete', async () => {
  const out = await CheckKImplIntArithSuccessor0(
    makeKImplIntArithSuccessor0({
      SemanticProofDAG: makeIntArithProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplIntArithSuccessor0.semanticReadiness');
  assert.deepEqual(out.Path, ['SemanticKernel']);
  assert.equal(
    out.Witness.reason,
    'IntArith-extended successor KImpl is not ready for final-theorem use',
  );
  assert.equal(out.Witness.missingRules.includes('IntArith'), false);
  assert.equal(out.Witness.missingRules.length, 3);
});

test('IntArith final gate rejects a development-purpose record before reuse', async () => {
  const out = await CheckKImplIntArithFinalTheoremReadiness0(
    makeKImplIntArithSuccessor0({
      SemanticProofDAG: makeIntArithProof0(),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplIntArithFinalTheoremReadiness0.purpose',
  );
  assert.deepEqual(out.Path, ['Purpose']);
  assert.equal(
    out.Witness.reason,
    'IntArith final-theorem readiness requires a final-theorem purpose record',
  );
});

test('IntArith final gate rejects explicit final use until all handlers exist', async () => {
  const out = await CheckKImplIntArithFinalTheoremReadiness0(
    makeKImplIntArithSuccessor0({
      SemanticProofDAG: makeIntArithProof0(),
      Purpose: 'final-theorem',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Coord,
    'CheckKImplIntArithFinalTheoremReadiness0.semanticReadiness',
  );
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
});

test('IntArith successor rejects caller-supplied readiness fields', async () => {
  const input = makeKImplIntArithSuccessor0({
    SemanticProofDAG: makeIntArithProof0(),
  });
  input.SemanticKernel.semanticKernelReady = true;
  input.SemanticKernel.missingRules = [];

  const out = await CheckKImplIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplIntArithSuccessor0.input');
  assert.deepEqual(out.Path, ['SemanticKernel', 'semanticKernelReady']);
  assert.equal(
    out.Witness.reason,
    'IntArith successor rejects caller-supplied semantic readiness assertions',
  );
});

test('IntArith successor rejects a weakened release policy', async () => {
  const input = makeKImplIntArithSuccessor0({
    SemanticProofDAG: makeIntArithProof0(),
  });
  input.Policy.exactBigIntEvaluationRequired = false;

  const out = await CheckKImplIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplIntArithSuccessor0.input');
  assert.deepEqual(out.Path, ['Policy']);
  assert.equal(
    out.Witness.reason,
    'IntArith successor release policy must match the fail-closed policy',
  );
});

test('IntArith successor rejects a stale MinCounterexample-only successor record', async () => {
  const input = makeKImplIntArithSuccessor0({
    SemanticProofDAG: makeIntArithProof0(),
  });
  input.kind = makeKImplMinCounterexampleSuccessor0().kind;

  const out = await CheckKImplIntArithSuccessor0(input);

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplIntArithSuccessor0.input');
  assert.equal(
    out.Witness.reason,
    'IntArith successor KImpl kind must be KImplSemanticIntArithSuccessor0',
  );
});

test('IntArith successor rejects a mutated arithmetic conclusion in development mode', async () => {
  const out = await CheckKImplIntArithSuccessor0(
    makeKImplIntArithSuccessor0({
      SemanticProofDAG: makeIntArithProof0({ invalid: true }),
      Purpose: 'development',
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplIntArithSuccessor0.semanticProof');
  assert.equal(
    out.Witness.inner.witness.reason,
    'IntArith conclusion must exactly equal the computed bounded integer decision',
  );
});

test('IntArith successor retains the legacy KImpl structural gate', async () => {
  const badKImpl = makeSyntheticKImpl0({
    RuleTable: makeKernelRuleTable0().filter(
      (rule) => rule.name !== 'Transport',
    ),
  });

  const out = await CheckKImplIntArithSuccessor0(
    makeKImplIntArithSuccessor0({
      KImpl: badKImpl,
      SemanticProofDAG: makeIntArithProof0(),
    }),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckKImplIntArithSuccessor0.predecessorSuccessor');
  assert.equal(
    collectReasons0(out).includes('kernel rule table is missing a primitive rule'),
    true,
  );
});

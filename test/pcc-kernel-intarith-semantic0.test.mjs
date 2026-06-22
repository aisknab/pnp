import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofIntArith0,
  CheckSemanticKernelReadinessIntArith0,
  deriveSemanticIntArithJudgment0,
  makeSemanticIntBinding0,
  makeSemanticIntClaim0,
  makeSemanticIntEnvironment0,
  makeSemanticIntLinearExpr0,
  makeSemanticIntLinearTerm0,
} from '../pcc-kernel-intarith-semantic0.mjs';

const BIG_X = '90071992547409931234567890';
const EXPECTED = '270215977642229793703703689';

function makeFixture0() {
  const xTerm = makeSemanticIntLinearTerm0({
    variable: 'x',
    coefficient: '3',
  });
  const yTerm = makeSemanticIntLinearTerm0({
    variable: 'y',
    coefficient: '-2',
  });
  const left = makeSemanticIntLinearExpr0({
    constant: '5',
    terms: [yTerm, xTerm],
  });
  const right = makeSemanticIntLinearExpr0({
    constant: EXPECTED,
  });
  const environment = makeSemanticIntEnvironment0({
    bindings: [
      makeSemanticIntBinding0({ variable: 'y', value: '-7' }),
      makeSemanticIntBinding0({ variable: 'x', value: BIG_X }),
    ],
  });
  const claim = makeSemanticIntClaim0({
    claimId: 'arith.big.identity',
    relation: 'eq',
    left,
    right,
  });
  const conclusion = deriveSemanticIntArithJudgment0({
    environment,
    claim,
  });
  const node = makeSemanticProofNode0({
    id: 'arith.prove',
    RuleName: 'IntArith',
    Conclusion: conclusion,
    Payload: { op: 'prove', environment, claim },
  });

  return {
    xTerm,
    yTerm,
    left,
    right,
    environment,
    claim,
    conclusion,
    node,
  };
}

function runNode0(node, prefix = []) {
  return CheckSemanticKernelProofIntArith0(
    makeSemanticProofDAG0([...prefix, node]),
  );
}

test('IntArith proves exact affine arithmetic beyond Number safe-integer range', () => {
  const fixture = makeFixture0();
  const out = runNode0(fixture.node);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.intArithNodeCount, 1);
  assert.deepEqual(out.NF.supportedRules, [
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
  assert.equal(fixture.conclusion.leftValue, EXPECTED);
  assert.equal(fixture.conclusion.rightValue, EXPECTED);
  assert.equal(fixture.conclusion.difference, '0');
  assert.equal(fixture.conclusion.comparison, 0);
  assert.equal(fixture.conclusion.exactBigIntEvaluation, true);
  assert.equal(fixture.conclusion.relationVerified, true);
  assert.equal(
    fixture.conclusion.noSolverSearchOptimizationOrOracleUsed,
    true,
  );
  assert.deepEqual(fixture.conclusion.variables, ['x', 'y']);
  assert.deepEqual(
    fixture.conclusion.normalizedDifference.terms.map(
      (term) => [term.variable, term.coefficient],
    ),
    [['x', '3'], ['y', '-2']],
  );
});

test('IntArith accepts a closed constant inequality with an empty environment', () => {
  const left = makeSemanticIntLinearExpr0({ constant: '-12' });
  const right = makeSemanticIntLinearExpr0({ constant: '4' });
  const environment = makeSemanticIntEnvironment0();
  const claim = makeSemanticIntClaim0({
    claimId: 'arith.constant.lt',
    relation: 'lt',
    left,
    right,
  });
  const conclusion = deriveSemanticIntArithJudgment0({ environment, claim });
  const node = makeSemanticProofNode0({
    id: 'arith.constant',
    RuleName: 'IntArith',
    Conclusion: conclusion,
    Payload: { op: 'prove', environment, claim },
  });

  const out = runNode0(node);
  assert.equal(out.tag, 'accept');
  assert.equal(conclusion.comparison, -1);
  assert.deepEqual(conclusion.variables, []);
});

test('IntArith rejects noncanonical signed decimal encoding', () => {
  const fixture = makeFixture0();
  const environment = {
    ...fixture.environment,
    bindings: fixture.environment.bindings.map((binding) => (
      binding.variable === 'x' ? { ...binding, value: '01' } : binding
    )),
  };
  const out = runNode0({
    ...fixture.node,
    Payload: { ...fixture.node.Payload, environment },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofIntArith0.shape');
  assert.equal(
    out.Witness.reason,
    'IntArith integers must use canonical signed decimal strings',
  );
});

test('IntArith rejects a zero affine coefficient', () => {
  const fixture = makeFixture0();
  const left = {
    ...fixture.left,
    terms: fixture.left.terms.map((term) => (
      term.variable === 'x' ? { ...term, coefficient: '0' } : term
    )),
  };
  const claim = { ...fixture.claim, left };
  const out = runNode0({
    ...fixture.node,
    Payload: { ...fixture.node.Payload, claim },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'IntArith linear coefficients must be nonzero',
  );
});

test('IntArith rejects noncanonical or duplicate variable order', () => {
  const fixture = makeFixture0();
  const left = {
    ...fixture.left,
    terms: [...fixture.left.terms].reverse(),
  };
  const claim = { ...fixture.claim, left };
  const out = runNode0({
    ...fixture.node,
    Payload: { ...fixture.node.Payload, claim },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'IntArith linear terms must be strictly ordered by unique variable id',
  );
});

test('IntArith rejects a missing environment binding', () => {
  const fixture = makeFixture0();
  const environment = {
    ...fixture.environment,
    bindings: fixture.environment.bindings.filter(
      (binding) => binding.variable !== 'y',
    ),
  };
  const out = runNode0({
    ...fixture.node,
    Payload: { ...fixture.node.Payload, environment },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'IntArith environment must bind exactly the variables used by the claim',
  );
  assert.deepEqual(out.Witness.missingVariables, ['y']);
});

test('IntArith rejects an unused extra environment binding', () => {
  const fixture = makeFixture0();
  const environment = {
    ...fixture.environment,
    bindings: [
      ...fixture.environment.bindings,
      makeSemanticIntBinding0({ variable: 'z', value: '9' }),
    ],
  };
  const out = runNode0({
    ...fixture.node,
    Payload: { ...fixture.node.Payload, environment },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'IntArith environment must bind exactly the variables used by the claim',
  );
  assert.deepEqual(out.Witness.extraVariables, ['z']);
});

test('IntArith rejects a ground claim that evaluates to false', () => {
  const fixture = makeFixture0();
  const claim = { ...fixture.claim, relation: 'gt' };
  const out = runNode0({
    ...fixture.node,
    Payload: { ...fixture.node.Payload, claim },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'IntArith claim evaluates to false');
  assert.equal(out.Witness.leftValue, EXPECTED);
  assert.equal(out.Witness.rightValue, EXPECTED);
});

test('IntArith rejects an unsupported relation', () => {
  const fixture = makeFixture0();
  const claim = { ...fixture.claim, relation: 'divides' };
  const out = runNode0({
    ...fixture.node,
    Payload: { ...fixture.node.Payload, claim },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofIntArith0.shape');
  assert.equal(out.Witness.reason, 'IntArith relation is unsupported');
});

test('IntArith rejects caller-supplied truth or solver assertions', () => {
  const fixture = makeFixture0();
  const out = runNode0({
    ...fixture.node,
    Payload: {
      ...fixture.node.Payload,
      holds: true,
      solver: 'trusted',
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofIntArith0.shape');
  assert.equal(
    out.Witness.reason,
    'IntArith payload rejects caller-supplied truth, certificate, result, optimization, minimization, solver, search, or oracle assertions',
  );
});

test('IntArith prove rejects every premise because evaluation is closed', () => {
  const fixture = makeFixture0();
  const term = makeSemanticConst0('premise.term', 'Term');
  const equality = makeSemanticEqJudgment0(term, term);
  const premise = makeSemanticProofNode0({
    id: 'eq.premise',
    RuleName: 'Eq',
    Conclusion: equality,
    Payload: { op: 'refl' },
  });
  const out = runNode0({
    ...fixture.node,
    Premises: ['eq.premise'],
  }, [premise]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'IntArith prove is a closed exact evaluation and must not consume premises',
  );
});

test('IntArith rejects a mutated computed conclusion', () => {
  const fixture = makeFixture0();
  const out = runNode0({
    ...fixture.node,
    Conclusion: {
      ...fixture.conclusion,
      rightValue: '0',
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'IntArith conclusion must exactly equal the computed bounded integer decision',
  );
});

test('IntArith rejects decimal inputs beyond the explicit digit bound', () => {
  const fixture = makeFixture0();
  const environment = {
    ...fixture.environment,
    bindings: fixture.environment.bindings.map((binding) => (
      binding.variable === 'x'
        ? { ...binding, value: `1${'0'.repeat(2048)}` }
        : binding
    )),
  };
  const out = runNode0({
    ...fixture.node,
    Payload: { ...fixture.node.Payload, environment },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'IntArith integer exceeds the decimal digit bound',
  );
});

test('predecessor rules cannot consume IntArith conclusions without explicit semantics', () => {
  const fixture = makeFixture0();
  const term = makeSemanticConst0('after.term', 'Term');
  const illegal = makeSemanticProofNode0({
    id: 'eq.after.arith',
    RuleName: 'Eq',
    Premises: ['arith.prove'],
    Conclusion: makeSemanticEqJudgment0(term, term),
    Payload: { op: 'symm' },
  });
  const out = CheckSemanticKernelProofIntArith0(
    makeSemanticProofDAG0([fixture.node, illegal]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofIntArith0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall/RankInd/MinCounterexample sub-DAG rejected under the predecessor semantic checker',
  );
});

test('IntArith readiness removes IntArith but leaves three primitive families missing', () => {
  const out = CheckSemanticKernelReadinessIntArith0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessIntArith0.coverage');
  assert.equal(out.Witness.missingRules.includes('IntArith'), false);
  assert.equal(out.Witness.missingRules.includes('Transport'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 3);
});

import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofFiniteRel0,
  CheckSemanticKernelReadinessFiniteRel0,
  deriveSemanticFiniteRelJudgment0,
  makeSemanticFiniteRelClaim0,
  makeSemanticFiniteRelDomain0,
  makeSemanticFiniteRelNode0,
  makeSemanticFiniteRelProgram0,
  makeSemanticFiniteRelRestriction0,
  makeSemanticFiniteRelSpec0,
  makeSemanticFiniteRelTuple0,
} from '../pcc-kernel-finiterel-semantic0.mjs';

function tuple0(index, values) {
  return makeSemanticFiniteRelTuple0({ index, values });
}

function literal0(index, id, domainIds, tupleValues) {
  return makeSemanticFiniteRelNode0({
    index,
    id,
    op: 'literal',
    domainIds,
    tuples: tupleValues.map((values, tupleIndex) => tuple0(tupleIndex, values)),
  });
}

function node0(index, id, op, domainIds, inputIds, extra = {}) {
  return makeSemanticFiniteRelNode0({
    index,
    id,
    op,
    domainIds,
    inputIds,
    ...extra,
  });
}

function claim0(index, id, claimKind, leftId, rightId = null) {
  return makeSemanticFiniteRelClaim0({
    index,
    id,
    claimKind,
    leftId,
    rightId,
  });
}

function makeFixture0() {
  const domain = makeSemanticFiniteRelDomain0({
    index: 0,
    id: 'D',
    elements: ['a', 'b', 'c'],
  });
  const nodes = [
    literal0(0, 'R', ['D', 'D'], [['a', 'b'], ['b', 'c']]),
    literal0(1, 'S', ['D', 'D'], [['b', 'c'], ['c', 'a']]),
    node0(2, 'R.compose.S', 'compose', ['D', 'D'], ['R', 'S']),
    node0(3, 'R.converse', 'converse', ['D', 'D'], ['R']),
    node0(4, 'R.tc', 'transitive-closure', ['D', 'D'], ['R']),
    node0(5, 'R.rtc', 'reflexive-transitive-closure', ['D', 'D'], ['R']),
    literal0(6, 'Expected.compose', ['D', 'D'], [['a', 'c'], ['b', 'a']]),
    literal0(7, 'Expected.converse', ['D', 'D'], [['b', 'a'], ['c', 'b']]),
    literal0(8, 'Expected.tc', ['D', 'D'], [['a', 'b'], ['a', 'c'], ['b', 'c']]),
  ];
  const claims = [
    claim0(0, 'claim.compose.equal', 'equal', 'R.compose.S', 'Expected.compose'),
    claim0(1, 'claim.converse.equal', 'equal', 'R.converse', 'Expected.converse'),
    claim0(2, 'claim.tc.equal', 'equal', 'R.tc', 'Expected.tc'),
    claim0(3, 'claim.R.in.tc', 'included', 'R', 'R.tc'),
    claim0(4, 'claim.tc.transitive', 'transitive', 'R.tc'),
    claim0(5, 'claim.rtc.closed', 'reflexive-transitive-closed', 'R.rtc'),
  ];
  const program = makeSemanticFiniteRelProgram0({
    programId: 'finiterel.program.main',
    domains: [domain],
    nodes,
    claims,
  });
  const spec = makeSemanticFiniteRelSpec0({
    evaluationId: 'finiterel.eval.main',
    program,
  });
  const conclusion = deriveSemanticFiniteRelJudgment0({ spec });
  const proofNode = makeSemanticProofNode0({
    id: 'finiterel.verify',
    RuleName: 'FiniteRel',
    Conclusion: conclusion,
    Payload: { op: 'verify', spec },
  });
  return { domain, nodes, claims, program, spec, conclusion, proofNode };
}

function run0(node, prefix = []) {
  return CheckSemanticKernelProofFiniteRel0(
    makeSemanticProofDAG0([...prefix, node]),
  );
}

function valuesOf0(relation) {
  return relation.tuples.map((tuple) => tuple.values);
}

test('FiniteRel computes explicit relation operations and checked claims', () => {
  const fixture = makeFixture0();
  const out = run0(fixture.proofNode);

  assert.equal(out.tag, 'accept');
  assert.equal(out.NF.finiteRelNodeCount, 1);
  assert.equal(out.NF.semanticRuleCoverageComplete, true);
  assert.deepEqual(out.NF.missingRequiredRules, []);
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
    'Transport',
    'TruthVec',
    'FiniteRel',
  ]);

  const byNode = new Map(
    fixture.conclusion.relations.map((relation) => [relation.nodeId, relation]),
  );
  assert.deepEqual(valuesOf0(byNode.get('R.compose.S')), [['a', 'c'], ['b', 'a']]);
  assert.deepEqual(valuesOf0(byNode.get('R.converse')), [['b', 'a'], ['c', 'b']]);
  assert.deepEqual(valuesOf0(byNode.get('R.tc')), [['a', 'b'], ['a', 'c'], ['b', 'c']]);
  assert.deepEqual(valuesOf0(byNode.get('R.rtc')), [
    ['a', 'a'],
    ['a', 'b'],
    ['a', 'c'],
    ['b', 'b'],
    ['b', 'c'],
    ['c', 'c'],
  ]);
  assert.equal(fixture.conclusion.claims.every((claim) => claim.holds), true);
  assert.equal(fixture.conclusion.allClaimsHold, true);
});

test('FiniteRel computes restriction, union, intersection, and difference', () => {
  const domain = makeSemanticFiniteRelDomain0({
    index: 0,
    id: 'D',
    elements: ['a', 'b', 'c'],
  });
  const nodes = [
    literal0(0, 'A', ['D', 'D'], [['a', 'b'], ['b', 'b'], ['c', 'a']]),
    literal0(1, 'B', ['D', 'D'], [['a', 'b'], ['b', 'c']]),
    node0(2, 'A.restricted', 'restrict', ['D', 'D'], ['A'], {
      restrictions: [
        makeSemanticFiniteRelRestriction0({
          index: 0,
          domainId: 'D',
          allowedElements: ['a', 'b'],
        }),
        makeSemanticFiniteRelRestriction0({
          index: 1,
          domainId: 'D',
          allowedElements: ['a', 'b'],
        }),
      ],
    }),
    node0(3, 'A.union.B', 'union', ['D', 'D'], ['A', 'B']),
    node0(4, 'A.intersection.B', 'intersection', ['D', 'D'], ['A', 'B']),
    node0(5, 'A.difference.B', 'difference', ['D', 'D'], ['A', 'B']),
    literal0(6, 'Expected.restricted', ['D', 'D'], [['a', 'b'], ['b', 'b']]),
    literal0(7, 'Expected.union', ['D', 'D'], [
      ['a', 'b'],
      ['b', 'b'],
      ['b', 'c'],
      ['c', 'a'],
    ]),
    literal0(8, 'Expected.intersection', ['D', 'D'], [['a', 'b']]),
    literal0(9, 'Expected.difference', ['D', 'D'], [['b', 'b'], ['c', 'a']]),
  ];
  const program = makeSemanticFiniteRelProgram0({
    programId: 'finiterel.program.setops',
    domains: [domain],
    nodes,
    claims: [
      claim0(0, 'claim.restricted', 'equal', 'A.restricted', 'Expected.restricted'),
      claim0(1, 'claim.union', 'equal', 'A.union.B', 'Expected.union'),
      claim0(2, 'claim.intersection', 'equal', 'A.intersection.B', 'Expected.intersection'),
      claim0(3, 'claim.difference', 'equal', 'A.difference.B', 'Expected.difference'),
    ],
  });
  const spec = makeSemanticFiniteRelSpec0({
    evaluationId: 'finiterel.eval.setops',
    program,
  });
  const conclusion = deriveSemanticFiniteRelJudgment0({ spec });
  const out = run0(makeSemanticProofNode0({
    id: 'finiterel.setops',
    RuleName: 'FiniteRel',
    Conclusion: conclusion,
    Payload: { op: 'verify', spec },
  }));

  assert.equal(out.tag, 'accept');
  const byNode = new Map(conclusion.relations.map((relation) => [relation.nodeId, relation]));
  assert.deepEqual(valuesOf0(byNode.get('A.restricted')), [['a', 'b'], ['b', 'b']]);
  assert.deepEqual(valuesOf0(byNode.get('A.union.B')), [
    ['a', 'b'],
    ['b', 'b'],
    ['b', 'c'],
    ['c', 'a'],
  ]);
});

test('FiniteRel rejects noncanonical literal tuple order', () => {
  const fixture = makeFixture0();
  const badProgram = {
    ...fixture.program,
    nodes: [
      {
        ...fixture.nodes[0],
        tuples: [
          tuple0(0, ['b', 'c']),
          tuple0(1, ['a', 'b']),
        ],
      },
      ...fixture.nodes.slice(1),
    ],
  };
  const out = run0({
    ...fixture.proofNode,
    Payload: { op: 'verify', spec: { ...fixture.spec, program: badProgram } },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofFiniteRel0.shape');
  assert.equal(
    out.Witness.reason,
    'FiniteRel literal tuples must be unique and in canonical domain order',
  );
});

test('FiniteRel rejects a composition with mismatched middle domains', () => {
  const fixture = makeFixture0();
  const otherDomain = makeSemanticFiniteRelDomain0({
    index: 1,
    id: 'E',
    elements: ['u', 'v'],
  });
  const badRight = literal0(1, 'BadS', ['E', 'D'], [['u', 'a']]);
  const badProgram = {
    ...fixture.program,
    domains: [fixture.domain, otherDomain],
    nodes: [
      fixture.nodes[0],
      badRight,
      node0(2, 'bad.compose', 'compose', ['D', 'D'], ['R', 'BadS']),
    ],
    claims: [claim0(0, 'claim.bad', 'included', 'R', 'bad.compose')],
  };
  const out = run0({
    ...fixture.proofNode,
    Payload: { op: 'verify', spec: { ...fixture.spec, program: badProgram } },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteRel composition middle domains must match exactly',
  );
});

test('FiniteRel rejects caller-supplied result tuples for computed nodes', () => {
  const fixture = makeFixture0();
  const badProgram = {
    ...fixture.program,
    nodes: fixture.nodes.map((node) => (
      node.id === 'R.tc'
        ? { ...node, tuples: [tuple0(0, ['a', 'b'])] }
        : node
    )),
  };
  const out = run0({
    ...fixture.proofNode,
    Payload: { op: 'verify', spec: { ...fixture.spec, program: badProgram } },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteRel computed relation nodes cannot contain caller-supplied result tuples',
  );
});

test('FiniteRel rejects false equality and inclusion claims by independent computation', () => {
  const domain = makeSemanticFiniteRelDomain0({
    index: 0,
    id: 'D',
    elements: ['a', 'b'],
  });
  const program = makeSemanticFiniteRelProgram0({
    programId: 'finiterel.program.false.claim',
    domains: [domain],
    nodes: [
      literal0(0, 'A', ['D', 'D'], [['a', 'a']]),
      literal0(1, 'B', ['D', 'D'], [['b', 'b']]),
    ],
    claims: [claim0(0, 'claim.false.equal', 'equal', 'A', 'B')],
  });
  const spec = makeSemanticFiniteRelSpec0({
    evaluationId: 'finiterel.eval.false.claim',
    program,
  });
  const fixture = makeFixture0();
  const out = run0({
    ...fixture.proofNode,
    Payload: { op: 'verify', spec },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofFiniteRel0.node.0000.semantic');
  assert.equal(out.Witness.reason, 'FiniteRel checked claim does not hold');
});

test('FiniteRel rejects caller-supplied equality or completion assertions', () => {
  const fixture = makeFixture0();
  const out = run0({
    ...fixture.proofNode,
    Payload: {
      op: 'verify',
      spec: fixture.spec,
      equal: true,
      complete: true,
    },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofFiniteRel0.shape');
  assert.equal(
    out.Witness.reason,
    'FiniteRel payload rejects caller-supplied relations, equality, inclusion, closure, completeness, normalization, result, solver, search, optimization, or oracle assertions',
  );
});

test('FiniteRel rejects a mutated computed relation conclusion', () => {
  const fixture = makeFixture0();
  const mutatedRelations = fixture.conclusion.relations.map((relation) => (
    relation.nodeId === 'R.compose.S'
      ? { ...relation, tuples: relation.tuples.slice(0, 1) }
      : relation
  ));
  const out = run0({
    ...fixture.proofNode,
    Conclusion: { ...fixture.conclusion, relations: mutatedRelations },
  });

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteRel conclusion must exactly equal the computed relation and claim ledger',
  );
});

test('FiniteRel verify rejects every proof premise because computation is closed', () => {
  const fixture = makeFixture0();
  const term = makeSemanticConst0('finiterel.premise', 'Term');
  const premise = makeSemanticProofNode0({
    id: 'eq.finiterel.premise',
    RuleName: 'Eq',
    Conclusion: makeSemanticEqJudgment0(term, term),
    Payload: { op: 'refl' },
  });
  const out = run0({
    ...fixture.proofNode,
    Premises: ['eq.finiterel.premise'],
  }, [premise]);

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'FiniteRel verify is a closed exact finite computation and must not consume premises',
  );
});

test('predecessor rules cannot consume FiniteRel conclusions without explicit semantics', () => {
  const fixture = makeFixture0();
  const term = makeSemanticConst0('after.finiterel', 'Term');
  const illegal = makeSemanticProofNode0({
    id: 'eq.after.finiterel',
    RuleName: 'Eq',
    Premises: ['finiterel.verify'],
    Conclusion: makeSemanticEqJudgment0(term, term),
    Payload: { op: 'symm' },
  });
  const out = CheckSemanticKernelProofFiniteRel0(
    makeSemanticProofDAG0([fixture.proofNode, illegal]),
  );

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofFiniteRel0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd/Hall/RankInd/MinCounterexample/IntArith/Transport/TruthVec sub-DAG rejected under the predecessor semantic checker',
  );
});

test('FiniteRel readiness completes the primitive semantic rule set', () => {
  const out = CheckSemanticKernelReadinessFiniteRel0();

  assert.equal(out.tag, 'accept');
  assert.deepEqual(out.NF.missingRules, []);
  assert.equal(out.NF.semanticRuleCoverageComplete, true);
  assert.equal(out.NF.supportedRules.includes('FiniteRel'), true);
});

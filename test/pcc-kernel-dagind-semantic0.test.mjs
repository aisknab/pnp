import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

import {
  makeSemanticProofNode0 as makeNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofDAGInd0,
  CheckSemanticKernelReadinessDAGInd0,
  deriveSemanticDAGIndJudgment0,
  makeSemanticDAGIndCase0,
  makeSemanticInductionDAG0,
  makeSemanticInductionDAGNode0,
} from '../pcc-kernel-dagind-semantic0.mjs';

function invariant0(name) {
  const term = makeSemanticVar0(name, 'Bool');
  return makeSemanticEqJudgment0(term, term);
}

function eqProof0(id, judgment) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Conclusion: judgment,
    Payload: { op: 'refl' },
  });
}

function recordCaseNode0({
  id,
  graphId,
  nodeId,
  current,
  predecessorEntries = [],
  premiseIds,
}) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Record',
    Premises: premiseIds,
    Conclusion: makeSemanticDAGIndCase0({
      graphId,
      nodeId,
      current,
      predecessorInvariants: predecessorEntries,
    }),
    Payload: {
      op: 'intro',
      recordType: `DAGIndCase0.${graphId}.${nodeId}`,
      fieldNames: [
        'current',
        ...predecessorEntries.map((entry) => `pred.${entry.nodeId}`),
      ].sort(),
    },
  });
}

function makeValidClosure0() {
  const graphId = 'proof.graph';
  const graph = makeSemanticInductionDAG0(graphId, [
    makeSemanticInductionDAGNode0('a'),
    makeSemanticInductionDAGNode0('b'),
    makeSemanticInductionDAGNode0('c', ['a', 'b']),
    makeSemanticInductionDAGNode0('d', ['c']),
  ]);

  const invA = invariant0('a');
  const invB = invariant0('b');
  const invC = invariant0('c');
  const invD = invariant0('d');

  const caseA = makeSemanticDAGIndCase0({
    graphId,
    nodeId: 'a',
    current: invA,
  });
  const caseB = makeSemanticDAGIndCase0({
    graphId,
    nodeId: 'b',
    current: invB,
  });
  const caseC = makeSemanticDAGIndCase0({
    graphId,
    nodeId: 'c',
    current: invC,
    predecessorInvariants: [
      { nodeId: 'a', invariant: invA },
      { nodeId: 'b', invariant: invB },
    ],
  });
  const caseD = makeSemanticDAGIndCase0({
    graphId,
    nodeId: 'd',
    current: invD,
    predecessorInvariants: [
      { nodeId: 'c', invariant: invC },
    ],
  });

  const caseProofIds = ['case.a', 'case.b', 'case.c', 'case.d'];
  const conclusion = deriveSemanticDAGIndJudgment0({
    graph,
    caseRecords: [caseA, caseB, caseC, caseD],
    caseProofIds,
  });

  const nodes = [
    eqProof0('inv.a', invA),
    eqProof0('inv.b', invB),
    eqProof0('inv.c', invC),
    eqProof0('inv.d', invD),
    recordCaseNode0({
      id: 'case.a',
      graphId,
      nodeId: 'a',
      current: invA,
      premiseIds: ['inv.a'],
    }),
    recordCaseNode0({
      id: 'case.b',
      graphId,
      nodeId: 'b',
      current: invB,
      premiseIds: ['inv.b'],
    }),
    recordCaseNode0({
      id: 'case.c',
      graphId,
      nodeId: 'c',
      current: invC,
      predecessorEntries: [
        { nodeId: 'a', invariant: invA },
        { nodeId: 'b', invariant: invB },
      ],
      premiseIds: ['inv.c', 'inv.a', 'inv.b'],
    }),
    recordCaseNode0({
      id: 'case.d',
      graphId,
      nodeId: 'd',
      current: invD,
      predecessorEntries: [
        { nodeId: 'c', invariant: invC },
      ],
      premiseIds: ['inv.d', 'inv.c'],
    }),
    makeSemanticProofNode0({
      id: 'dag.close',
      RuleName: 'DAGInd',
      Premises: caseProofIds,
      Conclusion: conclusion,
      Payload: { op: 'close', graph },
    }),
  ];

  return {
    graphId,
    graph,
    conclusion,
    caseProofIds,
    cases: { caseA, caseB, caseC, caseD },
    invariants: { invA, invB, invC, invD },
    nodes,
  };
}

test('DAGInd closes every node from predecessor-complete accepted case records', () => {
  const fixture = makeValidClosure0();
  const out = CheckSemanticKernelProofDAGInd0(makeSemanticProofDAG0(fixture.nodes));

  assert.equal(out.tag, 'accept');
  assert.deepEqual(out.NF.supportedRules, ['Eq', 'Subst', 'Record', 'DAGInd']);
  assert.equal(out.NF.dagIndNodeCount, 1);
  assert.equal(out.NF.missingRequiredRules.includes('DAGInd'), false);
  assert.deepEqual(fixture.conclusion.sourceNodeIds, ['a', 'b']);
  assert.deepEqual(fixture.conclusion.sinkNodeIds, ['d']);
  assert.equal(fixture.conclusion.allNodesClosed, true);
});

test('DAGInd rejects a predecessor invariant that differs from the earlier closed node', () => {
  const fixture = makeValidClosure0();
  const badCase = recordCaseNode0({
    id: 'case.c',
    graphId: fixture.graphId,
    nodeId: 'c',
    current: fixture.invariants.invC,
    predecessorEntries: [
      { nodeId: 'a', invariant: fixture.invariants.invB },
      { nodeId: 'b', invariant: fixture.invariants.invB },
    ],
    premiseIds: ['inv.c', 'inv.b', 'inv.b'],
  });
  const nodes = fixture.nodes.map((node) => node.id === 'case.c' ? badCase : node);

  const out = CheckSemanticKernelProofDAGInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofDAGInd0.node.0008.semantic');
  assert.equal(
    out.Witness.reason,
    'DAGInd predecessor invariant must exactly match the earlier node invariant',
  );
});

test('DAGInd rejects a case missing one graph predecessor', () => {
  const fixture = makeValidClosure0();
  const shortCase = recordCaseNode0({
    id: 'case.c',
    graphId: fixture.graphId,
    nodeId: 'c',
    current: fixture.invariants.invC,
    predecessorEntries: [
      { nodeId: 'a', invariant: fixture.invariants.invA },
    ],
    premiseIds: ['inv.c', 'inv.a'],
  });
  const nodes = fixture.nodes.map((node) => node.id === 'case.c' ? shortCase : node);

  const out = CheckSemanticKernelProofDAGInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DAGInd case fields must contain current and every predecessor invariant exactly once',
  );
});

test('DAGInd rejects case proofs supplied in a different graph-node order', () => {
  const fixture = makeValidClosure0();
  const dagNode = fixture.nodes.at(-1);
  const swapped = {
    ...dagNode,
    Premises: ['case.b', 'case.a', 'case.c', 'case.d'],
  };
  const nodes = [...fixture.nodes.slice(0, -1), swapped];

  const out = CheckSemanticKernelProofDAGInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DAGInd case recordType must bind the graph and node id',
  );
});

test('DAGInd rejects a forward graph predecessor', () => {
  const fixture = makeValidClosure0();
  const badGraph = {
    ...fixture.graph,
    nodes: [
      makeSemanticInductionDAGNode0('a', ['b']),
      makeSemanticInductionDAGNode0('b'),
    ],
  };
  const dagNode = fixture.nodes.at(-1);
  const nodes = [
    ...fixture.nodes.slice(0, -1),
    { ...dagNode, Payload: { op: 'close', graph: badGraph } },
  ];

  const out = CheckSemanticKernelProofDAGInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofDAGInd0.shape');
  assert.equal(
    out.Witness.reason,
    'DAGInd predecessor must reference an earlier graph node',
  );
});

test('DAGInd rejects noncanonical graph-node ordering', () => {
  const fixture = makeValidClosure0();
  const badGraph = {
    ...fixture.graph,
    nodes: [
      makeSemanticInductionDAGNode0('b'),
      makeSemanticInductionDAGNode0('a'),
    ],
  };
  const dagNode = fixture.nodes.at(-1);
  const nodes = [
    ...fixture.nodes.slice(0, -1),
    { ...dagNode, Payload: { op: 'close', graph: badGraph } },
  ];

  const out = CheckSemanticKernelProofDAGInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DAGInd graph nodes must use canonical increasing topological order',
  );
});

test('DAGInd rejects a mutated all-node conclusion', () => {
  const fixture = makeValidClosure0();
  const dagNode = fixture.nodes.at(-1);
  const mutatedConclusion = {
    ...fixture.conclusion,
    sinkNodeIds: ['c'],
  };
  const nodes = [
    ...fixture.nodes.slice(0, -1),
    { ...dagNode, Conclusion: mutatedConclusion },
  ];

  const out = CheckSemanticKernelProofDAGInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DAGInd conclusion must exactly equal the computed all-node closure',
  );
});

test('DAGInd accepts only Record.intro local case evidence', () => {
  const graph = makeSemanticInductionDAG0('single.graph', [
    makeSemanticInductionDAGNode0('a'),
  ]);
  const invA = invariant0('a');
  const fakeConclusion = {
    kind: 'SemanticDAGIndJudgment0',
    version: 0,
    graphId: 'single.graph',
    nodeOrder: ['a'],
    sourceNodeIds: ['a'],
    sinkNodeIds: ['a'],
    caseProofIds: ['inv.a'],
    cases: [],
    allNodesClosed: true,
  };
  const out = CheckSemanticKernelProofDAGInd0(makeSemanticProofDAG0([
    eqProof0('inv.a', invA),
    makeSemanticProofNode0({
      id: 'dag.close',
      RuleName: 'DAGInd',
      Premises: ['inv.a'],
      Conclusion: fakeConclusion,
      Payload: { op: 'close', graph },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DAGInd case premise must be accepted Record.intro evidence',
  );
});

test('predecessor rules cannot consume DAGInd conclusions without explicit semantics', () => {
  const fixture = makeValidClosure0();
  const illegal = makeNode0({
    id: 'eq.after.dag',
    RuleName: 'Eq',
    Premises: ['dag.close'],
    Conclusion: fixture.invariants.invA,
    Payload: { op: 'symm' },
  });

  const out = CheckSemanticKernelProofDAGInd0(makeSemanticProofDAG0([
    ...fixture.nodes,
    illegal,
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofDAGInd0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record sub-DAG rejected under the predecessor semantic checker',
  );
});

test('DAGInd readiness removes DAGInd but leaves twelve rule families missing', () => {
  const out = CheckSemanticKernelReadinessDAGInd0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessDAGInd0.coverage');
  assert.equal(out.Witness.missingRules.includes('DAGInd'), false);
  assert.equal(out.Witness.missingRules.includes('LedgerInd'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 12);
});

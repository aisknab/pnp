import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofHall0,
  CheckSemanticKernelReadinessHall0,
  deriveSemanticHallJudgment0,
  makeSemanticHallEdge0,
  makeSemanticHallGraph0,
} from '../pcc-kernel-hall-semantic0.mjs';

function edge0(leftId, rightId) {
  return makeSemanticHallEdge0({ leftId, rightId });
}

function hallProof0(id, graph, conclusion = deriveSemanticHallJudgment0({ graph }), overrides = {}) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Hall',
    Conclusion: conclusion,
    Payload: { op: 'decide', graph },
    ...overrides,
  });
}

function makeCompleteGraph0() {
  return makeSemanticHallGraph0({
    graphId: 'matching.complete',
    leftVertexIds: ['l0', 'l1', 'l2'],
    rightVertexIds: ['r0', 'r1', 'r2'],
    edges: [
      edge0('l0', 'r0'),
      edge0('l0', 'r1'),
      edge0('l1', 'r1'),
      edge0('l2', 'r2'),
    ],
  });
}

function makeDeficientGraph0() {
  return makeSemanticHallGraph0({
    graphId: 'matching.deficient',
    leftVertexIds: ['l0', 'l1', 'l2'],
    rightVertexIds: ['r0', 'r1'],
    edges: [
      edge0('l0', 'r0'),
      edge0('l1', 'r0'),
      edge0('l2', 'r1'),
    ],
  });
}

test('Hall computes an exact left-complete injective matching', () => {
  const graph = makeCompleteGraph0();
  const conclusion = deriveSemanticHallJudgment0({ graph });
  const out = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.complete', graph, conclusion),
  ]));

  assert.equal(out.tag, 'accept');
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
  ]);
  assert.equal(out.NF.hallNodeCount, 1);
  assert.equal(out.NF.missingRequiredRules.includes('Hall'), false);
  assert.equal(conclusion.outcome, 'complete-matching');
  assert.deepEqual(conclusion.matching.map(({ leftId, rightId }) => ({ leftId, rightId })), [
    { leftId: 'l0', rightId: 'r0' },
    { leftId: 'l1', rightId: 'r1' },
    { leftId: 'l2', rightId: 'r2' },
  ]);
  assert.equal(conclusion.matchingSize, 3);
  assert.deepEqual(conclusion.unmatchedLeftVertexIds, []);
  assert.equal(conclusion.leftComplete, true);
  assert.equal(conclusion.hallDeficiencyVerified, false);
});

test('Hall computes an exact deficient set and exact neighbourhood', () => {
  const graph = makeDeficientGraph0();
  const conclusion = deriveSemanticHallJudgment0({ graph });
  const out = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.deficient', graph, conclusion),
  ]));

  assert.equal(out.tag, 'accept');
  assert.equal(conclusion.outcome, 'hall-deficient');
  assert.equal(conclusion.matchingSize, 2);
  assert.deepEqual(conclusion.unmatchedLeftVertexIds, ['l1']);
  assert.deepEqual(conclusion.deficientLeftVertexIds, ['l0', 'l1']);
  assert.deepEqual(conclusion.neighbourhoodRightVertexIds, ['r0']);
  assert.equal(conclusion.deficiency, 1);
  assert.equal(conclusion.leftComplete, false);
  assert.equal(conclusion.hallDeficiencyVerified, true);
});

test('Hall accepts an isolated left vertex as an exact empty-neighbourhood deficiency', () => {
  const graph = makeSemanticHallGraph0({
    graphId: 'matching.isolated',
    leftVertexIds: ['l0'],
    rightVertexIds: [],
    edges: [],
  });
  const conclusion = deriveSemanticHallJudgment0({ graph });
  const out = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.isolated', graph, conclusion),
  ]));

  assert.equal(out.tag, 'accept');
  assert.equal(conclusion.outcome, 'hall-deficient');
  assert.deepEqual(conclusion.deficientLeftVertexIds, ['l0']);
  assert.deepEqual(conclusion.neighbourhoodRightVertexIds, []);
  assert.equal(conclusion.deficiency, 1);
});

test('Hall rejects noncanonical vertex order', () => {
  const graph = makeCompleteGraph0();
  const badGraph = {
    ...graph,
    leftVertexIds: ['l1', 'l0', 'l2'],
  };
  const out = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.order', graph, undefined, {
      Payload: { op: 'decide', graph: badGraph },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofHall0.shape');
  assert.equal(out.Witness.reason, 'Hall left vertex ids must be in canonical order');
});

test('Hall rejects duplicate graph edges', () => {
  const graph = makeCompleteGraph0();
  const badGraph = {
    ...graph,
    edges: [graph.edges[0], graph.edges[0], ...graph.edges.slice(1)],
  };
  const out = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.duplicate', graph, undefined, {
      Payload: { op: 'decide', graph: badGraph },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'Hall edges must be unique');
});

test('Hall rejects an edge whose endpoint is outside the declared graph', () => {
  const graph = makeCompleteGraph0();
  const badGraph = {
    ...graph,
    edges: [
      ...graph.edges,
      edge0('l2', 'r9'),
    ],
  };
  const out = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.endpoint', graph, undefined, {
      Payload: { op: 'decide', graph: badGraph },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'Hall edge rightId must name a declared right vertex');
});

test('Hall rejects caller matching or completion assertions in graph and payload', () => {
  const graph = makeCompleteGraph0();
  const assertedGraph = { ...graph, matchingComplete: true };
  const graphOut = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.graph.asserted', graph, undefined, {
      Payload: { op: 'decide', graph: assertedGraph },
    }),
  ]));
  assert.equal(graphOut.tag, 'reject');
  assert.equal(
    graphOut.Witness.reason,
    'Hall graph rejects undeclared matching, deficiency, completion, solver, search, or oracle assertions',
  );

  const conclusion = deriveSemanticHallJudgment0({ graph });
  const payloadOut = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.payload.asserted', graph, conclusion, {
      Payload: { op: 'decide', graph, matching: conclusion.matching },
    }),
  ]));
  assert.equal(payloadOut.tag, 'reject');
  assert.equal(
    payloadOut.Witness.reason,
    'Hall payload rejects caller-supplied matching, deficiency, completeness, or oracle fields',
  );
});

test('Hall rejects a mutated computed matching conclusion', () => {
  const graph = makeCompleteGraph0();
  const conclusion = deriveSemanticHallJudgment0({ graph });
  const badConclusion = {
    ...conclusion,
    matching: conclusion.matching.map((edge, index) => (
      index === 0 ? { ...edge, rightId: 'r1' } : edge
    )),
  };
  const out = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.mutated.matching', graph, badConclusion),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Hall conclusion must exactly equal the computed matching-or-deficiency decision',
  );
});

test('Hall rejects a mutated deficient-set neighbourhood conclusion', () => {
  const graph = makeDeficientGraph0();
  const conclusion = deriveSemanticHallJudgment0({ graph });
  const badConclusion = {
    ...conclusion,
    neighbourhoodRightVertexIds: ['r0', 'r1'],
  };
  const out = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.mutated.neighbourhood', graph, badConclusion),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Hall conclusion must exactly equal the computed matching-or-deficiency decision',
  );
});

test('Hall.decide rejects proof premises', () => {
  const graph = makeCompleteGraph0();
  const conclusion = deriveSemanticHallJudgment0({ graph });
  const x = makeSemanticConst0('x', 'Term');
  const eqNode = makeSemanticProofNode0({
    id: 'eq.x',
    RuleName: 'Eq',
    Conclusion: makeSemanticEqJudgment0(x, x),
    Payload: { op: 'refl' },
  });
  const hallNode = hallProof0('hall.with.premise', graph, conclusion, {
    Premises: ['eq.x'],
  });
  const out = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    eqNode,
    hallNode,
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'Hall.decide computes from the explicit graph and accepts no proof premises',
  );
});

test('predecessor rules cannot consume Hall conclusions without explicit semantics', () => {
  const graph = makeCompleteGraph0();
  const conclusion = deriveSemanticHallJudgment0({ graph });
  const x = makeSemanticConst0('x', 'Term');
  const out = CheckSemanticKernelProofHall0(makeSemanticProofDAG0([
    hallProof0('hall.complete', graph, conclusion),
    makeSemanticProofNode0({
      id: 'eq.after.hall',
      RuleName: 'Eq',
      Premises: ['hall.complete'],
      Conclusion: makeSemanticEqJudgment0(x, x),
      Payload: { op: 'symm' },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofHall0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust/DPInd sub-DAG rejected under the predecessor semantic checker',
  );
});

test('Hall readiness removes Hall but leaves six primitive families missing', () => {
  const out = CheckSemanticKernelReadinessHall0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessHall0.coverage');
  assert.equal(out.Witness.missingRules.includes('Hall'), false);
  assert.equal(out.Witness.missingRules.includes('RankInd'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 6);
});

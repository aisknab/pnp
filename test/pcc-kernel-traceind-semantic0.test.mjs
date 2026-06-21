import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticApp0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofTraceInd0,
  CheckSemanticKernelReadinessTraceInd0,
  deriveSemanticTraceIndJudgment0,
  makeSemanticTrace0,
  makeSemanticTraceIndCase0,
  makeSemanticTraceNANDNode0,
  makeSemanticTraceSourceNode0,
} from '../pcc-kernel-traceind-semantic0.mjs';

function eqProof0(id, judgment) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Conclusion: judgment,
    Payload: { op: 'refl' },
  });
}

function recordProof0(id, conclusion, proofByField) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Record',
    Premises: conclusion.fields.map((field) => proofByField[field.name]),
    Conclusion: conclusion,
    Payload: {
      op: 'intro',
      recordType: conclusion.recordType,
      fieldNames: conclusion.fields.map((field) => field.name),
    },
  });
}

function makeValidTraceFixture0() {
  const traceId = 'locked.trace';
  const x0 = makeSemanticVar0('x0', 'Bool');
  const x1 = makeSemanticVar0('x1', 'Bool');
  const s0 = makeSemanticTraceSourceNode0({
    index: 0,
    id: 's0',
    sourceCoordinate: 'x0',
    sourceTerm: x0,
  });
  const s1 = makeSemanticTraceSourceNode0({
    index: 1,
    id: 's1',
    sourceCoordinate: 'x1',
    sourceTerm: x1,
  });
  const g0 = makeSemanticTraceNANDNode0({
    index: 2,
    id: 'g0',
    leftId: 's0',
    rightId: 's1',
    leftTerm: s0.valueTerm,
    rightTerm: s1.valueTerm,
  });
  const g1 = makeSemanticTraceNANDNode0({
    index: 3,
    id: 'g1',
    leftId: 'g0',
    rightId: 's0',
    leftTerm: g0.valueTerm,
    rightTerm: s0.valueTerm,
  });
  const traceNodes = [s0, s1, g0, g1];
  const nodesById = new Map(traceNodes.map((node) => [node.id, node]));
  const trace = makeSemanticTrace0({
    traceId,
    nodes: traceNodes,
    outputNodeId: 'g1',
    outputCoordinate: 'yout',
  });

  const proofNodes = [];
  const equationProofIds = new Map();
  const invariantProofIds = new Map();
  for (const node of traceNodes) {
    const equationId = `equation.${node.id}`;
    const invariantId = `invariant.${node.id}`;
    proofNodes.push(eqProof0(equationId, node.equation));
    proofNodes.push(eqProof0(invariantId, node.invariant));
    equationProofIds.set(node.id, equationId);
    invariantProofIds.set(node.id, invariantId);
  }

  const caseRecords = [];
  const caseProofIds = [];
  for (const node of traceNodes) {
    const dependencyIds = [...new Set(node.inputIds)];
    const caseRecord = makeSemanticTraceIndCase0({
      traceId,
      nodeId: node.id,
      equation: node.equation,
      current: node.invariant,
      dependencyInvariants: dependencyIds.map((dependencyId) => ({
        nodeId: dependencyId,
        invariant: nodesById.get(dependencyId).invariant,
      })),
    });
    const proofByField = {
      current: invariantProofIds.get(node.id),
      equation: equationProofIds.get(node.id),
    };
    for (const dependencyId of dependencyIds) {
      proofByField[`dep.${dependencyId}`] = invariantProofIds.get(dependencyId);
    }
    const caseId = `case.${node.id}`;
    proofNodes.push(recordProof0(caseId, caseRecord, proofByField));
    caseRecords.push(caseRecord);
    caseProofIds.push(caseId);
  }

  const conclusion = deriveSemanticTraceIndJudgment0({
    trace,
    caseRecords,
    caseProofIds,
  });
  proofNodes.push(makeSemanticProofNode0({
    id: 'trace.close',
    RuleName: 'TraceInd',
    Premises: caseProofIds,
    Conclusion: conclusion,
    Payload: { op: 'close', trace },
  }));

  return {
    traceId,
    x0,
    x1,
    traceNodes,
    nodesById,
    trace,
    caseRecords,
    caseProofIds,
    conclusion,
    proofNodes,
    equationProofIds,
    invariantProofIds,
  };
}

test('TraceInd closes exact source and NAND equations in topological order', () => {
  const fixture = makeValidTraceFixture0();
  const out = CheckSemanticKernelProofTraceInd0(
    makeSemanticProofDAG0(fixture.proofNodes),
  );

  assert.equal(out.tag, 'accept');
  assert.deepEqual(out.NF.supportedRules, [
    'Eq', 'Subst', 'Record', 'DAGInd', 'LedgerInd', 'OblTopoInd', 'TraceInd',
  ]);
  assert.equal(out.NF.traceIndNodeCount, 1);
  assert.equal(out.NF.missingRequiredRules.includes('TraceInd'), false);
  assert.deepEqual(fixture.conclusion.nodeOrder, ['s0', 's1', 'g0', 'g1']);
  assert.deepEqual(fixture.conclusion.sourceNodeIds, ['s0', 's1']);
  assert.deepEqual(fixture.conclusion.nandNodeIds, ['g0', 'g1']);
  assert.equal(fixture.conclusion.outputNodeId, 'g1');
  assert.equal(fixture.conclusion.outputCoordinate, 'yout');
  assert.deepEqual(
    fixture.conclusion.outputTerm,
    fixture.nodesById.get('g1').valueTerm,
  );
  assert.equal(fixture.conclusion.allSourceBindingsExact, true);
  assert.equal(fixture.conclusion.allNANDEquationsExact, true);
  assert.equal(fixture.conclusion.outputCoordinateBound, true);
});

test('TraceInd rejects a NAND value that is not the ordered NAND of earlier inputs', () => {
  const fixture = makeValidTraceFixture0();
  const badValue = makeSemanticApp0('nand', [fixture.x1, fixture.x0], 'Bool');
  const badG0 = {
    ...fixture.nodesById.get('g0'),
    valueTerm: badValue,
    equation: makeSemanticEqJudgment0(badValue, badValue),
    invariant: makeSemanticEqJudgment0(badValue, badValue),
  };
  const badTrace = {
    ...fixture.trace,
    nodes: fixture.trace.nodes.map((node) => node.id === 'g0' ? badG0 : node),
  };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofTraceInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', trace: badTrace } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofTraceInd0.shape');
  assert.equal(
    out.Witness.reason,
    'TraceInd NAND value term must equal the NAND of earlier input values',
  );
});

test('TraceInd rejects a forward NAND input reference', () => {
  const fixture = makeValidTraceFixture0();
  const badG0 = { ...fixture.nodesById.get('g0'), inputIds: ['g1', 's0'] };
  const badTrace = {
    ...fixture.trace,
    nodes: fixture.trace.nodes.map((node) => node.id === 'g0' ? badG0 : node),
  };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofTraceInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', trace: badTrace } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TraceInd NAND input must reference an earlier trace node',
  );
});

test('TraceInd rejects a NAND case missing one input invariant', () => {
  const fixture = makeValidTraceFixture0();
  const g0 = fixture.nodesById.get('g0');
  const shortCase = makeSemanticTraceIndCase0({
    traceId: fixture.traceId,
    nodeId: 'g0',
    equation: g0.equation,
    current: g0.invariant,
    dependencyInvariants: [
      { nodeId: 's0', invariant: fixture.nodesById.get('s0').invariant },
    ],
  });
  const shortCaseNode = recordProof0('case.g0', shortCase, {
    current: fixture.invariantProofIds.get('g0'),
    equation: fixture.equationProofIds.get('g0'),
    'dep.s0': fixture.invariantProofIds.get('s0'),
  });
  const out = CheckSemanticKernelProofTraceInd0(makeSemanticProofDAG0(
    fixture.proofNodes.map((node) => node.id === 'case.g0' ? shortCaseNode : node),
  ));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TraceInd case fields must contain the exact equation, current invariant, and input invariants',
  );
});

test('TraceInd rejects a substituted earlier input invariant', () => {
  const fixture = makeValidTraceFixture0();
  const g0 = fixture.nodesById.get('g0');
  const badCase = makeSemanticTraceIndCase0({
    traceId: fixture.traceId,
    nodeId: 'g0',
    equation: g0.equation,
    current: g0.invariant,
    dependencyInvariants: [
      { nodeId: 's0', invariant: fixture.nodesById.get('g1').invariant },
      { nodeId: 's1', invariant: fixture.nodesById.get('s1').invariant },
    ],
  });
  const badCaseNode = recordProof0('case.g0', badCase, {
    current: fixture.invariantProofIds.get('g0'),
    equation: fixture.equationProofIds.get('g0'),
    'dep.s0': fixture.invariantProofIds.get('g1'),
    'dep.s1': fixture.invariantProofIds.get('s1'),
  });
  const out = CheckSemanticKernelProofTraceInd0(makeSemanticProofDAG0(
    fixture.proofNodes.map((node) => node.id === 'case.g0' ? badCaseNode : node),
  ));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TraceInd input invariant must exactly match the earlier evaluated trace-node invariant',
  );
});

test('TraceInd rejects local cases supplied out of trace-node order', () => {
  const fixture = makeValidTraceFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofTraceInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Premises: ['case.s1', 'case.s0', 'case.g0', 'case.g1'],
    },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TraceInd case recordType must bind the trace and node id',
  );
});

test('TraceInd rejects an output term not equal to the declared output node', () => {
  const fixture = makeValidTraceFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const badTrace = { ...fixture.trace, outputTerm: fixture.x0 };
  const out = CheckSemanticKernelProofTraceInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', trace: badTrace } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TraceInd output term must exactly equal the declared output-node value',
  );
});

test('TraceInd rejects a mutated terminal output-coordinate conclusion', () => {
  const fixture = makeValidTraceFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofTraceInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Conclusion: { ...fixture.conclusion, outputCoordinate: 'wrongOutput' },
    },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TraceInd conclusion must exactly equal the computed terminal trace closure',
  );
});

test('TraceInd accepts only Record.intro local case evidence', () => {
  const fixture = makeValidTraceFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofTraceInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Premises: [
        fixture.invariantProofIds.get('s0'),
        'case.s1',
        'case.g0',
        'case.g1',
      ],
    },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'TraceInd case premise must be accepted Record.intro evidence',
  );
});

test('predecessor rules cannot consume TraceInd conclusions without explicit semantics', () => {
  const fixture = makeValidTraceFixture0();
  const illegal = makeSemanticProofNode0({
    id: 'eq.after.trace',
    RuleName: 'Eq',
    Premises: ['trace.close'],
    Conclusion: fixture.nodesById.get('s0').invariant,
    Payload: { op: 'symm' },
  });

  const out = CheckSemanticKernelProofTraceInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes,
    illegal,
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofTraceInd0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd sub-DAG rejected under the predecessor semantic checker',
  );
});

test('TraceInd readiness removes TraceInd but leaves nine rule families missing', () => {
  const out = CheckSemanticKernelReadinessTraceInd0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessTraceInd0.coverage');
  assert.equal(out.Witness.missingRules.includes('TraceInd'), false);
  assert.equal(out.Witness.missingRules.includes('FiniteExhaust'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 9);
});

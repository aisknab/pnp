import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticApp0,
  makeSemanticConst0,
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
} from '../pcc-kernel-semantic0.mjs';

import {
  CheckSemanticKernelProofDPInd0,
  CheckSemanticKernelReadinessDPInd0,
  deriveSemanticDPIndJudgment0,
  makeSemanticDPBaseState0,
  makeSemanticDPIndCase0,
  makeSemanticDPProgram0,
  makeSemanticDPStepState0,
} from '../pcc-kernel-dpind-semantic0.mjs';

function eqProof0(id, conclusion) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Eq',
    Conclusion: conclusion,
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

function makeValidDPFixture0() {
  const programId = 'budget.dp';
  const zero = makeSemanticConst0('zero', 'Cost');
  const one = makeSemanticConst0('one', 'Cost');

  const b0 = makeSemanticDPBaseState0({
    index: 0,
    id: 'b0',
    baseTerm: zero,
  });
  const b1 = makeSemanticDPBaseState0({
    index: 1,
    id: 'b1',
    baseTerm: one,
  });
  const s0 = makeSemanticDPStepState0({
    index: 2,
    id: 's0',
    predecessorIds: ['b0', 'b1'],
    predecessorValues: [b0.value, b1.value],
    operator: 'combine',
    valueSort: 'Cost',
  });
  const s1 = makeSemanticDPStepState0({
    index: 3,
    id: 's1',
    predecessorIds: ['s0'],
    predecessorValues: [s0.value],
    operator: 'extend',
    valueSort: 'Cost',
  });
  const states = [b0, b1, s0, s1];
  const stateById = new Map(states.map((state) => [state.id, state]));
  const program = makeSemanticDPProgram0({
    programId,
    valueSort: 'Cost',
    states,
    terminalStateId: 's1',
    terminalCoordinate: 'budget.output',
  });

  const proofNodes = [];
  const equationProofIds = new Map();
  const valueProofIds = new Map();
  for (const state of states) {
    const equationId = `equation.${state.id}`;
    const valueId = `value.${state.id}`;
    proofNodes.push(eqProof0(equationId, state.equation));
    proofNodes.push(eqProof0(
      valueId,
      makeSemanticEqJudgment0(state.value, state.value),
    ));
    equationProofIds.set(state.id, equationId);
    valueProofIds.set(state.id, valueId);
  }

  const caseRecords = [];
  const caseProofIds = [];
  for (const state of states) {
    const caseRecord = makeSemanticDPIndCase0({
      programId,
      stateId: state.id,
      equation: state.equation,
      value: state.value,
      dependencyValues: state.predecessorIds.map((predecessorId) => ({
        stateId: predecessorId,
        value: stateById.get(predecessorId).value,
      })),
    });
    const proofByField = {
      equation: equationProofIds.get(state.id),
      value: valueProofIds.get(state.id),
    };
    for (const predecessorId of state.predecessorIds) {
      proofByField[`dep.${predecessorId}`] = valueProofIds.get(predecessorId);
    }
    const caseId = `case.${state.id}`;
    proofNodes.push(recordProof0(caseId, caseRecord, proofByField));
    caseRecords.push(caseRecord);
    caseProofIds.push(caseId);
  }

  const conclusion = deriveSemanticDPIndJudgment0({
    program,
    caseRecords,
    caseProofIds,
  });
  proofNodes.push(makeSemanticProofNode0({
    id: 'dp.close',
    RuleName: 'DPInd',
    Premises: caseProofIds,
    Conclusion: conclusion,
    Payload: { op: 'close', program },
  }));

  return {
    programId,
    zero,
    one,
    states,
    stateById,
    program,
    proofNodes,
    equationProofIds,
    valueProofIds,
    caseRecords,
    caseProofIds,
    conclusion,
  };
}

test('DPInd closes exact base and recurrence states in well-founded order', () => {
  const fixture = makeValidDPFixture0();
  const out = CheckSemanticKernelProofDPInd0(
    makeSemanticProofDAG0(fixture.proofNodes),
  );

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
  ]);
  assert.equal(out.NF.dpIndNodeCount, 1);
  assert.equal(out.NF.missingRequiredRules.includes('DPInd'), false);
  assert.deepEqual(fixture.conclusion.stateOrder, ['b0', 'b1', 's0', 's1']);
  assert.deepEqual(fixture.conclusion.baseStateIds, ['b0', 'b1']);
  assert.deepEqual(fixture.conclusion.stepStateIds, ['s0', 's1']);
  assert.equal(fixture.conclusion.terminalStateId, 's1');
  assert.equal(fixture.conclusion.terminalCoordinate, 'budget.output');
  assert.deepEqual(
    fixture.conclusion.terminalValue,
    fixture.stateById.get('s1').value,
  );
  assert.equal(fixture.conclusion.evaluationOrderWellFounded, true);
  assert.equal(fixture.conclusion.predecessorCoverageComplete, true);
  assert.equal(fixture.conclusion.allStatesContributeToTerminal, true);
  assert.equal(fixture.conclusion.hiddenOptimizationAbsent, true);
});

test('DPInd rejects a recurrence predecessor that is not an earlier state', () => {
  const fixture = makeValidDPFixture0();
  const s0 = fixture.stateById.get('s0');
  const s1 = fixture.stateById.get('s1');
  const badS0 = {
    ...s0,
    predecessorIds: ['s1'],
    recurrenceTerm: makeSemanticApp0('combine', [s1.value], 'Cost'),
    equation: makeSemanticEqJudgment0(
      s0.value,
      makeSemanticApp0('combine', [s1.value], 'Cost'),
    ),
  };
  const badProgram = {
    ...fixture.program,
    states: fixture.program.states.map((state) => state.id === 's0' ? badS0 : state),
  };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofDPInd0.shape');
  assert.equal(
    out.Witness.reason,
    'DPInd recurrence predecessor must reference an earlier state',
  );
});

test('DPInd rejects a base state placed after recurrence evaluation begins', () => {
  const fixture = makeValidDPFixture0();
  const s1 = fixture.stateById.get('s1');
  const badS1 = {
    ...s1,
    stateKind: 'base',
    predecessorIds: [],
    operator: null,
    baseTerm: s1.value,
    recurrenceTerm: null,
    equation: makeSemanticEqJudgment0(s1.value, s1.value),
  };
  const badProgram = {
    ...fixture.program,
    states: fixture.program.states.map((state) => state.id === 's1' ? badS1 : state),
  };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DPInd base states must form one canonical prefix before recurrence states',
  );
});

test('DPInd rejects a nonconsecutive evaluation index', () => {
  const fixture = makeValidDPFixture0();
  const badProgram = {
    ...fixture.program,
    states: fixture.program.states.map((state) => (
      state.id === 's0' ? { ...state, index: 7 } : state
    )),
  };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DPInd state indices must be exact consecutive evaluation coordinates',
  );
});

test('DPInd rejects a recurrence term that omits a declared predecessor value', () => {
  const fixture = makeValidDPFixture0();
  const s0 = fixture.stateById.get('s0');
  const shortTerm = makeSemanticApp0('combine', [fixture.stateById.get('b0').value], 'Cost');
  const badS0 = {
    ...s0,
    recurrenceTerm: shortTerm,
    equation: makeSemanticEqJudgment0(s0.value, shortTerm),
  };
  const badProgram = {
    ...fixture.program,
    states: fixture.program.states.map((state) => state.id === 's0' ? badS0 : state),
  };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DPInd recurrence term must exactly apply the declared operator to all predecessor values',
  );
});

test('DPInd rejects an operator that hides minimization or an oracle', () => {
  const fixture = makeValidDPFixture0();
  const s0 = fixture.stateById.get('s0');
  const hiddenTerm = makeSemanticApp0(
    'argmin',
    [fixture.stateById.get('b0').value, fixture.stateById.get('b1').value],
    'Cost',
  );
  const badS0 = {
    ...s0,
    operator: 'argmin',
    recurrenceTerm: hiddenTerm,
    equation: makeSemanticEqJudgment0(s0.value, hiddenTerm),
  };
  const badProgram = {
    ...fixture.program,
    states: fixture.program.states.map((state) => state.id === 's0' ? badS0 : state),
  };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DPInd recurrence operator must be canonical and must not encode minimization, maximization, search, or an oracle',
  );
});

test('DPInd rejects a state graph containing a state that does not contribute to the terminal state', () => {
  const fixture = makeValidDPFixture0();
  const s0 = fixture.stateById.get('s0');
  const b0 = fixture.stateById.get('b0');
  const shortTerm = makeSemanticApp0('combine', [b0.value], 'Cost');
  const badS0 = {
    ...s0,
    predecessorIds: ['b0'],
    recurrenceTerm: shortTerm,
    value: shortTerm,
    equation: makeSemanticEqJudgment0(shortTerm, shortTerm),
  };
  const s1 = fixture.stateById.get('s1');
  const s1Term = makeSemanticApp0('extend', [shortTerm], 'Cost');
  const badS1 = {
    ...s1,
    recurrenceTerm: s1Term,
    value: s1Term,
    equation: makeSemanticEqJudgment0(s1Term, s1Term),
  };
  const badProgram = {
    ...fixture.program,
    states: fixture.program.states.map((state) => {
      if (state.id === 's0') return badS0;
      if (state.id === 's1') return badS1;
      return state;
    }),
  };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DPInd every declared state must contribute to the terminal state',
  );
  assert.deepEqual(out.Witness.deadStateIds, ['b1']);
});

test('DPInd rejects caller-supplied optimum or completion assertions', () => {
  const fixture = makeValidDPFixture0();
  const badProgram = { ...fixture.program, optimumVerified: true };
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', program: badProgram } },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofDPInd0.shape');
  assert.equal(
    out.Witness.reason,
    'DPInd program rejects undeclared completeness, optimum, minimizer, or oracle assertions',
  );
});

test('DPInd rejects a recurrence case missing one predecessor value', () => {
  const fixture = makeValidDPFixture0();
  const s0 = fixture.stateById.get('s0');
  const shortCase = makeSemanticDPIndCase0({
    programId: fixture.programId,
    stateId: 's0',
    equation: s0.equation,
    value: s0.value,
    dependencyValues: [{
      stateId: 'b0',
      value: fixture.stateById.get('b0').value,
    }],
  });
  const shortCaseNode = recordProof0('case.s0', shortCase, {
    equation: fixture.equationProofIds.get('s0'),
    value: fixture.valueProofIds.get('s0'),
    'dep.b0': fixture.valueProofIds.get('b0'),
  });
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0(
    fixture.proofNodes.map((node) => node.id === 'case.s0' ? shortCaseNode : node),
  ));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DPInd case fields must contain the exact equation, value, and predecessor values',
  );
});

test('DPInd rejects a substituted predecessor value in a local recurrence case', () => {
  const fixture = makeValidDPFixture0();
  const s0 = fixture.stateById.get('s0');
  const badCase = makeSemanticDPIndCase0({
    programId: fixture.programId,
    stateId: 's0',
    equation: s0.equation,
    value: s0.value,
    dependencyValues: [
      { stateId: 'b0', value: fixture.stateById.get('b1').value },
      { stateId: 'b1', value: fixture.stateById.get('b1').value },
    ],
  });
  const badCaseNode = recordProof0('case.s0', badCase, {
    equation: fixture.equationProofIds.get('s0'),
    value: fixture.valueProofIds.get('s0'),
    'dep.b0': fixture.equationProofIds.get('b1'),
    'dep.b1': fixture.valueProofIds.get('b1'),
  });
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0(
    fixture.proofNodes.map((node) => node.id === 'case.s0' ? badCaseNode : node),
  ));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DPInd predecessor value must exactly match the earlier evaluated state value',
  );
});

test('DPInd rejects local cases supplied out of state evaluation order', () => {
  const fixture = makeValidDPFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Premises: ['case.b1', 'case.b0', 'case.s0', 'case.s1'],
    },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DPInd case recordType must bind the program and state id',
  );
});

test('DPInd rejects a mutated terminal dynamic-programming conclusion', () => {
  const fixture = makeValidDPFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Conclusion: {
        ...fixture.conclusion,
        terminalCoordinate: 'wrong.output',
      },
    },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DPInd conclusion must exactly equal the computed terminal dynamic-programming closure',
  );
});

test('DPInd accepts only Record.intro local case evidence', () => {
  const fixture = makeValidDPFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Premises: [
        fixture.valueProofIds.get('b0'),
        'case.b1',
        'case.s0',
        'case.s1',
      ],
    },
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'DPInd case premise must be accepted Record.intro evidence',
  );
});

test('predecessor rules cannot consume DPInd conclusions without explicit semantics', () => {
  const fixture = makeValidDPFixture0();
  const illegal = makeSemanticProofNode0({
    id: 'eq.after.dp',
    RuleName: 'Eq',
    Premises: ['dp.close'],
    Conclusion: makeSemanticEqJudgment0(fixture.zero, fixture.zero),
    Payload: { op: 'symm' },
  });

  const out = CheckSemanticKernelProofDPInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes,
    illegal,
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofDPInd0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd/OblTopoInd/TraceInd/FiniteExhaust sub-DAG rejected under the predecessor semantic checker',
  );
});

test('DPInd readiness removes DPInd but leaves seven rule families missing', () => {
  const out = CheckSemanticKernelReadinessDPInd0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessDPInd0.coverage');
  assert.equal(out.Witness.missingRules.includes('DPInd'), false);
  assert.equal(out.Witness.missingRules.includes('Hall'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 7);
});

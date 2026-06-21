import assert from 'node:assert/strict';
import { test } from 'node:test';

import {
  makeSemanticEqJudgment0,
  makeSemanticProofDAG0,
  makeSemanticProofNode0,
  makeSemanticVar0,
} from '../pcc-kernel-semantic0.mjs';

import {
  makeSemanticRecordJudgment0,
} from '../pcc-kernel-record-semantic0.mjs';

import {
  CheckSemanticKernelProofOblTopoInd0,
  CheckSemanticKernelReadinessOblTopoInd0,
  deriveSemanticOblTopoIndJudgment0,
  makeSemanticObligation0,
  makeSemanticObligationCreationEvidence0,
  makeSemanticObligationDischargeEvidence0,
  makeSemanticObligationPlan0,
  makeSemanticOblTopoIndCase0,
} from '../pcc-kernel-obltopoind-semantic0.mjs';

function judgment0(name) {
  const term = makeSemanticVar0(name, 'ObligationAtom');
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

function recordProof0(id, conclusion, premises) {
  return makeSemanticProofNode0({
    id,
    RuleName: 'Record',
    Premises: premises,
    Conclusion: conclusion,
    Payload: {
      op: 'intro',
      recordType: conclusion.recordType,
      fieldNames: conclusion.fields.map((field) => field.name),
    },
  });
}

function makeObligationParts0(planId, obligationId, prefix, {
  mode = 'Full',
  dischargeRule = 'R6',
} = {}) {
  const source = judgment0(`${prefix}.source`);
  const target = judgment0(`${prefix}.target`);
  const frontier = judgment0(`${prefix}.frontier`);
  const projection = judgment0(`${prefix}.projection`);
  const result = judgment0(`${prefix}.result`);
  const fullWitness = mode === 'Full'
    ? judgment0(`${prefix}.fullWitness`)
    : null;
  const closed = judgment0(`${prefix}.closed`);

  const creation = makeSemanticObligationCreationEvidence0({
    planId,
    obligationId,
    mode,
    source,
    target,
    frontier,
    projection,
  });
  const discharge = makeSemanticObligationDischargeEvidence0({
    planId,
    obligationId,
    mode,
    rule: dischargeRule,
    result,
    fullWitness,
  });

  const nodes = [
    eqProof0(`${prefix}.source`, source),
    eqProof0(`${prefix}.target`, target),
    eqProof0(`${prefix}.frontier`, frontier),
    eqProof0(`${prefix}.projection`, projection),
    eqProof0(`${prefix}.result`, result),
    eqProof0(`${prefix}.closed`, closed),
  ];
  if (mode === 'Full') {
    nodes.push(eqProof0(`${prefix}.fullWitness`, fullWitness));
  }

  nodes.push(recordProof0(
    `${prefix}.creation`,
    creation,
    [
      `${prefix}.frontier`,
      `${prefix}.projection`,
      `${prefix}.source`,
      `${prefix}.target`,
    ],
  ));
  nodes.push(recordProof0(
    `${prefix}.discharge`,
    discharge,
    mode === 'Full'
      ? [`${prefix}.fullWitness`, `${prefix}.result`]
      : [`${prefix}.result`],
  ));

  return {
    mode,
    dischargeRule,
    source,
    target,
    frontier,
    projection,
    result,
    fullWitness,
    closed,
    creation,
    discharge,
    nodes,
    creationProofId: `${prefix}.creation`,
    dischargeProofId: `${prefix}.discharge`,
    closedProofId: `${prefix}.closed`,
  };
}

function makeValidFixture0() {
  const planId = 'obligation.plan';
  const o0 = makeObligationParts0(planId, 'o0', 'o0');
  const o1 = makeObligationParts0(planId, 'o1', 'o1', {
    dischargeRule: 'R7',
  });
  const o2 = makeObligationParts0(planId, 'o2', 'o2', {
    dischargeRule: 'R8',
  });

  const obligations = [
    makeSemanticObligation0({
      id: 'o0',
      mode: 'Full',
      dependencies: [],
      createIndex: 0,
      dischargeIndex: 2,
      dischargeRule: 'R6',
      creationEvidence: o0.creation,
      dischargeEvidence: o0.discharge,
    }),
    makeSemanticObligation0({
      id: 'o1',
      mode: 'Full',
      dependencies: ['o0'],
      createIndex: 1,
      dischargeIndex: 4,
      dischargeRule: 'R7',
      creationEvidence: o1.creation,
      dischargeEvidence: o1.discharge,
    }),
    makeSemanticObligation0({
      id: 'o2',
      mode: 'Full',
      dependencies: ['o1'],
      createIndex: 3,
      dischargeIndex: 5,
      dischargeRule: 'R8',
      creationEvidence: o2.creation,
      dischargeEvidence: o2.discharge,
    }),
  ];
  const plan = makeSemanticObligationPlan0(planId, obligations);

  const case0 = makeSemanticOblTopoIndCase0({
    planId,
    obligationId: 'o0',
    creation: o0.creation,
    discharge: o0.discharge,
    closed: o0.closed,
  });
  const case1 = makeSemanticOblTopoIndCase0({
    planId,
    obligationId: 'o1',
    creation: o1.creation,
    discharge: o1.discharge,
    closed: o1.closed,
    dependencyInvariants: [{ obligationId: 'o0', invariant: o0.closed }],
  });
  const case2 = makeSemanticOblTopoIndCase0({
    planId,
    obligationId: 'o2',
    creation: o2.creation,
    discharge: o2.discharge,
    closed: o2.closed,
    dependencyInvariants: [{ obligationId: 'o1', invariant: o1.closed }],
  });
  const caseProofIds = ['case.o0', 'case.o1', 'case.o2'];
  const conclusion = deriveSemanticOblTopoIndJudgment0({
    plan,
    caseRecords: [case0, case1, case2],
    caseProofIds,
  });

  const proofNodes = [
    ...o0.nodes,
    ...o1.nodes,
    ...o2.nodes,
    recordProof0('case.o0', case0, [
      o0.closedProofId,
      o0.creationProofId,
      o0.dischargeProofId,
    ]),
    recordProof0('case.o1', case1, [
      o1.closedProofId,
      o1.creationProofId,
      o0.closedProofId,
      o1.dischargeProofId,
    ]),
    recordProof0('case.o2', case2, [
      o2.closedProofId,
      o2.creationProofId,
      o1.closedProofId,
      o2.dischargeProofId,
    ]),
    makeSemanticProofNode0({
      id: 'obligations.close',
      RuleName: 'OblTopoInd',
      Premises: caseProofIds,
      Conclusion: conclusion,
      Payload: { op: 'close', plan },
    }),
  ];

  return {
    planId,
    plan,
    obligations,
    conclusion,
    cases: { case0, case1, case2 },
    parts: { o0, o1, o2 },
    caseProofIds,
    proofNodes,
  };
}

test('OblTopoInd closes exact R5 creation and R6/R7/R8 discharge lifecycles', () => {
  const fixture = makeValidFixture0();
  const out = CheckSemanticKernelProofOblTopoInd0(
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
  ]);
  assert.equal(out.NF.oblTopoIndNodeCount, 1);
  assert.equal(out.NF.missingRequiredRules.includes('OblTopoInd'), false);
  assert.deepEqual(fixture.conclusion.obligationOrder, ['o0', 'o1', 'o2']);
  assert.deepEqual(fixture.conclusion.dischargeOrder, ['o0', 'o1', 'o2']);
  assert.deepEqual(fixture.conclusion.sourceObligationIds, ['o0']);
  assert.deepEqual(fixture.conclusion.terminalObligationIds, ['o2']);
  assert.deepEqual(fixture.conclusion.openObligationIds, []);
  assert.equal(fixture.conclusion.fullModeDischargesVerified, true);
  assert.equal(fixture.conclusion.noOpenObligations, true);
  assert.deepEqual(
    fixture.conclusion.eventOrder.map((event) => `${event.index}:${event.action}:${event.obligationId}`),
    [
      '0:create:o0',
      '1:create:o1',
      '2:discharge:o0',
      '3:create:o2',
      '4:discharge:o1',
      '5:discharge:o2',
    ],
  );
});

test('OblTopoInd rejects a substituted dependency invariant', () => {
  const fixture = makeValidFixture0();
  const badCase = makeSemanticOblTopoIndCase0({
    planId: fixture.planId,
    obligationId: 'o1',
    creation: fixture.parts.o1.creation,
    discharge: fixture.parts.o1.discharge,
    closed: fixture.parts.o1.closed,
    dependencyInvariants: [
      { obligationId: 'o0', invariant: fixture.parts.o2.closed },
    ],
  });
  const badCaseNode = recordProof0('case.o1', badCase, [
    fixture.parts.o1.closedProofId,
    fixture.parts.o1.creationProofId,
    fixture.parts.o2.closedProofId,
    fixture.parts.o1.dischargeProofId,
  ]);
  const nodes = fixture.proofNodes.map(
    (node) => node.id === 'case.o1' ? badCaseNode : node,
  );

  const out = CheckSemanticKernelProofOblTopoInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd dependency invariant must exactly match the earlier discharged obligation invariant',
  );
});

test('OblTopoInd rejects a dependent case that omits dependency evidence', () => {
  const fixture = makeValidFixture0();
  const shortCase = makeSemanticOblTopoIndCase0({
    planId: fixture.planId,
    obligationId: 'o1',
    creation: fixture.parts.o1.creation,
    discharge: fixture.parts.o1.discharge,
    closed: fixture.parts.o1.closed,
  });
  const shortCaseNode = recordProof0('case.o1', shortCase, [
    fixture.parts.o1.closedProofId,
    fixture.parts.o1.creationProofId,
    fixture.parts.o1.dischargeProofId,
  ]);
  const nodes = fixture.proofNodes.map(
    (node) => node.id === 'case.o1' ? shortCaseNode : node,
  );

  const out = CheckSemanticKernelProofOblTopoInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd case fields must contain exact creation, discharge, closure, and dependency evidence',
  );
});

test('OblTopoInd rejects a nonconsecutive lifecycle event schedule', () => {
  const fixture = makeValidFixture0();
  const obligations = fixture.obligations.map((obligation) => (
    obligation.id === 'o2'
      ? { ...obligation, dischargeIndex: 4 }
      : obligation
  ));
  const plan = { ...fixture.plan, obligations };
  const closeNode = fixture.proofNodes.at(-1);
  const nodes = [
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', plan } },
  ];

  const out = CheckSemanticKernelProofOblTopoInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofOblTopoInd0.shape');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd creation and discharge events must form one exact consecutive schedule',
  );
});

test('OblTopoInd rejects R6 discharge of a Quot-mode obligation', () => {
  const fixture = makeValidFixture0();
  const obligations = fixture.obligations.map((obligation) => (
    obligation.id === 'o0'
      ? { ...obligation, mode: 'Quot' }
      : obligation
  ));
  const plan = { ...fixture.plan, obligations };
  const closeNode = fixture.proofNodes.at(-1);
  const nodes = [
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', plan } },
  ];

  const out = CheckSemanticKernelProofOblTopoInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Witness.reason, 'R6 may discharge only a Full-mode obligation');
});

test('OblTopoInd rejects Full-mode discharge evidence without fullWitness', () => {
  const fixture = makeValidFixture0();
  const malformedDischarge = makeSemanticRecordJudgment0(
    `ObligationDischarge0.${fixture.planId}.o0.R6.Full`,
    fixture.parts.o0.discharge.fields.filter((field) => field.name === 'result'),
  );
  const obligations = fixture.obligations.map((obligation) => (
    obligation.id === 'o0'
      ? { ...obligation, dischargeEvidence: malformedDischarge }
      : obligation
  ));
  const plan = { ...fixture.plan, obligations };
  const closeNode = fixture.proofNodes.at(-1);
  const nodes = [
    ...fixture.proofNodes.slice(0, -1),
    { ...closeNode, Payload: { op: 'close', plan } },
  ];

  const out = CheckSemanticKernelProofOblTopoInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd discharge evidence must contain the exact canonical evidence fields',
  );
});

test('OblTopoInd rejects local cases supplied out of discharge order', () => {
  const fixture = makeValidFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const nodes = [
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Premises: ['case.o1', 'case.o0', 'case.o2'],
    },
  ];

  const out = CheckSemanticKernelProofOblTopoInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd case recordType must bind the plan and obligation id',
  );
});

test('OblTopoInd rejects a mutated terminal no-open-obligations conclusion', () => {
  const fixture = makeValidFixture0();
  const closeNode = fixture.proofNodes.at(-1);
  const nodes = [
    ...fixture.proofNodes.slice(0, -1),
    {
      ...closeNode,
      Conclusion: {
        ...fixture.conclusion,
        openObligationIds: ['o2'],
        noOpenObligations: false,
      },
    },
  ];

  const out = CheckSemanticKernelProofOblTopoInd0(makeSemanticProofDAG0(nodes));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofOblTopoInd0.shape');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd conclusion noOpenObligations must be true',
  );
});

test('OblTopoInd accepts only Record.intro local case evidence', () => {
  const planId = 'single.plan';
  const parts = makeObligationParts0(planId, 'o0', 'single');
  const obligation = makeSemanticObligation0({
    id: 'o0',
    mode: 'Full',
    dependencies: [],
    createIndex: 0,
    dischargeIndex: 1,
    dischargeRule: 'R6',
    creationEvidence: parts.creation,
    dischargeEvidence: parts.discharge,
  });
  const plan = makeSemanticObligationPlan0(planId, [obligation]);
  const fakeConclusion = {
    kind: 'SemanticOblTopoIndJudgment0',
    version: 0,
    planId,
    obligationOrder: ['o0'],
    dischargeOrder: ['o0'],
    eventOrder: [],
    sourceObligationIds: ['o0'],
    terminalObligationIds: ['o0'],
    fullModeObligationIds: ['o0'],
    quotientModeObligationIds: [],
    caseProofIds: ['single.closed'],
    cases: [],
    dischargedObligationIds: ['o0'],
    openObligationIds: [],
    allDependenciesClosed: true,
    fullModeDischargesVerified: true,
    allObligationsDischarged: true,
    noOpenObligations: true,
  };

  const out = CheckSemanticKernelProofOblTopoInd0(makeSemanticProofDAG0([
    ...parts.nodes,
    makeSemanticProofNode0({
      id: 'obligations.close',
      RuleName: 'OblTopoInd',
      Premises: [parts.closedProofId],
      Conclusion: fakeConclusion,
      Payload: { op: 'close', plan },
    }),
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(
    out.Witness.reason,
    'OblTopoInd case premise must be accepted Record.intro evidence',
  );
});

test('predecessor rules cannot consume OblTopoInd conclusions without explicit semantics', () => {
  const fixture = makeValidFixture0();
  const illegal = makeSemanticProofNode0({
    id: 'eq.after.obligations',
    RuleName: 'Eq',
    Premises: ['obligations.close'],
    Conclusion: fixture.parts.o0.closed,
    Payload: { op: 'symm' },
  });

  const out = CheckSemanticKernelProofOblTopoInd0(makeSemanticProofDAG0([
    ...fixture.proofNodes,
    illegal,
  ]));

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelProofOblTopoInd0.baseProof');
  assert.equal(
    out.Witness.reason,
    'Eq/Subst/Record/DAGInd/LedgerInd sub-DAG rejected under the predecessor semantic checker',
  );
});

test('OblTopoInd readiness removes OblTopoInd but leaves ten rule families missing', () => {
  const out = CheckSemanticKernelReadinessOblTopoInd0();

  assert.equal(out.tag, 'reject');
  assert.equal(out.Coord, 'CheckSemanticKernelReadinessOblTopoInd0.coverage');
  assert.equal(out.Witness.missingRules.includes('OblTopoInd'), false);
  assert.equal(out.Witness.missingRules.includes('TraceInd'), true);
  assert.equal(out.Witness.missingRules.includes('FiniteRel'), true);
  assert.equal(out.Witness.missingRules.length, 10);
});
